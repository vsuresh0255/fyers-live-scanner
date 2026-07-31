/**
 * Fyers Live Scanner — Railway-hosted version
 * =============================================
 * Same purpose as the local version, adapted to run on Railway instead of your
 * own computer:
 *   - Uses whatever port Railway assigns (via process.env.PORT), not a fixed one
 *   - Daily login: instead of pasting the auth code into a terminal, you paste it
 *     into a simple webpage this app serves itself
 *   - Requires a secret token on the WebSocket connection, since this is now
 *     reachable from the internet, not just your own computer
 *
 * CONFIG: set these as Environment Variables in the Railway dashboard (not a
 * config.json file — Railway apps read config from environment variables):
 *   FYERS_APP_ID       - your Fyers App ID
 *   FYERS_SECRET_KEY    - your Fyers Secret Key
 *   FYERS_REDIRECT_URI  - must exactly match what's set on myapi.fyers.in
 *   RELAY_TOKEN         - make up any password-like string yourself; you'll enter
 *                         this same value in the browser tool's Live Scanner tab
 *
 * symbols.json must be uploaded alongside this file (same folder) — export it
 * from the browser tool's Bhavcopy panel.
 */

const fs = require('fs');
const path = require('path');
const http = require('http');
const url = require('url');
const WebSocket = require('ws');
const { fyersModel, fyersDataSocket } = require('fyers-api-v3');

const PORT = process.env.PORT || 3000;
const APP_ID = process.env.FYERS_APP_ID;
const SECRET_KEY = process.env.FYERS_SECRET_KEY;
const REDIRECT_URI = process.env.FYERS_REDIRECT_URI;
const RELAY_TOKEN = process.env.RELAY_TOKEN;

let currentAccessToken = null; // stored after daily login, needed for placing orders

if (!APP_ID || !SECRET_KEY || !REDIRECT_URI || !RELAY_TOKEN) {
  console.error('\nMissing required environment variables. Set FYERS_APP_ID, FYERS_SECRET_KEY, FYERS_REDIRECT_URI, and RELAY_TOKEN in the Railway dashboard (Variables tab).\n');
  process.exit(1);
}

const SYMBOLS_PATH = path.join(__dirname, 'symbols.json');
if (!fs.existsSync(SYMBOLS_PATH)) {
  console.error('\nMissing symbols.json. Export it from the browser tool and upload it into this same folder in GitHub.\n');
  process.exit(1);
}
const symbols = JSON.parse(fs.readFileSync(SYMBOLS_PATH, 'utf8'));
console.log(`Loaded ${symbols.length} symbols to track.`);

// ============ live state per symbol ============
const state = {};
symbols.forEach(s => { state[s] = { open: null, high: null, low: null, ltp: null, volume: null, prevClose: null }; });
let rawSampleCount = 0;
const MAX_RAW_SAMPLES = 8; // log the first several messages, not just one — the very first is
                            // usually just a connection acknowledgment, not real tick data
let fyersSocket = null;
let isLive = false;

function pick(obj, candidates) {
  for (const key of candidates) {
    if (obj[key] !== undefined && obj[key] !== null) return obj[key];
  }
  return null;
}

function updateStateFromTick(symbol, tick) {
  const s = state[symbol];
  if (!s) return;
  const open = pick(tick, ['open_price', 'o', 'open']);
  const high = pick(tick, ['high_price', 'h', 'high']);
  const low = pick(tick, ['low_price', 'l', 'low']);
  const ltp = pick(tick, ['ltp', 'last_traded_price', 'lp']);
  const volume = pick(tick, ['vol_traded_today', 'volume', 'v']);
  const prevClose = pick(tick, ['prev_close_price', 'previous_close_price', 'pc']);
  if (open !== null) s.open = open;
  if (high !== null) s.high = high;
  if (low !== null) s.low = low;
  if (ltp !== null) s.ltp = ltp;
  if (volume !== null) s.volume = volume;
  if (prevClose !== null) s.prevClose = prevClose;
}

const EPS = 0.01;

function computeScreeners() {
  const openEqLow = [], openEqHigh = [], gapNeutral = [];
  Object.keys(state).forEach(symbol => {
    const s = state[symbol];
    if (s.open === null || s.high === null || s.low === null) return;
    if (Math.abs(s.low - s.open) <= EPS) openEqLow.push({ symbol, open: s.open, low: s.low, ltp: s.ltp });
    if (Math.abs(s.high - s.open) <= EPS) openEqHigh.push({ symbol, open: s.open, high: s.high, ltp: s.ltp });
    if (s.prevClose !== null && Math.abs(s.open - s.prevClose) <= EPS) gapNeutral.push({ symbol, open: s.open, prevClose: s.prevClose, ltp: s.ltp });
  });
  const withVolume = Object.entries(state).filter(([, s]) => s.volume !== null).map(([symbol, s]) => ({ symbol, volume: s.volume, ltp: s.ltp }));
  withVolume.sort((a, b) => b.volume - a.volume);
  const topCount = Math.max(1, Math.ceil(withVolume.length * 0.05));
  const volumeShockers = withVolume.slice(0, topCount);
  return { openEqLow, openEqHigh, gapNeutral, volumeShockers, updatedAt: new Date().toISOString(), isLive };
}

// ============ Fyers connection (started after auth code submitted) ============
function startFyersConnection(accessToken) {
  if (fyersSocket) {
    console.log('A connection already exists — closing it before starting a fresh one.');
    try { fyersSocket.close(); } catch (e) { /* ignore */ }
    fyersSocket = null;
    isLive = false;
  }

  const fullToken = `${APP_ID}:${accessToken}`;
  fyersSocket = fyersDataSocket.getInstance(fullToken, __dirname, false);

  fyersSocket.on('connect', () => {
    console.log('Connected to Fyers live data feed. Subscribing to', symbols.length, 'symbols...');
    fyersSocket.subscribe(symbols);
    isLive = true;
  });

  fyersSocket.on('message', tick => {
    if (rawSampleCount < MAX_RAW_SAMPLES) {
      rawSampleCount++;
      console.log(`\n=== RAW SAMPLE ${rawSampleCount}/${MAX_RAW_SAMPLES} ===\n` + JSON.stringify(tick, null, 2) + '\n=======================\n');
    }
    const symbol = tick.symbol || tick.s;
    if (symbol && state[symbol]) {
      updateStateFromTick(symbol, tick);
      broadcastScreeners();
    }
  });

  fyersSocket.on('error', msg => console.error('Fyers WS error:', msg));
  fyersSocket.on('close', () => { console.log('Fyers WS connection closed.'); isLive = false; });

  fyersSocket.autoreconnect(6);
  fyersSocket.connect();
}

// ============ web server: auth page + WebSocket relay, sharing one port ============
const server = http.createServer(async (req, res) => {
  const parsed = url.parse(req.url, true);

  if (parsed.pathname === '/' && req.method === 'GET') {
    const fyers = new fyersModel({ path: __dirname, enableLogging: false });
    fyers.setAppId(APP_ID);
    fyers.setRedirectUrl(REDIRECT_URI);
    const loginUrl = fyers.generateAuthCode();

    res.writeHead(200, { 'Content-Type': 'text/html' });
    res.end(`
      <html><body style="font-family:sans-serif; max-width:600px; margin:40px auto;">
        <h2>Fyers Live Scanner — Daily Login</h2>
        <p>Status: <b>${isLive ? 'Connected and live' : 'Not connected'}</b></p>
        <ol>
          <li><a href="${loginUrl}" target="_blank">Click here to log in to Fyers</a></li>
          <li>After login, your browser will try to redirect and fail to load — that's expected.</li>
          <li>Copy the <code>auth_code</code> value from the URL bar.</li>
          <li>Paste it below and submit.</li>
        </ol>
        <form method="POST" action="/submit-auth-code">
          <input type="text" name="authCode" placeholder="Paste auth_code here" style="width:100%; padding:8px;">
          <button type="submit" style="padding:8px 16px; margin-top:10px;">Connect</button>
        </form>
      </body></html>
    `);
    return;
  }

  if (parsed.pathname === '/submit-auth-code' && req.method === 'POST') {
    let body = '';
    req.on('data', chunk => { body += chunk; });
    req.on('end', async () => {
      const params = new url.URLSearchParams(body);
      const authCode = params.get('authCode');

      const fyers = new fyersModel({ path: __dirname, enableLogging: false });
      fyers.setAppId(APP_ID);
      fyers.setRedirectUrl(REDIRECT_URI);

      try {
        const response = await fyers.generate_access_token({
          client_id: APP_ID, secret_key: SECRET_KEY, auth_code: authCode
        });
        if (response.s !== 'ok') {
          res.writeHead(400, { 'Content-Type': 'text/html' });
          res.end(`<p>Token generation failed: ${JSON.stringify(response)}. <a href="/">Try again</a></p>`);
          return;
        }
        startFyersConnection(response.access_token);
        currentAccessToken = response.access_token;
        res.writeHead(200, { 'Content-Type': 'text/html' });
        res.end('<p>Success! Connecting to live data feed... <a href="/">Check status</a></p>');
      } catch (err) {
        res.writeHead(500, { 'Content-Type': 'text/html' });
        res.end(`<p>Error: ${err.message}. <a href="/">Try again</a></p>`);
      }
    });
    return;
  }

  if (parsed.pathname === '/place-order' && req.method === 'POST') {
    if (parsed.query.token !== RELAY_TOKEN) {
      res.writeHead(401, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ error: 'Invalid token' }));
      return;
    }
    if (!currentAccessToken) {
      res.writeHead(400, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ error: 'Not logged in to Fyers yet — complete the daily login first' }));
      return;
    }

    let body = '';
    req.on('data', chunk => { body += chunk; });
    req.on('end', async () => {
      try {
        const order = JSON.parse(body);
        const { symbol, side, qty, orderType, limitPrice } = order;

        // basic validation — reject anything malformed before it reaches Fyers
        if (!symbol || !state[symbol]) throw new Error('Unknown or missing symbol');
        if (side !== 'BUY' && side !== 'SELL') throw new Error('side must be BUY or SELL');
        const qtyNum = parseInt(qty);
        if (!qtyNum || qtyNum <= 0) throw new Error('qty must be a positive number');
        if (orderType !== 'MARKET' && orderType !== 'LIMIT') throw new Error('orderType must be MARKET or LIMIT');
        if (orderType === 'LIMIT' && (!limitPrice || limitPrice <= 0)) throw new Error('limitPrice required for LIMIT orders');

        const fyers = new fyersModel({ path: __dirname, enableLogging: false });
        fyers.setAppId(APP_ID);
        fyers.token = `${APP_ID}:${currentAccessToken}`;

        const orderData = {
          symbol,
          qty: qtyNum,
          type: orderType === 'MARKET' ? 2 : 1,
          side: side === 'BUY' ? 1 : -1,
          productType: 'INTRADAY',
          limitPrice: orderType === 'LIMIT' ? parseFloat(limitPrice) : 0,
          stopPrice: 0,
          disclosedQty: 0,
          validity: 'DAY',
          offlineOrder: false
        };

        console.log('Placing order:', JSON.stringify(orderData));
        const response = await fyers.place_order(orderData);
        console.log('Order response:', JSON.stringify(response));

        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify(response));
      } catch (err) {
        res.writeHead(400, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ error: err.message }));
      }
    });
    return;
  }

  res.writeHead(404);
  res.end('Not found');
});

const wss = new WebSocket.Server({ server, path: '/live' });

wss.on('connection', (ws, req) => {
  const parsed = url.parse(req.url, true);
  if (parsed.query.token !== RELAY_TOKEN) {
    ws.close(4001, 'Invalid token');
    return;
  }
  console.log('Browser tool connected to relay.');
  ws.send(JSON.stringify(computeScreeners()));
});

function broadcastScreeners() {
  const payload = JSON.stringify(computeScreeners());
  wss.clients.forEach(client => {
    if (client.readyState === WebSocket.OPEN) client.send(payload);
  });
}

server.listen(PORT, () => {
  console.log(`Server listening on port ${PORT}. Visit your Railway URL to complete daily login.`);
});
