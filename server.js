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
let rawSamplesLoggedThisLifetime = false; // don't re-log raw samples every time it reconnects —
                                            // this SDK reconnects often, and repeating this every
                                            // time was drowning out other, more useful log lines
let lastTickReceivedAt = null; // tracks the last REAL price tick, separate from relay-connection status —
                                 // lets you tell "connected but Fyers feed has gone quiet" apart from
                                 // "genuinely fine, just between ticks"
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
  return { openEqLow, openEqHigh, gapNeutral, volumeShockers, updatedAt: new Date().toISOString(), isLive, lastTickReceivedAt };
}

// ============ minute-by-minute historical slot tracking ============
// Runs on the SERVER (not per-browser), so a browser connecting at 12:30 still sees
// what happened at 9:15, 9:20, etc. Each symbol is recorded only in the FIRST minute
// it qualifies for a given screener — later minutes where it's still qualifying don't
// repeat it, per your "make it unique" request.
//
// PERSISTENCE: written to disk so history survives a Railway redeploy, not just a
// simple in-memory restart. Requires a Railway Volume mounted at the path below —
// see the README for setup steps. Without a volume, this still works fine during
// normal operation (all day, no redeploys); it just won't survive a code update.
const PERSIST_DIR = process.env.RAILWAY_VOLUME_MOUNT_PATH || '/data';
const PERSIST_FILE = path.join(PERSIST_DIR, 'slot_history.json');

let slotHistory = { openlow: [], openhigh: [], gapneutral: [], orb5up: [], orb5down: [], orb15up: [], orb15down: [] };
let alreadySeen = { openlow: new Set(), openhigh: new Set(), gapneutral: new Set(), orb5up: new Set(), orb5down: new Set(), orb15up: new Set(), orb15down: new Set() };

function todayDateKey(){
  return new Date().toISOString().slice(0, 10);
}

function loadPersistedHistory(){
  try{
    if(!fs.existsSync(PERSIST_FILE)) {
      console.log('No persisted history file found — starting fresh (this is normal on first run, or if no volume is mounted).');
      return;
    }
    const saved = JSON.parse(fs.readFileSync(PERSIST_FILE, 'utf8'));
    if(saved.date !== todayDateKey()){
      console.log('Persisted history is from a previous day — starting fresh for today.');
      return;
    }
    slotHistory = saved.slotHistory;
    Object.keys(alreadySeen).forEach(key => {
      alreadySeen[key] = new Set((saved.alreadySeen && saved.alreadySeen[key]) || []);
      if(!slotHistory[key]) slotHistory[key] = []; // in case this key didn't exist in an older saved file
    });
    console.log('Restored slot history from disk — survived the restart/redeploy.');
  } catch(err){
    console.log('Could not load persisted history (this is fine if no volume is mounted yet):', err.message);
  }
}

function savePersistedHistory(){
  try{
    if(!fs.existsSync(PERSIST_DIR)) return; // no volume mounted — skip silently, still works in-memory
    const toSave = {
      date: todayDateKey(),
      slotHistory,
      alreadySeen: Object.fromEntries(Object.keys(alreadySeen).map(k => [k, [...alreadySeen[k]]]))
    };
    fs.writeFileSync(PERSIST_FILE, JSON.stringify(toSave));
  } catch(err){
    console.log('Could not save history to disk (this is fine if no volume is mounted):', err.message);
  }
}

loadPersistedHistory();

function timeLabel(){
  // Railway's server clock is very likely UTC, not IST — compute IST explicitly rather
  // than relying on the container's local timezone, which could show misleading labels
  // otherwise (e.g. a UTC-based label while you're looking at an IST market clock).
  const now = new Date();
  const istMillis = now.getTime() + (5.5 * 60 * 60 * 1000) + (now.getTimezoneOffset() * 60 * 1000);
  const ist = new Date(istMillis);
  return `${String(ist.getUTCHours()).padStart(2,'0')}:${String(ist.getUTCMinutes()).padStart(2,'0')}`;
}

function getISTDateKeyAndMinutes(){
  const now = new Date();
  const istMillis = now.getTime() + (5.5 * 60 * 60 * 1000) + (now.getTimezoneOffset() * 60 * 1000);
  const ist = new Date(istMillis);
  const dateKey = `${ist.getUTCFullYear()}-${String(ist.getUTCMonth()+1).padStart(2,'0')}-${String(ist.getUTCDate()).padStart(2,'0')}`;
  const minutes = ist.getUTCHours()*60 + ist.getUTCMinutes();
  return { dateKey, minutes };
}

// ============ Opening Range Breakout (ORB) tracking — 5-min and 15-min ============
// The opening range for a stock is simply its cumulative high/low from market open (9:15)
// through the lock time (9:20 for 5-min, 9:30 for 15-min) — since Fyers ticks already carry
// the cumulative high/low since open, we don't need a separate accumulator, just a snapshot
// of state[symbol].high/low taken at exactly the right moment.
const orb5Locked = {};   // symbol -> {high, low}
const orb15Locked = {};  // symbol -> {high, low}
let orb5LockedFlag = false;
let orb15LockedFlag = false;
let orbLockedDateKey = null; // resets orb5/orb15 fresh each new trading day

function checkAndLockOpeningRanges(){
  const { dateKey, minutes } = getISTDateKeyAndMinutes();

  if(orbLockedDateKey !== dateKey){
    // new trading day — clear yesterday's locked ranges and start fresh
    orbLockedDateKey = dateKey;
    orb5LockedFlag = false;
    orb15LockedFlag = false;
    Object.keys(orb5Locked).forEach(k => delete orb5Locked[k]);
    Object.keys(orb15Locked).forEach(k => delete orb15Locked[k]);
  }

  if(!orb5LockedFlag && minutes >= (9*60+20)){
    Object.keys(state).forEach(symbol => {
      const s = state[symbol];
      if(s.high !== null && s.low !== null) orb5Locked[symbol] = { high: s.high, low: s.low };
    });
    orb5LockedFlag = true;
    console.log(`5-min Opening Range locked for ${Object.keys(orb5Locked).length} symbols.`);
  }
  if(!orb15LockedFlag && minutes >= (9*60+30)){
    Object.keys(state).forEach(symbol => {
      const s = state[symbol];
      if(s.high !== null && s.low !== null) orb15Locked[symbol] = { high: s.high, low: s.low };
    });
    orb15LockedFlag = true;
    console.log(`15-min Opening Range locked for ${Object.keys(orb15Locked).length} symbols.`);
  }
}

function computeOrbBreakouts(minutes){
  const locked = minutes === 5 ? orb5Locked : orb15Locked;
  const up = [], down = [];
  Object.keys(locked).forEach(symbol => {
    const s = state[symbol];
    const range = locked[symbol];
    if(!s || s.ltp === null) return;
    if(s.ltp > range.high) up.push({ symbol, ltp: s.ltp, orbHigh: range.high, orbLow: range.low });
    else if(s.ltp < range.low) down.push({ symbol, ltp: s.ltp, orbHigh: range.high, orbLow: range.low });
  });
  return { up, down };
}

function recordMinuteSlot(){
  checkAndLockOpeningRanges();

  const snap = computeScreeners();
  const orb5 = computeOrbBreakouts(5);
  const orb15 = computeOrbBreakouts(15);
  const groups = {
    openlow: snap.openEqLow, openhigh: snap.openEqHigh, gapneutral: snap.gapNeutral,
    orb5up: orb5.up, orb5down: orb5.down, orb15up: orb15.up, orb15down: orb15.down
  };
  const label = timeLabel();

  Object.keys(groups).forEach(key => {
    const freshSymbols = groups[key]
      .map(r => r.symbol)
      .filter(sym => !alreadySeen[key].has(sym));
    freshSymbols.forEach(sym => alreadySeen[key].add(sym));
    // always record this minute, even with an empty list — so you can see time actually
    // progressing (9:15, 9:16, 9:17...) rather than the table looking "stuck" whenever
    // nothing new happens to qualify that particular minute
    slotHistory[key].push({ time: label, symbols: freshSymbols });
  });

  savePersistedHistory();
}

// check every 10 seconds whether a new clock-minute has started, and if so, record it —
// more reliable than a raw 60s interval, which can drift out of alignment with real clock minutes
let lastRecordedMinute = null;
setInterval(() => {
  try{
    const label = timeLabel();
    if (label !== lastRecordedMinute) {
      console.log(`Minute changed: ${lastRecordedMinute} -> ${label}, recording new slot.`);
      lastRecordedMinute = label;
      recordMinuteSlot();
      broadcastScreeners(); // push the newly recorded minute out immediately
      console.log(`Slot recorded successfully. openlow history now has ${slotHistory.openlow.length} entries.`);
    }
  } catch(err){
    console.log('ERROR in minute-recording interval:', err.message, err.stack);
  }
}, 10000);

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

  // Defensive fix for a real memory leak: Fyers' "getInstance" naming strongly suggests
  // this may return a shared/singleton object rather than a genuinely fresh one on every
  // call. Without this, every reconnect (which happens often — see the known SDK
  // reliability issue) would stack a new set of listeners on top of the old ones,
  // accumulating hundreds over a trading day and causing the OOM crashes we saw.
  if (typeof fyersSocket.removeAllListeners === 'function') {
    fyersSocket.removeAllListeners();
  }

  fyersSocket.on('connect', () => {
    console.log('Connected to Fyers live data feed. Subscribing to', symbols.length, 'symbols...');
    fyersSocket.subscribe(symbols);
    isLive = true;
  });

  fyersSocket.on('message', tick => {
    if (rawSampleCount < MAX_RAW_SAMPLES && !rawSamplesLoggedThisLifetime) {
      rawSampleCount++;
      console.log(`\n=== RAW SAMPLE ${rawSampleCount}/${MAX_RAW_SAMPLES} ===\n` + JSON.stringify(tick, null, 2) + '\n=======================\n');
      if(rawSampleCount >= MAX_RAW_SAMPLES) rawSamplesLoggedThisLifetime = true;
    }
    const symbol = tick.symbol || tick.s;
    if (symbol && state[symbol]) {
      updateStateFromTick(symbol, tick);
      lastTickReceivedAt = new Date().toISOString();
      scheduleBroadcast();
    }
  });

  fyersSocket.on('error', msg => console.error('Fyers WS error:', msg));
  fyersSocket.on('close', () => { console.log('Fyers WS connection closed.'); isLive = false; });

  fyersSocket.autoreconnect(6);
  fyersSocket.connect();
}

// ============ stall watchdog ============
// The known failure mode with this SDK: the connection can go silent — no error, no
// close event — it just stops delivering ticks. The SDK's own autoreconnect only
// fires on an actual error/close, so it never catches this. This checks independently:
// if we're within market hours and haven't seen a real tick in a while, force a fresh
// reconnect using the same stored access token, rather than waiting for an error that
// may never come.
function isMarketHoursIST(){
  const now = new Date();
  const istOffset = 5.5 * 60; // IST is UTC+5:30, in minutes
  const utcMinutes = now.getUTCHours()*60 + now.getUTCMinutes();
  const istMinutes = (utcMinutes + istOffset) % (24*60);
  const day = now.getUTCDay(); // adjust for date-line, but day-of-week is close enough here
  const isWeekday = day >= 1 && day <= 5;
  return isWeekday && istMinutes >= (9*60+15) && istMinutes <= (15*60+30);
}

const STALL_THRESHOLD_MS = 90 * 1000; // 90 seconds with no real tick = considered stalled

setInterval(() => {
  if(!currentAccessToken || !isMarketHoursIST()) return; // nothing to watch if not logged in or market closed
  const staleFor = lastTickReceivedAt ? Date.now() - new Date(lastTickReceivedAt).getTime() : Infinity;
  if(staleFor > STALL_THRESHOLD_MS){
    console.log(`No real tick for over ${Math.round(staleFor/1000)}s during market hours — forcing a fresh Fyers reconnect (this SDK is known to go silent without an error).`);
    try{ if(fyersSocket) fyersSocket.close(); } catch(e){ /* ignore */ }
    startFyersConnection(currentAccessToken);
  }
}, 30000); // check every 30 seconds

// ============ web server: auth page + WebSocket relay, sharing one port ============
const server = http.createServer(async (req, res) => {
  // CORS: your WordPress site and this Railway app are different origins — without
  // these headers, the browser blocks the Buy/Sell fetch() requests entirely.
  res.setHeader('Access-Control-Allow-Origin', '*');
  res.setHeader('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
  res.setHeader('Access-Control-Allow-Headers', 'Content-Type');
  if (req.method === 'OPTIONS') {
    res.writeHead(204);
    res.end();
    return;
  }

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
        fyers.setAccessToken(currentAccessToken);

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
        console.log('Order placement threw an exception:', err.message, err.stack);
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

function buildPayload(){
  const orb5 = computeOrbBreakouts(5);
  const orb15 = computeOrbBreakouts(15);
  return {
    ...computeScreeners(),
    slotHistory,
    orb5Up: orb5.up, orb5Down: orb5.down,
    orb15Up: orb15.up, orb15Down: orb15.down,
    orb5Locked: orb5LockedFlag, orb15Locked: orb15LockedFlag
  };
}

wss.on('connection', (ws, req) => {
  const parsed = url.parse(req.url, true);
  if (parsed.query.token !== RELAY_TOKEN) {
    ws.close(4001, 'Invalid token');
    return;
  }
  console.log('Browser tool connected to relay.');
  ws.send(JSON.stringify(buildPayload())); // includes full slotHistory so far today
});

function broadcastScreeners() {
  const payload = JSON.stringify(buildPayload());
  wss.clients.forEach(client => {
    if (client.readyState === WebSocket.OPEN) client.send(payload);
  });
}

// throttle broadcasts to at most once per second — without this, active market hours
// (Fyers can send 1000+ ticks/sec) would trigger a full computeScreeners() + JSON.stringify
// + broadcast on every single tick, which is almost certainly what caused the OOM crashes.
let broadcastPending = false;
function scheduleBroadcast() {
  if (broadcastPending) return;
  broadcastPending = true;
  setTimeout(() => { broadcastPending = false; broadcastScreeners(); }, 1000);
}

server.listen(PORT, () => {
  console.log(`Server listening on port ${PORT}. Visit your Railway URL to complete daily login.`);
});
