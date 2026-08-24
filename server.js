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
 *
 * --- RECONNECT BACKOFF / CIRCUIT BREAKER (2026-08 fix) ---
 * Previously, the stall watchdog retried a fresh Fyers connection every 30s
 * forever, with no backoff and no limit — including while the token itself
 * was being rejected on every single subscribe attempt (code -15, "Please
 * provide valid token"). During one incident this ran for 30+ hours straight,
 * hammering Fyers' subscribe endpoint hundreds of times even immediately
 * after a fresh login. That's both wasteful and risks tripping Fyers-side
 * rate limiting or abuse detection on the app itself.
 *
 * Now: each consecutive failed subscribe increases the wait before the next
 * attempt (exponential backoff, capped). After MAX_CONSECUTIVE_FAILURES in a
 * row, auto-retry stops entirely and the app sets needsRelogin = true, shown
 * clearly on the status page — instead of silently spinning forever. The
 * counters reset the moment a real tick comes in.
 *
 * --- TREND SCANNER WIRING (2026-08 addition) ---
 * trend_scanner.js must be uploaded alongside this file (same folder). It
 * builds 5-min/15-min/Daily candles from the same live ticks this file
 * already receives, computes EMA20/RSI14/ADX14/SuperTrend/VWAP/Pivots per
 * symbol, and classifies Bullish/Bearish only when every indicator agrees.
 * See trend_scanner.js's own header comment for the full rule set. Four
 * hooks tie it in below: the require() near the top, a backfillHistory()
 * call right after daily login succeeds, a processTick() call inside the
 * tick handler, and a trendScanner key added to buildPayload()'s output.
 */

const fs = require('fs');
const path = require('path');
const http = require('http');
const https = require('https');
const url = require('url');
const WebSocket = require('ws');
// Patches a real bug in fyers-api-v3's tbtsocket/tbtSocket.js: it calls https.get()
// without importing 'https' first, causing "https is not defined" and silently falling
// back to a generic hardcoded URL instead of fetching the real, account-specific socket
// URL. Making it available globally here fixes this without needing to touch node_modules
// (which gets reinstalled fresh on every deploy anyway).
global.https = require('https');

const { fyersModel, fyersDataSocket } = require('fyers-api-v3');
// 2026-08-16: wrapped in try/catch so a missing/broken trend_scanner.js can
// NEVER crash the entire app again (it did — every core screener, the live
// feed, everything went down because this one require() failed). If the file
// is missing or fails to load, trendScannerAvailable stays false and every
// trend-scanner call below becomes a safe no-op — the rest of the app runs
// completely normally either way.
let trendScanner = null;
let trendScannerAvailable = false;
try {
  trendScanner = require('./trend_scanner.js');
  trendScannerAvailable = true;
} catch (err) {
  console.error('Trend scanner module failed to load — trend scanner features disabled, rest of the app continues normally. Error:', err.message);
}

// Safety net: without this, ANY uncaught exception — including ones thrown deep inside
// Fyers' own SDK code that we can't directly control (e.g. a race condition during
// reconnect) — crashes the entire Node process, wiping the day's login session and
// in-memory state. This converts a fatal crash into a logged, recoverable error instead.
// The underlying triggering bug should still be fixed where possible (see the watchdog
// grace-period fix below) — this is a backstop, not a substitute for that.
process.on('uncaughtException', (err) => {
  console.error('Uncaught exception (recovered, process kept running):', err.message, err.stack);
});

const PORT = process.env.PORT || 3000;
const APP_ID = process.env.FYERS_APP_ID;
const SECRET_KEY = process.env.FYERS_SECRET_KEY;
const REDIRECT_URI = process.env.FYERS_REDIRECT_URI;
const RELAY_TOKEN = process.env.RELAY_TOKEN;

// Telegram notifications for the Strong/Weak Intraday Scanner — optional.
// TELEGRAM_BOT_TOKEN must be set (create a bot via @BotFather on Telegram)
// for notifications to actually send; if it's missing, the app just logs a
// one-time notice and continues running normally with notifications off —
// this was deliberately made non-fatal, unlike the Fyers credentials above,
// since notifications are a nice-to-have, not core to the app working.
const TELEGRAM_BOT_TOKEN = process.env.TELEGRAM_BOT_TOKEN;
const TELEGRAM_CHAT_ID = process.env.TELEGRAM_CHAT_ID || '-1001816364014';

let currentAccessToken = null; // stored after daily login, needed for placing orders

if (!APP_ID || !SECRET_KEY || !REDIRECT_URI || !RELAY_TOKEN) {
  console.error('\nMissing required environment variables. Set FYERS_APP_ID, FYERS_SECRET_KEY, FYERS_REDIRECT_URI, and RELAY_TOKEN in the Railway dashboard (Variables tab).\n');
  process.exit(1);
}

if (!TELEGRAM_BOT_TOKEN) {
  console.log('TELEGRAM_BOT_TOKEN not set — Strong/Weak Scanner Telegram notifications are disabled. Set it in Railway Variables to enable them.');
}

const SYMBOLS_PATH = path.join(__dirname, 'symbols.json');
if (!fs.existsSync(SYMBOLS_PATH)) {
  console.error('\nMissing symbols.json. Export it from the browser tool and upload it into this same folder in GitHub.\n');
  process.exit(1);
}
const symbols = JSON.parse(fs.readFileSync(SYMBOLS_PATH, 'utf8'));
console.log(`Loaded ${symbols.length} symbols to track.`);

// Market-cap-filtered symbol set (Nifty 500 proxy for Market Cap >= 10,000
// Cr) — see market_cap_filter.py for how this file gets generated. OPTIONAL
// and applies ONLY to the Momentum Scanner, not the whole app — every other
// screener (Strong/Weak, Open=Low/High, etc.) keeps tracking the full
// symbols.json universe as before, since only the Momentum Scanner's
// reference conditions asked for a market-cap floor. If this file isn't
// present, the Momentum Scanner falls back to the full symbol list with a
// clear one-time log message, rather than silently running unfiltered.
const MARKET_CAP_SYMBOLS_PATH = path.join(__dirname, 'symbols_marketcap_filtered.json');
let momentumScannerSymbols = null; // null = "use the full list" (fallback)
if (fs.existsSync(MARKET_CAP_SYMBOLS_PATH)) {
  try {
    momentumScannerSymbols = JSON.parse(fs.readFileSync(MARKET_CAP_SYMBOLS_PATH, 'utf8'));
    console.log(`Loaded ${momentumScannerSymbols.length} market-cap-filtered symbols for the Momentum Scanner (from symbols_marketcap_filtered.json).`);
  } catch (err) {
    console.log('symbols_marketcap_filtered.json exists but failed to parse — Momentum Scanner will use the full symbol list instead:', err.message);
  }
} else {
  console.log('No symbols_marketcap_filtered.json found — Momentum Scanner will use the full symbol list (run market_cap_filter.py and upload its output to apply the Market Cap >= 10,000 Cr filter).');
}

// ============ live state per symbol ============
const state = {};
symbols.forEach(s => { state[s] = { open: null, high: null, low: null, ltp: null, volume: null, prevClose: null }; });
// The 210 stocks use their own Fyers symbol as both the subscribe symbol
// AND the state key, so the loop above is sufficient for them. The three
// indices are different: symbols.json now (correctly) holds their real
// Fyers subscribe symbols ("NSE:NIFTY50-INDEX" etc.), but every OTHER part
// of this codebase (HALF_DAY_SYMBOLS, discoverAndSubscribeMultiStrikes,
// state['NIFTY'] lookups throughout) expects the bare short name as the
// state key - so those bare-name objects need to be created explicitly
// here too, since nothing in symbols.json literally spells "NIFTY".
// Missing this was the reason ticks kept arriving (correctly translated
// by INDEX_TICK_SYMBOL_TO_STATE_KEY below) but were then silently
// discarded by updateStateFromTick's "if (!s) return" check.
['NIFTY', 'BANKNIFTY', 'SENSEX'].forEach(s => {
  if(!state[s]) state[s] = { open: null, high: null, low: null, ltp: null, volume: null, prevClose: null };
});
let lastTickReceivedAt = null; // tracks the last REAL price tick, separate from relay-connection status —
                                 // lets you tell "connected but Fyers feed has gone quiet" apart from
                                 // "genuinely fine, just between ticks"
let fyersSocket = null;
let isLive = false;
let lastConnectionAttemptAt = null; // tracks when the current connection attempt started,
                                     // so the watchdog can give it a fair grace period

// ============ reconnect backoff / circuit breaker state ============
const MAX_CONSECUTIVE_FAILURES = 8;     // stop auto-retrying after this many failed subscribes in a row
const BASE_BACKOFF_MS = 30 * 1000;      // first retry wait (matches the old fixed 30s)
const MAX_BACKOFF_MS = 10 * 60 * 1000;  // cap backoff at 10 minutes between attempts
let consecutiveSubscribeFailures = 0;
let lastSubscribeFailureAt = null;
let lastSubscribeFailureReason = null;
let needsRelogin = false; // true once MAX_CONSECUTIVE_FAILURES is hit — auto-retry stops until a fresh login happens

function currentBackoffMs() {
  // 30s, 60s, 120s, 240s, ... capped at MAX_BACKOFF_MS
  const ms = BASE_BACKOFF_MS * Math.pow(2, consecutiveSubscribeFailures);
  return Math.min(ms, MAX_BACKOFF_MS);
}

function recordSubscribeFailure(reason) {
  consecutiveSubscribeFailures++;
  lastSubscribeFailureAt = new Date().toISOString();
  lastSubscribeFailureReason = reason;
  console.log(`Subscribe failure #${consecutiveSubscribeFailures} (${reason}). Next auto-retry backoff: ${Math.round(currentBackoffMs()/1000)}s.`);
  if (consecutiveSubscribeFailures >= MAX_CONSECUTIVE_FAILURES && !needsRelogin) {
    needsRelogin = true;
    console.log(`*** ${MAX_CONSECUTIVE_FAILURES} consecutive subscribe failures — stopping auto-retry. Visit the app's status page and redo the daily login. ***`);
  }
}

function recordSubscribeSuccess() {
  if (consecutiveSubscribeFailures > 0 || needsRelogin) {
    console.log('Real tick received — clearing subscribe-failure counters.');
  }
  consecutiveSubscribeFailures = 0;
  lastSubscribeFailureAt = null;
  lastSubscribeFailureReason = null;
  needsRelogin = false;
}

// ============ tracked strike depth (user enters one strike, we watch its CE+PE) ============
let trackedStrikeSymbols = { ce: null, pe: null, strike: null };
let trackedStrikeDepth = { ce: null, pe: null }; // { maxBuyPrice, maxBuyQty, maxSellPrice, maxSellQty, source: '5-level'|'50-level' }
let currentTbtSocket = null; // so a new strike lookup can unsubscribe the old symbols first

// given a 5-level depth tick (bid_price1-5/ask_price1-5/bid_size1-5/ask_size1-5), finds
// which price level has the largest quantity on each side
function computeMaxLevelsFrom5(tick){
  let maxBuyQty = -1, maxBuyPrice = null, maxSellQty = -1, maxSellPrice = null;
  for(let i = 1; i <= 5; i++){
    const bidPrice = tick[`bid_price${i}`], bidSize = tick[`bid_size${i}`];
    const askPrice = tick[`ask_price${i}`], askSize = tick[`ask_size${i}`];
    if(bidPrice > 0 && bidSize > maxBuyQty){ maxBuyQty = bidSize; maxBuyPrice = bidPrice; }
    if(askPrice > 0 && askSize > maxSellQty){ maxSellQty = askSize; maxSellPrice = askPrice; }
  }
  return { maxBuyPrice, maxBuyQty: maxBuyQty >= 0 ? maxBuyQty : null, maxSellPrice, maxSellQty: maxSellQty >= 0 ? maxSellQty : null, source: '5-level' };
}

// given a TBT depth object (50-element bidprice/askprice/bidqty/askqty arrays), finds the
// same thing across the full depth
function computeMaxLevelsFrom50(depth){
  let maxBuyQty = -1, maxBuyPrice = null, maxSellQty = -1, maxSellPrice = null;
  for(let i = 0; i < 50; i++){
    if(depth.bidprice[i] > 0 && depth.bidqty[i] > maxBuyQty){ maxBuyQty = depth.bidqty[i]; maxBuyPrice = depth.bidprice[i]; }
    if(depth.askprice[i] > 0 && depth.askqty[i] > maxSellQty){ maxSellQty = depth.askqty[i]; maxSellPrice = depth.askprice[i]; }
  }
  return { maxBuyPrice, maxBuyQty: maxBuyQty >= 0 ? maxBuyQty : null, maxSellPrice, maxSellQty: maxSellQty >= 0 ? maxSellQty : null, source: '50-level' };
}

function pick(obj, candidates) {
  for (const key of candidates) {
    if (obj[key] !== undefined && obj[key] !== null) return obj[key];
  }
  return null;
}

// Sends one message to the configured Telegram chat via the Bot API. Fire-
// and-forget by design (callers don't await this) — a failed/slow Telegram
// send should never block or slow down the live tick/broadcast pipeline.
// No-ops quietly if TELEGRAM_BOT_TOKEN isn't configured.
function sendTelegramMessage(text){
  if(!TELEGRAM_BOT_TOKEN) return;
  const payload = JSON.stringify({ chat_id: TELEGRAM_CHAT_ID, text });
  const options = {
    hostname: 'api.telegram.org',
    path: `/bot${TELEGRAM_BOT_TOKEN}/sendMessage`,
    method: 'POST',
    headers: { 'Content-Type': 'application/json', 'Content-Length': Buffer.byteLength(payload) },
  };
  const req = https.request(options, (res) => {
    let data = '';
    res.on('data', chunk => { data += chunk; });
    res.on('end', () => {
      if(res.statusCode !== 200){
        console.log('Telegram send failed:', res.statusCode, data);
      }
    });
  });
  req.on('error', (err) => { console.log('Telegram send error:', err.message); });
  req.write(payload);
  req.end();
}

// Sends one Telegram message summarizing every symbol that matched an
// Open=Low/Open=High screener at its lock moment (9:21 for 5-min, 9:31 for
// 15-min) — a distinct emoji per screener so all four stay visually
// distinguishable at a glance in a shared chat. Sends nothing if the list
// is empty, to avoid a daily "0 matches" message cluttering the chat.
function sendOpenEqScreenerAlert(label, emoji, list, lockTime){
  if(!TELEGRAM_BOT_TOKEN || !list || list.length === 0) return;
  const symbolLines = list.map(r => `• ${r.symbol} (LTP ${r.ltp})`).join('\n');
  const message = `${emoji} ${label} locked at ${lockTime} — ${list.length} symbol(s):\n${symbolLines}`;
  sendTelegramMessage(message);
}

// Called once per broadcast cycle — drains whatever Strong/Weak/Turning-Weak
// notifications trend_scanner.js queued up since the last check, and sends
// each one. Safe to call even when nothing's pending (drainPendingNotifications
// returns an empty array in that case, this is then a no-op).
function checkAndSendStrongWeakNotifications(){
  if(!trendScannerAvailable || !TELEGRAM_BOT_TOKEN) return;
  const messages = trendScanner.drainPendingNotifications();
  messages.forEach(msg => sendTelegramMessage(msg));
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
  if (ltp !== null) { s.ltp = ltp; updateRoundNumberCandle(symbol, ltp); updateSecondHalfTracking(symbol, ltp); }
  if (volume !== null) s.volume = volume;
  if (prevClose !== null) s.prevClose = prevClose;
}

const EPS = 0.01;

// ============ Round Number Scanner — 15-min candles, continuously live all day ============
let roundNumberCandleState = {}; // symbol -> {bucketStart, open, high, low, close}
let roundNumberMatches = {};     // symbol -> {roundNumber, closePrice, matchedAt}
let roundNumberTolerancePct = 0.1; // configurable via /set-round-tolerance
let roundNumberDateKey = null;
let roundNumberHistory = [];         // running history of 15-min snapshots, newest first
let lastRoundNumberSnapshotBucket = null; // which 15-min bucket we last took a snapshot for

const ROUND_NUMBER_STEP = 100;

function nearestRoundNumber(price){
  return Math.round(price / ROUND_NUMBER_STEP) * ROUND_NUMBER_STEP;
}

function roundNumberMatchFor(price){
  const nearest = nearestRoundNumber(price);
  if(nearest <= 0) return null; // guards very low-priced stocks where "nearest round number" would be 0
  const diffPct = Math.abs(price - nearest) / nearest * 100;
  return diffPct <= roundNumberTolerancePct ? nearest : null;
}

function get15MinBucketStart(minutes){
  return Math.floor(minutes / 15) * 15;
}

function updateRoundNumberCandle(symbol, price){
  const { dateKey, minutes } = getISTDateKeyAndMinutes();

  if(roundNumberDateKey !== dateKey){
    roundNumberDateKey = dateKey;
    roundNumberCandleState = {};
    roundNumberMatches = {};
  }

  const bucketStart = get15MinBucketStart(minutes);
  const existing = roundNumberCandleState[symbol];

  if(!existing || existing.bucketStart !== bucketStart){
    if(existing){
      const match = roundNumberMatchFor(existing.close);
      if(match !== null){
        roundNumberMatches[symbol] = {
          roundNumber: match,
          closePrice: existing.close,
          matchedAt: `${String(Math.floor(existing.bucketStart/60)).padStart(2,'0')}:${String(existing.bucketStart%60).padStart(2,'0')}`,
        };
      } else {
        delete roundNumberMatches[symbol];
      }
    }
    roundNumberCandleState[symbol] = { bucketStart, open: price, high: price, low: price, close: price };
  } else {
    existing.high = Math.max(existing.high, price);
    existing.low = Math.min(existing.low, price);
    existing.close = price;
  }
}

function buildRoundNumberRows(){
  return Object.entries(roundNumberMatches).map(([symbol, m]) => ({
    symbol,
    roundNumber: m.roundNumber,
    closePrice: m.closePrice,
    ltp: (state[symbol] && state[symbol].ltp !== null) ? state[symbol].ltp : m.closePrice,
    matchedAt: m.matchedAt,
  }));
}

function checkAndRecordRoundNumberSnapshot(){
  const { minutes } = getISTDateKeyAndMinutes();
  const bucketStart = get15MinBucketStart(minutes);
  if(lastRoundNumberSnapshotBucket === bucketStart) return;
  lastRoundNumberSnapshotBucket = bucketStart;

  const rows = buildRoundNumberRows();
  const label = `${String(Math.floor(bucketStart/60)).padStart(2,'0')}:${String(bucketStart%60).padStart(2,'0')}`;
  roundNumberHistory.unshift({ time: label, matches: rows });
  saveRoundNumberHistory();
}

const SCREENER_SCAN_TIME_MINUTES = 9 * 60 + 21;
const BTST_LOCK_TIME_MINUTES = 15 * 60 + 10; // 3:10 PM — matches the backtest's own entry time exactly
const BTST_VOLUME_RATIO_THRESHOLD = 1.5; // matches the backtest's default; delivery% is checked client-side, not here

let btstLockedRows = null;
let btstLockDone = false;
let btstLockDateKey = null;
let btstLockTimestamp = null;

function checkAndRunBtstLock(){
  const { dateKey, minutes } = getISTDateKeyAndMinutes();

  if(btstLockDateKey !== dateKey){
    btstLockDateKey = dateKey;
    btstLockDone = false;
    btstLockedRows = null;
    btstLockTimestamp = null;
  }

  if(!btstLockDone && minutes >= BTST_LOCK_TIME_MINUTES){
    const payload = trendScannerAvailable ? trendScanner.getBtstVolumeRatioPayload(state) : { rows: [] };
    btstLockedRows = payload.rows.filter(r => r.volumeRatio > BTST_VOLUME_RATIO_THRESHOLD);
    btstLockDone = true;
    btstLockTimestamp = timeLabel();
    console.log(`BTST volume-ratio list locked at ${btstLockTimestamp} — ${btstLockedRows.length} symbol(s) above ${BTST_VOLUME_RATIO_THRESHOLD}x (delivery% filter applied client-side, not reflected in this count).`);
    saveBtstLock();
  }
}

// Narrow CPR (Next-Day) — locks at market close (3:30 PM), since only then
// is today's H/L/C truly final, making "tomorrow's projected CPR" an
// actual, definitive projection rather than a still-forming one. Matches
// the exact formula validated in backtest_narrow_cpr.js.
const NARROW_CPR_LOCK_TIME_MINUTES = 15 * 60 + 30; // 3:30 PM, market close

let narrowCprLockedRows = null;
let narrowCprLockDone = false;
let narrowCprLockDateKey = null;
let narrowCprLockTimestamp = null;

function checkAndRunNarrowCprLock(){
  const { dateKey, minutes } = getISTDateKeyAndMinutes();

  if(narrowCprLockDateKey !== dateKey){
    narrowCprLockDateKey = dateKey;
    narrowCprLockDone = false;
    narrowCprLockedRows = null;
    narrowCprLockTimestamp = null;
  }

  if(!narrowCprLockDone && minutes >= NARROW_CPR_LOCK_TIME_MINUTES){
    const payload = trendScannerAvailable ? trendScanner.getNarrowCprPayload(state) : { rows: [] };
    narrowCprLockedRows = payload.rows;
    narrowCprLockDone = true;
    narrowCprLockTimestamp = timeLabel();
    console.log(`Narrow CPR (next-day) list locked at ${narrowCprLockTimestamp} — ${narrowCprLockedRows.length} symbol(s) qualify for tomorrow.`);
    saveNarrowCprLock();
  }
}

// Narrow Camarilla — same 3:30 PM lock convention as Narrow CPR, for the
// same reason: today's H/L/C is only truly final at market close. Matches
// the exact formula validated in backtest_narrow_camarilla.js, the most
// trustworthy of the "narrow range" backtests (smallest ambiguous-day
// rate, ~8% vs ~52% for the CPR versions). Recommended trade, per that
// backtest: 1% target / 0.5% stop, entry at whichever of R3/S3 breaks first.
const NARROW_CAMARILLA_LOCK_TIME_MINUTES = 15 * 60 + 30; // 3:30 PM, market close

let narrowCamarillaLockedRows = null;
let narrowCamarillaLockDone = false;
let narrowCamarillaLockDateKey = null;
let narrowCamarillaLockTimestamp = null;

function checkAndRunNarrowCamarillaLock(){
  const { dateKey, minutes } = getISTDateKeyAndMinutes();

  if(narrowCamarillaLockDateKey !== dateKey){
    narrowCamarillaLockDateKey = dateKey;
    narrowCamarillaLockDone = false;
    narrowCamarillaLockedRows = null;
    narrowCamarillaLockTimestamp = null;
  }

  if(!narrowCamarillaLockDone && minutes >= NARROW_CAMARILLA_LOCK_TIME_MINUTES){
    const payload = trendScannerAvailable ? trendScanner.getNarrowCamarillaPayload(state) : { rows: [] };
    narrowCamarillaLockedRows = payload.rows;
    narrowCamarillaLockDone = true;
    narrowCamarillaLockTimestamp = timeLabel();
    console.log(`Narrow Camarilla list locked at ${narrowCamarillaLockTimestamp} — ${narrowCamarillaLockedRows.length} symbol(s) qualify for tomorrow.`);
    saveNarrowCamarillaLock();
  }
}


let screenerScanResults = { openlow: null, openhigh: null, gapneutral: null, openhighsimple: null, openlowyestlow: null, openlowsimple: null };
let screenerScanDone = false;
let screenerScanDateKey = null;
let screenerScanTimestamp = null;

function checkAndRunScreenerScan(){
  const { dateKey, minutes } = getISTDateKeyAndMinutes();

  if(screenerScanDateKey !== dateKey){
    screenerScanDateKey = dateKey;
    screenerScanDone = false;
    screenerScanResults = { openlow: null, openhigh: null, gapneutral: null, openhighsimple: null, openlowyestlow: null, openlowsimple: null };
    screenerScanTimestamp = null;
  }

  if(!screenerScanDone && minutes >= SCREENER_SCAN_TIME_MINUTES){
    const snap = computeScreenersUnrestricted();
    screenerScanResults.openlow = snap.openEqLow;
    screenerScanResults.openhigh = snap.openEqHigh;
    screenerScanResults.gapneutral = snap.gapNeutral;
    screenerScanResults.openhighsimple = snap.openEqHighSimple;
    screenerScanResults.openlowyestlow = snap.openEqLowYestLow;
    screenerScanResults.openlowsimple = snap.openEqLowSimple;
    screenerScanDone = true;
    screenerScanTimestamp = timeLabel();
    console.log(`Screener scan locked at ${screenerScanTimestamp} — Open=Low: ${screenerScanResults.openlow.length}, Open=High: ${screenerScanResults.openhigh.length}, Gap-Neutral: ${screenerScanResults.gapneutral.length}, Open=High(simple): ${screenerScanResults.openhighsimple.length}, Open=Low(simple): ${screenerScanResults.openlowsimple.length}, Open=Low vs Yest-Low: ${screenerScanResults.openlowyestlow.length} symbols.`);
    saveScreenerScanResults();
    sendOpenEqScreenerAlert('OPEN=LOW (5-min / "first-5min-buy-candle")', '📗', screenerScanResults.openlow, screenerScanTimestamp);
    sendOpenEqScreenerAlert('OPEN=HIGH (5-min / "first-5min-sell-candle")', '📕', screenerScanResults.openhigh, screenerScanTimestamp);
    sendOpenEqScreenerAlert('OPEN=LOW SIMPLE (5-min, no yesterday condition)', '🟢', screenerScanResults.openlowsimple, screenerScanTimestamp);
    sendOpenEqScreenerAlert('OPEN=HIGH SIMPLE (5-min, no yesterday condition)', '🔴', screenerScanResults.openhighsimple, screenerScanTimestamp);
  }
}

function computeScreenersUnrestricted() {
  const openEqLow = [], openEqHigh = [], gapNeutral = [], openEqHighSimple = [], openEqLowYestLow = [], openEqLowSimple = [];
  Object.keys(state).forEach(symbol => {
    const s = state[symbol];
    if (s.open === null || s.high === null || s.low === null) return;

    const first5Min = first5MinLocked[symbol];
    const yest = yesterdaySnapshot[symbol];
    if (first5Min && yest) {
      const openEqualsFirst5MinLow = Math.abs(s.open - first5Min.low) <= EPS;
      const closedAboveYesterdayHigh = first5Min.close > yest.dayHigh;
      if (openEqualsFirst5MinLow && closedAboveYesterdayHigh) {
        openEqLow.push({
          symbol, first5MinOpen: s.open, first5MinLow: first5Min.low,
          first5MinClose: first5Min.close, yesterdayHigh: yest.dayHigh, ltp: s.ltp,
        });
      }
    }

    if (first5Min && yest) {
      const openEqualsFirst5MinHigh = Math.abs(s.open - first5Min.high) <= EPS;
      const closedBelowYesterdayLow = first5Min.close < yest.dayLow;
      if (openEqualsFirst5MinHigh && closedBelowYesterdayLow) {
        openEqHigh.push({
          symbol, first5MinOpen: s.open, first5MinHigh: first5Min.high,
          first5MinClose: first5Min.close, yesterdayLow: yest.dayLow, ltp: s.ltp,
        });
      }
    }
    if (s.prevClose !== null && Math.abs(s.open - s.prevClose) <= EPS) gapNeutral.push({ symbol, open: s.open, prevClose: s.prevClose, ltp: s.ltp });

    // Open=High, no yesterday comparison at all — just "did the first 5 min never
    // trade above the open" on its own. Doesn't need yesterdaySnapshot to exist,
    // so this can populate even before a "yesterday" snapshot has been captured.
    if (first5Min) {
      const openEqualsFirst5MinHigh = Math.abs(s.open - first5Min.high) <= EPS;
      if (openEqualsFirst5MinHigh) {
        openEqHighSimple.push({
          symbol, first5MinOpen: s.open, first5MinHigh: first5Min.high,
          first5MinClose: first5Min.close, ltp: s.ltp,
        });
      }

      // Reciprocal of the above: Open=Low, no yesterday comparison — "did the
      // first 5 min never trade below the open" on its own.
      const openEqualsFirst5MinLowSimple = Math.abs(s.open - first5Min.low) <= EPS;
      if (openEqualsFirst5MinLowSimple) {
        openEqLowSimple.push({
          symbol, first5MinOpen: s.open, first5MinLow: first5Min.low,
          first5MinClose: first5Min.close, ltp: s.ltp,
        });
      }
    }

    // Open=Low, but compared against yesterday's LOW instead of yesterday's HIGH —
    // a looser bullish threshold than the openEqLow screener above (that one
    // requires closing above yesterday's entire range; this only requires
    // closing above yesterday's low, so more symbols will typically qualify).
    if (first5Min && yest) {
      const openEqualsFirst5MinLow = Math.abs(s.open - first5Min.low) <= EPS;
      const closedAboveYesterdayLow = first5Min.close > yest.dayLow;
      if (openEqualsFirst5MinLow && closedAboveYesterdayLow) {
        openEqLowYestLow.push({
          symbol, first5MinOpen: s.open, first5MinLow: first5Min.low,
          first5MinClose: first5Min.close, yesterdayLow: yest.dayLow, ltp: s.ltp,
        });
      }
    }
  });
  return { openEqLow, openEqHigh, gapNeutral, openEqHighSimple, openEqLowYestLow, openEqLowSimple };
}

function buildLockedScreenerRows(key){
  const frozen = screenerScanResults[key];
  if(!frozen) return [];
  return frozen.map(r => ({
    ...r,
    ltp: (state[r.symbol] && state[r.symbol].ltp !== null) ? state[r.symbol].ltp : r.ltp,
    dayHigh: (state[r.symbol] && state[r.symbol].high !== null) ? state[r.symbol].high : null,
    dayLow: (state[r.symbol] && state[r.symbol].low !== null) ? state[r.symbol].low : null,
    matchedAt: screenerScanTimestamp,
  }));
}

// ============ 15-min screeners (mirrors the 5-min ones above) ============
// Same pattern, same logic, just using the first 15 minutes (9:15-9:30) of the
// day instead of the first 5 (9:15-9:20), and locking one minute later (9:31
// instead of 9:21). Open=Low and Open=High are both covered — Gap-Neutral was
// not requested for the 15-min version.
const SCREENER_SCAN_15M_TIME_MINUTES = 9 * 60 + 31;

let screenerScan15mResults = { openlow: null, openhigh: null, openhighsimple: null, openlowyestlow: null, openlowsimple: null };
let screenerScan15mDone = false;
let screenerScan15mDateKey = null;
let screenerScan15mTimestamp = null;

function checkAndRunScreenerScan15m(){
  const { dateKey, minutes } = getISTDateKeyAndMinutes();

  if(screenerScan15mDateKey !== dateKey){
    screenerScan15mDateKey = dateKey;
    screenerScan15mDone = false;
    screenerScan15mResults = { openlow: null, openhigh: null, openhighsimple: null, openlowyestlow: null, openlowsimple: null };
    screenerScan15mTimestamp = null;
  }

  if(!screenerScan15mDone && minutes >= SCREENER_SCAN_15M_TIME_MINUTES){
    const snap = computeScreener15mUnrestricted();
    screenerScan15mResults.openlow = snap.openEqLow;
    screenerScan15mResults.openhigh = snap.openEqHigh;
    screenerScan15mResults.openhighsimple = snap.openEqHighSimple;
    screenerScan15mResults.openlowyestlow = snap.openEqLowYestLow;
    screenerScan15mResults.openlowsimple = snap.openEqLowSimple;
    screenerScan15mDone = true;
    screenerScan15mTimestamp = timeLabel();
    console.log(`15-min screener scan locked at ${screenerScan15mTimestamp} — Open=Low: ${screenerScan15mResults.openlow.length}, Open=High: ${screenerScan15mResults.openhigh.length}, Open=High(simple): ${screenerScan15mResults.openhighsimple.length}, Open=Low(simple): ${screenerScan15mResults.openlowsimple.length}, Open=Low vs Yest-Low: ${screenerScan15mResults.openlowyestlow.length} symbols.`);
    saveScreenerScan15mResults();
    sendOpenEqScreenerAlert('OPEN=LOW (15-min)', '📘', screenerScan15mResults.openlow, screenerScan15mTimestamp);
    sendOpenEqScreenerAlert('OPEN=HIGH (15-min)', '📙', screenerScan15mResults.openhigh, screenerScan15mTimestamp);
    sendOpenEqScreenerAlert('OPEN=LOW SIMPLE (15-min, no yesterday condition)', '🔵', screenerScan15mResults.openlowsimple, screenerScan15mTimestamp);
    sendOpenEqScreenerAlert('OPEN=HIGH SIMPLE (15-min, no yesterday condition)', '🟠', screenerScan15mResults.openhighsimple, screenerScan15mTimestamp);
  }
}

function computeScreener15mUnrestricted() {
  const openEqLow = [], openEqHigh = [], openEqHighSimple = [], openEqLowYestLow = [], openEqLowSimple = [];
  Object.keys(state).forEach(symbol => {
    const s = state[symbol];
    if (s.open === null || s.high === null || s.low === null) return;

    const first15Min = first15MinLocked[symbol];
    const yest = yesterdaySnapshot[symbol];
    if (first15Min && yest) {
      const openEqualsFirst15MinLow = Math.abs(s.open - first15Min.low) <= EPS;
      const closedAboveYesterdayHigh = first15Min.close > yest.dayHigh;
      if (openEqualsFirst15MinLow && closedAboveYesterdayHigh) {
        openEqLow.push({
          symbol, first15MinOpen: s.open, first15MinLow: first15Min.low,
          first15MinClose: first15Min.close, yesterdayHigh: yest.dayHigh, ltp: s.ltp,
        });
      }

      const openEqualsFirst15MinHigh = Math.abs(s.open - first15Min.high) <= EPS;
      const closedBelowYesterdayLow = first15Min.close < yest.dayLow;
      if (openEqualsFirst15MinHigh && closedBelowYesterdayLow) {
        openEqHigh.push({
          symbol, first15MinOpen: s.open, first15MinHigh: first15Min.high,
          first15MinClose: first15Min.close, yesterdayLow: yest.dayLow, ltp: s.ltp,
        });
      }

      // Open=Low vs yesterday's LOW (not HIGH) — same looser-threshold variant as
      // the 5-min version above.
      const closedAboveYesterdayLow = first15Min.close > yest.dayLow;
      if (openEqualsFirst15MinLow && closedAboveYesterdayLow) {
        openEqLowYestLow.push({
          symbol, first15MinOpen: s.open, first15MinLow: first15Min.low,
          first15MinClose: first15Min.close, yesterdayLow: yest.dayLow, ltp: s.ltp,
        });
      }
    }

    // Open=High, no yesterday comparison — doesn't need yest, only first15Min.
    if (first15Min) {
      const openEqualsFirst15MinHigh = Math.abs(s.open - first15Min.high) <= EPS;
      if (openEqualsFirst15MinHigh) {
        openEqHighSimple.push({
          symbol, first15MinOpen: s.open, first15MinHigh: first15Min.high,
          first15MinClose: first15Min.close, ltp: s.ltp,
        });
      }

      // Reciprocal: Open=Low, no yesterday comparison.
      const openEqualsFirst15MinLowSimple = Math.abs(s.open - first15Min.low) <= EPS;
      if (openEqualsFirst15MinLowSimple) {
        openEqLowSimple.push({
          symbol, first15MinOpen: s.open, first15MinLow: first15Min.low,
          first15MinClose: first15Min.close, ltp: s.ltp,
        });
      }
    }
  });
  return { openEqLow, openEqHigh, openEqHighSimple, openEqLowYestLow, openEqLowSimple };
}

function buildLockedScreener15mRows(key){
  const frozen = screenerScan15mResults[key];
  if(!frozen) return [];
  return frozen.map(r => ({
    ...r,
    ltp: (state[r.symbol] && state[r.symbol].ltp !== null) ? state[r.symbol].ltp : r.ltp,
    dayHigh: (state[r.symbol] && state[r.symbol].high !== null) ? state[r.symbol].high : null,
    dayLow: (state[r.symbol] && state[r.symbol].low !== null) ? state[r.symbol].low : null,
    matchedAt: screenerScan15mTimestamp,
  }));
}

const FIRST_5MIN_LOCK_MINUTES = 9 * 60 + 20;
const FIRST_5MIN_LOCK_HARD_CUTOFF_MINUTES = 9 * 60 + 25; // 5-min grace window, same pattern as the pre-market-close fix
const FIRST_15MIN_LOCK_MINUTES = 9 * 60 + 30; // 9:30 AM — end of the 9:15-9:30 window
const FIRST_15MIN_LOCK_HARD_CUTOFF_MINUTES = 9 * 60 + 35; // 5-min grace window, same pattern as the pre-market-close fix

// Top-3-Losers-at-9:16, Loser #2 short — locks ONCE per day, right at 9:16
// AM, matching the exact signal timing validated in backtest_top_losers_916.js
// (71-day, +0.311% EV, the second-strongest confirmed edge of the whole
// day's testing). Unlike the other live scanners, this is a one-shot daily
// ranking, not something that keeps recalculating all day - the ranking is
// only meaningful at that one specific moment.
const TOP3_LOSERS_916_LOCK_MINUTES = 9 * 60 + 16;
let top3Losers916Locked = null;
let top3Losers916LockedFlag = false;
let top3Losers916DateKey = null;

function checkAndLockTop3Losers916(){
  const { dateKey, minutes } = getISTDateKeyAndMinutes();
  if(top3Losers916DateKey !== dateKey){
    top3Losers916DateKey = dateKey;
    top3Losers916LockedFlag = false;
    top3Losers916Locked = null;
  }
  if(!top3Losers916LockedFlag && minutes >= TOP3_LOSERS_916_LOCK_MINUTES){
    const payload = trendScannerAvailable ? trendScanner.computeTop3LosersAt916(state) : { rows: [] };
    top3Losers916Locked = payload.rows;
    top3Losers916LockedFlag = true;
    const loser2 = top3Losers916Locked.find(r => r.rank === 2);
    console.log(`Top-3-Losers-at-9:16 locked — ${top3Losers916Locked.length} symbol(s) ranked.${loser2 ? ` Loser #2: ${loser2.symbol} (${loser2.dropPct.toFixed(2)}% drop, entry ${loser2.entryPrice.toFixed(2)}, stop ${loser2.stopPrice.toFixed(2)}, target ${loser2.targetPrice.toFixed(2)}).` : ''}`);
    saveTop3Losers916Lock();
  }
}

const PRE_MARKET_CLOSE_MINUTES = 9 * 60 + 9;
let preMarketClose = {};
let preMarketCloseLockedFlag = false;
let preMarketCloseDateKey = null;

// 2026-08-24 fix: this used to lock permanently the INSTANT minutes first
// passed PRE_MARKET_CLOSE_MINUTES, with no regard for whether the Fyers
// connection had actually had a chance to establish yet. On any restart
// happening shortly after 9:09 AM (a redeploy, a crash), this fired
// immediately with 0 symbols captured, and - being a one-shot lock - never
// retried for the rest of the day. Now: keeps retrying every cycle until
// EITHER at least one symbol has real data, OR a hard cutoff (market open,
// 9:15 AM) passes - past which "pre-market close" is genuinely
// unrecoverable anyway, so there's no point waiting further.
const PRE_MARKET_CLOSE_HARD_CUTOFF_MINUTES = 9 * 60 + 15;

function checkAndLockPreMarketClose(){
  const { dateKey, minutes } = getISTDateKeyAndMinutes();
  if(preMarketCloseDateKey !== dateKey){
    preMarketCloseDateKey = dateKey;
    preMarketCloseLockedFlag = false;
    preMarketClose = {};
  }
  if(preMarketCloseLockedFlag || minutes < PRE_MARKET_CLOSE_MINUTES) return;

  const captured = {};
  HALF_DAY_SYMBOLS.forEach(symbol => {
    const s = state[symbol];
    if(s && s.ltp !== null) captured[symbol] = s.ltp;
  });
  const gotAnyData = Object.keys(captured).length > 0;
  const pastHardCutoff = minutes >= PRE_MARKET_CLOSE_HARD_CUTOFF_MINUTES;

  if(gotAnyData || pastHardCutoff){
    preMarketClose = captured;
    preMarketCloseLockedFlag = true;
    if(gotAnyData){
      console.log(`Pre-market close captured for ${Object.keys(preMarketClose).length} symbol(s).`);
    } else {
      console.log(`Pre-market close: no symbol had live data by ${PRE_MARKET_CLOSE_HARD_CUTOFF_MINUTES/60|0}:${String(PRE_MARKET_CLOSE_HARD_CUTOFF_MINUTES%60).padStart(2,'0')} — giving up for today (likely a restart well after market open; discovery will fall back to live LTP instead, same as it already does).`);
    }
  }
  // else: keep retrying next cycle - the connection may still be establishing
}

const EOD_SNAPSHOT_MINUTES = 15 * 60 + 30;

let first5MinLocked = {};
let first5MinLockedFlag = false;
let first5MinDateKey = null;

let first15MinLocked = {};
let first15MinLockedFlag = false;
let first15MinDateKey = null;

let yesterdaySnapshot = {};
let eodSnapshotSavedToday = false;
let eodSnapshotDateKey = null;

const HALF_DAY_SYMBOLS = ['NIFTY', 'BANKNIFTY', 'SENSEX'];
const FIRST_HALF_LOCK_MINUTES = 9 * 60 + 15 + 195;

let firstHalfLocked = {};
let secondHalfRunning = {};
let secondHalfOpen = {};
let secondHalfLocked = {};
let yesterdayHalves = {};
let halfDayDateKey = null;
let firstHalfLockedFlag = false;
let secondHalfLockedFlag = false;

const STRIKE_INTERVALS = { NIFTY: 50, BANKNIFTY: 100, SENSEX: 100 };
const STRIKE_TRACK_RANGE = 20; // was 10, originally 5 — widened further since the server's ATM anchor still can't know what price a user manually enters on the ISP Selector page (that entry is client-side only, never sent back here) — this is the honest, reliable safety net regardless of whether pre-market ticks stream that day
const NSE_SYMBOL_MASTER_URL = 'https://public.fyers.in/sym_details/NSE_FO.csv';
const BSE_SYMBOL_MASTER_URL = 'https://public.fyers.in/sym_details/BSE_FO.csv';

let multiStrikeMeta = {};
let multiStrikeSymbolList = [];
let multiStrikeSelectedToday = false;
let multiStrikeDiscoveryInProgress = false;
let yesterdayMultiStrikeHalves = {};

// timeoutMs added 2026-08: without this, a hung request (network stall,
// unresponsive server) never resolves OR rejects the promise — which left
// discoverAndSubscribeMultiStrikes()'s multiStrikeDiscoveryInProgress flag
// stuck true forever, silently blocking ATM strike discovery for the rest
// of the trading day with zero error logged. Confirmed as the root cause
// of a real incident: the "Multi-strike ATM discovery" log line never
// appeared once in a full day's log, with no failure message either.
function fetchUrl(targetUrl, timeoutMs = 15000){
  return new Promise((resolve, reject) => {
    const req = https.get(targetUrl, (res) => {
      let data = '';
      res.on('data', chunk => { data += chunk; });
      res.on('end', () => resolve(data));
    });
    req.on('error', reject);
    req.setTimeout(timeoutMs, () => {
      req.destroy();
      reject(new Error(`Request to ${targetUrl} timed out after ${timeoutMs}ms`));
    });
  });
}

function parseStrikesFromCsv(csvText, indexSymbol, atmStrike, interval){
  if(!csvText) return {};
  const nowTs = Date.now() / 1000;
  const bestByKey = {};
  csvText.split('\n').forEach(line => {
    const cols = line.split(',');
    if(cols.length < 17) return;
    const optType = cols[16] ? cols[16].trim() : '';
    if(optType !== 'CE' && optType !== 'PE') return;
    const underlying = (cols[13] || '').trim().toUpperCase();
    if(underlying !== indexSymbol) return;
    const expiryTs = parseFloat(cols[8]);
    const strike = parseFloat(cols[15]);
    const fyersSymbol = (cols[9] || '').trim();
    if(isNaN(expiryTs) || isNaN(strike) || !fyersSymbol) return;
    if(expiryTs < nowTs) return;
    const key = `${strike}_${optType}`;
    if(!bestByKey[key] || expiryTs < bestByKey[key].expiryTs){
      bestByKey[key] = { expiryTs, fyersSymbol };
    }
  });

  const result = {};
  for(let offset = -STRIKE_TRACK_RANGE; offset <= STRIKE_TRACK_RANGE; offset++){
    const strike = atmStrike + offset * interval;
    const posLabel = offset === 0 ? 'ATM' : (offset > 0 ? `ATM+${offset}` : `ATM${offset}`);
    ['CE', 'PE'].forEach(optType => {
      const found = bestByKey[`${strike}_${optType}`];
      if(found){
        result[found.fyersSymbol] = { index: indexSymbol, relativePos: posLabel, type: optType, strike };
      }
    });
  }
  return result;
}

async function discoverAndSubscribeMultiStrikes(){
  if(multiStrikeSelectedToday || multiStrikeDiscoveryInProgress) return;
  const indices = ['NIFTY', 'BANKNIFTY', 'SENSEX'];
  const notReady = indices.filter(sym => !state[sym] || state[sym].ltp === null);
  if(notReady.length > 0) return;

  multiStrikeDiscoveryInProgress = true;
  try{
    const nseCsv = await fetchUrl(NSE_SYMBOL_MASTER_URL);
    let bseCsv = null;
    try{ bseCsv = await fetchUrl(BSE_SYMBOL_MASTER_URL); }
    catch(e){ console.log('Could not fetch BSE symbol master (SENSEX strikes will be skipped):', e.message); }

    // ATM anchor: prefer the captured pre-market close over the live LTP at
    // whatever moment this function happens to run. This function only
    // fires once all three indices have a valid LTP (the notReady check
    // above), which is usually a little INTO the regular session, not at
    // 9:08 AM pre-market close — if the index gapped between those two
    // moments, anchoring to the later live price silently drifts this
    // server's own tracked strike range away from whatever pre-market
    // price the ISP Selector page's manual entry is based on, no matter
    // how wide STRIKE_TRACK_RANGE is set. Anchoring to the SAME captured
    // pre-market value (when available) removes that mismatch at the
    // source instead of just padding around it. Falls back to live LTP if
    // pre-market wasn't captured that day (matches the same "unconfirmed"
    // caveat already noted on the ISP Selector page itself).
    function atmAnchorPrice(sym){
      return (preMarketClose && preMarketClose[sym] != null) ? preMarketClose[sym] : state[sym].ltp;
    }

    let meta = {};
    const atmLog = []; // collected for one clear diagnostic log line below
    ['NIFTY', 'BANKNIFTY'].forEach(sym => {
      const anchorPrice = atmAnchorPrice(sym);
      const anchorSource = (preMarketClose && preMarketClose[sym] != null) ? 'pre-market close' : 'live LTP';
      const atm = Math.round(anchorPrice / STRIKE_INTERVALS[sym]) * STRIKE_INTERVALS[sym];
      atmLog.push(`${sym}: anchor=${anchorPrice} (${anchorSource}) -> ATM=${atm}, tracked range ${atm - STRIKE_TRACK_RANGE*STRIKE_INTERVALS[sym]}-${atm + STRIKE_TRACK_RANGE*STRIKE_INTERVALS[sym]}`);
      Object.assign(meta, parseStrikesFromCsv(nseCsv, sym, atm, STRIKE_INTERVALS[sym]));
    });
    if(bseCsv){
      const anchorPrice = atmAnchorPrice('SENSEX');
      const anchorSource = (preMarketClose && preMarketClose.SENSEX != null) ? 'pre-market close' : 'live LTP';
      const atm = Math.round(anchorPrice / STRIKE_INTERVALS.SENSEX) * STRIKE_INTERVALS.SENSEX;
      atmLog.push(`SENSEX: anchor=${anchorPrice} (${anchorSource}) -> ATM=${atm}, tracked range ${atm - STRIKE_TRACK_RANGE*STRIKE_INTERVALS.SENSEX}-${atm + STRIKE_TRACK_RANGE*STRIKE_INTERVALS.SENSEX}`);
      Object.assign(meta, parseStrikesFromCsv(bseCsv, 'SENSEX', atm, STRIKE_INTERVALS.SENSEX));
    }
    console.log('Multi-strike ATM discovery:\n  ' + atmLog.join('\n  '));

    multiStrikeMeta = meta;
    multiStrikeSymbolList = Object.keys(meta);
    multiStrikeSymbolList.forEach(sym => {
      if(!state[sym]) state[sym] = { open: null, high: null, low: null, ltp: null, volume: null, prevClose: null };
    });

    if(fyersSocket && multiStrikeSymbolList.length > 0){
      fyersSocket.subscribe(multiStrikeSymbolList);
      console.log(`Multi-strike tracking: subscribed to ${multiStrikeSymbolList.length} option symbols (ATM +/-${STRIKE_TRACK_RANGE}) across NIFTY/BANKNIFTY/SENSEX.`);
    }
    multiStrikeSelectedToday = true;
  } catch(err){
    console.log('Multi-strike discovery failed (will retry next minute):', err.message);
  } finally {
    multiStrikeDiscoveryInProgress = false;
  }
}

function updateSecondHalfTracking(symbol, ltp){
  if(!HALF_DAY_SYMBOLS.includes(symbol) && !multiStrikeSymbolList.includes(symbol)) return;
  if(!firstHalfLockedFlag || secondHalfLockedFlag) return;
  if(!secondHalfRunning[symbol]){
    secondHalfRunning[symbol] = { high: ltp, low: ltp };
  } else {
    if(ltp > secondHalfRunning[symbol].high) secondHalfRunning[symbol].high = ltp;
    if(ltp < secondHalfRunning[symbol].low) secondHalfRunning[symbol].low = ltp;
  }
}


let earlyExhaustionResults = null;
let earlyExhaustionScanDone = false;
let earlyExhaustionScanTimestamp = null;
let earlyExhaustionDateKey = null;

// 2026-08-24 fix: same class of bug as checkAndLockPreMarketClose - this
// used to lock permanently the instant minutes passed FIRST_5MIN_LOCK_MINUTES,
// even if the Fyers connection hadn't had a chance to establish yet after a
// restart. Now waits for at least one symbol to have real data, or gives up
// gracefully at a hard cutoff a few minutes later.
function checkAndLockFirst5MinCandle(){
  const { dateKey, minutes } = getISTDateKeyAndMinutes();
  if(first5MinDateKey !== dateKey){
    first5MinDateKey = dateKey;
    first5MinLockedFlag = false;
    first5MinLocked = {};
  }
  if(first5MinLockedFlag || minutes < FIRST_5MIN_LOCK_MINUTES) return;

  const captured = {};
  Object.keys(state).forEach(symbol => {
    const s = state[symbol];
    if(s.high !== null && s.low !== null && s.ltp !== null && s.open !== null) captured[symbol] = { open: s.open, high: s.high, low: s.low, close: s.ltp };
  });
  const gotAnyData = Object.keys(captured).length > 0;
  const pastHardCutoff = minutes >= FIRST_5MIN_LOCK_HARD_CUTOFF_MINUTES;

  if(gotAnyData || pastHardCutoff){
    first5MinLocked = captured;
    first5MinLockedFlag = true;
    if(gotAnyData){
      console.log(`First-5-min candle locked for ${Object.keys(first5MinLocked).length} symbols.`);
    } else {
      console.log(`First-5-min candle: no symbol had live data by the hard cutoff — giving up for today (likely a restart well after market open).`);
    }
    saveFirst5MinLocked();
  }
  // else: keep retrying next cycle - the connection may still be establishing
}

// Same exact pattern as checkAndLockFirst5MinCandle — state[symbol].high/low
// are cumulative from market open (9:15) already, so locking at 9:30 instead
// of 9:20 naturally captures the true 9:15-9:30 range, no separate candle
// tracking needed.
// Same fix as checkAndLockFirst5MinCandle above (2026-08-24) - waits for
// real data or a hard cutoff, instead of locking permanently and instantly
// with nothing on a late restart.
function checkAndLockFirst15MinCandle(){
  const { dateKey, minutes } = getISTDateKeyAndMinutes();
  if(first15MinDateKey !== dateKey){
    first15MinDateKey = dateKey;
    first15MinLockedFlag = false;
    first15MinLocked = {};
  }
  if(first15MinLockedFlag || minutes < FIRST_15MIN_LOCK_MINUTES) return;

  const captured = {};
  Object.keys(state).forEach(symbol => {
    const s = state[symbol];
    if(s.high !== null && s.low !== null && s.ltp !== null && s.open !== null) captured[symbol] = { open: s.open, high: s.high, low: s.low, close: s.ltp };
  });
  const gotAnyData = Object.keys(captured).length > 0;
  const pastHardCutoff = minutes >= FIRST_15MIN_LOCK_HARD_CUTOFF_MINUTES;

  if(gotAnyData || pastHardCutoff){
    first15MinLocked = captured;
    first15MinLockedFlag = true;
    if(gotAnyData){
      console.log(`First-15-min candle locked for ${Object.keys(first15MinLocked).length} symbols.`);
    } else {
      console.log(`First-15-min candle: no symbol had live data by the hard cutoff — giving up for today (likely a restart well after market open).`);
    }
  }
  // else: keep retrying next cycle - the connection may still be establishing
}

function checkAndSaveEODSnapshot(){
  const { dateKey, minutes } = getISTDateKeyAndMinutes();
  if(eodSnapshotDateKey !== dateKey){
    eodSnapshotDateKey = dateKey;
    eodSnapshotSavedToday = false;
  }
  if(!eodSnapshotSavedToday && minutes >= EOD_SNAPSHOT_MINUTES){
    let count = 0;
    Object.keys(state).forEach(symbol => {
      const s = state[symbol];
      const locked = first5MinLocked[symbol];
      if(locked && s.high !== null && s.low !== null){
        yesterdaySnapshot[symbol] = { first5MinHigh: locked.high, first5MinLow: locked.low, dayHigh: s.high, dayLow: s.low };
        count++;
      }
    });
    eodSnapshotSavedToday = true;
    console.log(`End-of-day snapshot saved for ${count} symbols — will be tomorrow's "yesterday" data.`);
    saveYesterdaySnapshot();
  }
}

function checkAndLockFirstHalf(){
  const { dateKey, minutes } = getISTDateKeyAndMinutes();
  if(halfDayDateKey !== dateKey){
    if(halfDayDateKey !== null){
      HALF_DAY_SYMBOLS.forEach(symbol => {
        if(firstHalfLocked[symbol] || secondHalfLocked[symbol]){
          yesterdayHalves[symbol] = {
            firstHalf: firstHalfLocked[symbol] || (yesterdayHalves[symbol] && yesterdayHalves[symbol].firstHalf) || null,
            secondHalf: secondHalfLocked[symbol] || (yesterdayHalves[symbol] && yesterdayHalves[symbol].secondHalf) || null,
          };
        }
      });
      rollMultiStrikeIntoYesterday();
      saveYesterdayHalves();
      saveYesterdayMultiStrikeHalves();
      multiStrikeSelectedToday = false;
      multiStrikeMeta = {};
      multiStrikeSymbolList = [];
    }
    halfDayDateKey = dateKey;
    firstHalfLockedFlag = false;
    secondHalfLockedFlag = false;
    firstHalfLocked = {};
    secondHalfLocked = {};
    secondHalfRunning = {};
    secondHalfOpen = {};
  }
  if(!firstHalfLockedFlag && minutes >= FIRST_HALF_LOCK_MINUTES){
    const allSymbols = [...HALF_DAY_SYMBOLS, ...multiStrikeSymbolList];
    allSymbols.forEach(symbol => {
      const s = state[symbol];
      if(s && s.open !== null && s.high !== null && s.low !== null && s.ltp !== null){
        firstHalfLocked[symbol] = { open: s.open, high: s.high, low: s.low, close: s.ltp };
        secondHalfOpen[symbol] = s.ltp;
        secondHalfRunning[symbol] = { high: s.ltp, low: s.ltp };
      }
    });
    firstHalfLockedFlag = true;
    console.log(`First-half (9:15-12:30) locked for ${Object.keys(firstHalfLocked).length} symbol(s) (indices + ${multiStrikeSymbolList.length} tracked strikes).`);
  }
}

function rollMultiStrikeIntoYesterday(){
  multiStrikeSymbolList.forEach(symbol => {
    const meta = multiStrikeMeta[symbol];
    if(!meta) return;
    if(firstHalfLocked[symbol] || secondHalfLocked[symbol]){
      const key = `${meta.index}_${meta.relativePos}_${meta.type}`;
      yesterdayMultiStrikeHalves[key] = {
        firstHalf: firstHalfLocked[symbol] || (yesterdayMultiStrikeHalves[key] && yesterdayMultiStrikeHalves[key].firstHalf) || null,
        secondHalf: secondHalfLocked[symbol] || (yesterdayMultiStrikeHalves[key] && yesterdayMultiStrikeHalves[key].secondHalf) || null,
      };
    }
  });
}

function checkAndLockSecondHalf(){
  const { minutes } = getISTDateKeyAndMinutes();
  if(!firstHalfLockedFlag || secondHalfLockedFlag) return;
  if(minutes >= EOD_SNAPSHOT_MINUTES){
    const allSymbols = [...HALF_DAY_SYMBOLS, ...multiStrikeSymbolList];
    allSymbols.forEach(symbol => {
      const s = state[symbol];
      const running = secondHalfRunning[symbol];
      const openPrice = secondHalfOpen[symbol];
      if(s && running && openPrice !== undefined && s.ltp !== null){
        secondHalfLocked[symbol] = { open: openPrice, high: running.high, low: running.low, close: s.ltp };
      }
    });
    secondHalfLockedFlag = true;
    console.log(`Second-half (12:30-3:30) locked for ${Object.keys(secondHalfLocked).length} symbol(s).`);
    HALF_DAY_SYMBOLS.forEach(symbol => {
      if(firstHalfLocked[symbol] || secondHalfLocked[symbol]){
        yesterdayHalves[symbol] = {
          firstHalf: firstHalfLocked[symbol] || (yesterdayHalves[symbol] && yesterdayHalves[symbol].firstHalf) || null,
          secondHalf: secondHalfLocked[symbol] || (yesterdayHalves[symbol] && yesterdayHalves[symbol].secondHalf) || null,
        };
      }
    });
    rollMultiStrikeIntoYesterday();
    saveYesterdayHalves();
    saveYesterdayMultiStrikeHalves();
  }
}

function checkAndRunEarlyExhaustionScan(){
  const { dateKey, minutes } = getISTDateKeyAndMinutes();
  if(earlyExhaustionDateKey !== dateKey){
    earlyExhaustionDateKey = dateKey;
    earlyExhaustionScanDone = false;
    earlyExhaustionResults = null;
    earlyExhaustionScanTimestamp = null;
  }
  if(!earlyExhaustionScanDone && minutes >= SCREENER_SCAN_TIME_MINUTES){
    const matches = [];
    Object.keys(first5MinLocked).forEach(symbol => {
      const today = first5MinLocked[symbol];
      const s = state[symbol];
      const yest = yesterdaySnapshot[symbol];
      if(!yest || !s || s.high === null) return;

      const yesterdayEarlyHighWasDayHigh = Math.abs(yest.first5MinHigh - yest.dayHigh) <= EPS;
      const todayEarlyHighIsStillTodaysHigh = Math.abs(today.high - s.high) <= EPS;
      const todayClosedBelowYesterdayLow = today.close < yest.dayLow;

      if(yesterdayEarlyHighWasDayHigh && todayEarlyHighIsStillTodaysHigh && todayClosedBelowYesterdayLow){
        matches.push({ symbol, first5MinHigh: today.high, first5MinClose: today.close, yesterdayLow: yest.dayLow, ltp: s.ltp });
      }
    });
    earlyExhaustionResults = matches;
    earlyExhaustionScanDone = true;
    earlyExhaustionScanTimestamp = timeLabel();
    console.log(`Early Exhaustion Breakdown scan locked at ${earlyExhaustionScanTimestamp} — ${matches.length} matches.`);
    saveEarlyExhaustionResults();
  }
}

function buildEarlyExhaustionRows(){
  if(!earlyExhaustionResults) return [];
  return earlyExhaustionResults.map(r => ({
    ...r,
    ltp: (state[r.symbol] && state[r.symbol].ltp !== null) ? state[r.symbol].ltp : r.ltp,
    matchedAt: earlyExhaustionScanTimestamp,
  }));
}

let earlyBottomResults = null;
let earlyBottomScanDone = false;
let earlyBottomScanTimestamp = null;
let earlyBottomDateKey = null;

function checkAndRunEarlyBottomScan(){
  const { dateKey, minutes } = getISTDateKeyAndMinutes();
  if(earlyBottomDateKey !== dateKey){
    earlyBottomDateKey = dateKey;
    earlyBottomScanDone = false;
    earlyBottomResults = null;
    earlyBottomScanTimestamp = null;
  }
  if(!earlyBottomScanDone && minutes >= SCREENER_SCAN_TIME_MINUTES){
    const matches = [];
    Object.keys(first5MinLocked).forEach(symbol => {
      const today = first5MinLocked[symbol];
      const s = state[symbol];
      const yest = yesterdaySnapshot[symbol];
      if(!yest || !s || s.low === null || yest.first5MinLow === undefined) return;

      const yesterdayEarlyLowWasDayLow = Math.abs(yest.first5MinLow - yest.dayLow) <= EPS;
      const todayEarlyLowIsStillTodaysLow = Math.abs(today.low - s.low) <= EPS;
      const todayClosedAboveYesterdayHigh = today.close > yest.dayHigh;

      if(yesterdayEarlyLowWasDayLow && todayEarlyLowIsStillTodaysLow && todayClosedAboveYesterdayHigh){
        matches.push({ symbol, first5MinLow: today.low, first5MinClose: today.close, yesterdayHigh: yest.dayHigh, ltp: s.ltp });
      }
    });
    earlyBottomResults = matches;
    earlyBottomScanDone = true;
    earlyBottomScanTimestamp = timeLabel();
    console.log(`Early Bottom Breakout scan locked at ${earlyBottomScanTimestamp} — ${matches.length} matches.`);
    saveEarlyBottomResults();
  }
}

function buildEarlyBottomRows(){
  if(!earlyBottomResults) return [];
  return earlyBottomResults.map(r => ({
    ...r,
    ltp: (state[r.symbol] && state[r.symbol].ltp !== null) ? state[r.symbol].ltp : r.ltp,
    matchedAt: earlyBottomScanTimestamp,
  }));
}

function computeCamarilla(h, l, c){
  const rng = h - l;
  return {
    r4: c + rng * 1.1 / 2,
    r3: c + rng * 1.1 / 4,
    s3: c - rng * 1.1 / 4,
    s4: c - rng * 1.1 / 2,
  };
}

let camarillaBuyResults = null;
let camarillaSellResults = null;
let camarillaScanDone = false;
let camarillaScanTimestamp = null;
let camarillaDateKey = null;

function checkAndRunCamarillaScan(){
  const { dateKey, minutes } = getISTDateKeyAndMinutes();
  if(camarillaDateKey !== dateKey){
    camarillaDateKey = dateKey;
    camarillaScanDone = false;
    camarillaBuyResults = null;
    camarillaSellResults = null;
    camarillaScanTimestamp = null;
  }
  if(!camarillaScanDone && minutes >= SCREENER_SCAN_TIME_MINUTES){
    const buys = [], sells = [];
    Object.keys(first5MinLocked).forEach(symbol => {
      const today = first5MinLocked[symbol];
      const s = state[symbol];
      const yest = yesterdaySnapshot[symbol];
      if(!yest || !s || s.prevClose === null) return;

      const cam = computeCamarilla(yest.dayHigh, yest.dayLow, s.prevClose);
      if(today.close > cam.r4){
        buys.push({ symbol, first5MinClose: today.close, r4: cam.r4, ltp: s.ltp });
      } else if(today.close < cam.s4){
        sells.push({ symbol, first5MinClose: today.close, s4: cam.s4, ltp: s.ltp });
      }
    });
    camarillaBuyResults = buys;
    camarillaSellResults = sells;
    camarillaScanDone = true;
    camarillaScanTimestamp = timeLabel();
    console.log(`Camarilla R4/S4 scan locked at ${camarillaScanTimestamp} — ${buys.length} buy, ${sells.length} sell matches.`);
    saveCamarillaResults();
  }
}

function buildCamarillaBuyRows(){
  if(!camarillaBuyResults) return [];
  return camarillaBuyResults.map(r => ({
    ...r,
    ltp: (state[r.symbol] && state[r.symbol].ltp !== null) ? state[r.symbol].ltp : r.ltp,
    matchedAt: camarillaScanTimestamp,
  }));
}

function buildCamarillaSellRows(){
  if(!camarillaSellResults) return [];
  return camarillaSellResults.map(r => ({
    ...r,
    ltp: (state[r.symbol] && state[r.symbol].ltp !== null) ? state[r.symbol].ltp : r.ltp,
    matchedAt: camarillaScanTimestamp,
  }));
}

function computeCPR(h, l, c){
  const pp = (h + l + c) / 3;
  const bc = (h + l) / 2;
  const tc = 2 * pp - bc;
  const widthPct = pp !== 0 ? Math.abs(tc - bc) / pp * 100 : null;
  return { pp, bc, tc, widthPct };
}

let narrowCprTolerancePct = 0.5;
let narrowCprResults = null;
let narrowCprScanDone = false;
let narrowCprScanTimestamp = null;
let narrowCprDateKey = null;

function checkAndRunNarrowCprScan(){
  const { dateKey, minutes } = getISTDateKeyAndMinutes();
  if(narrowCprDateKey !== dateKey){
    narrowCprDateKey = dateKey;
    narrowCprScanDone = false;
    narrowCprResults = null;
    narrowCprScanTimestamp = null;
  }
  if(!narrowCprScanDone && minutes >= SCREENER_SCAN_TIME_MINUTES){
    const matches = [];
    Object.keys(first5MinLocked).forEach(symbol => {
      const yest = yesterdaySnapshot[symbol];
      const today = first5MinLocked[symbol];
      const s = state[symbol];
      if(!yest || !s || s.prevClose === null) return;
      const cpr = computeCPR(yest.dayHigh, yest.dayLow, s.prevClose);
      if(cpr.widthPct !== null && cpr.widthPct <= narrowCprTolerancePct){
        const direction = today.close > cpr.pp ? 'buy' : 'sell';
        matches.push({ symbol, widthPct: cpr.widthPct, pp: cpr.pp, tc: cpr.tc, bc: cpr.bc, direction, ltp: s.ltp });
      }
    });
    narrowCprResults = matches;
    narrowCprScanDone = true;
    narrowCprScanTimestamp = timeLabel();
    console.log(`Narrow CPR scan locked at ${narrowCprScanTimestamp} — ${matches.length} matches at ${narrowCprTolerancePct}% cutoff.`);
    saveNarrowCprResults();
  }
}

function buildNarrowCprRows(){
  if(!narrowCprResults) return [];
  return narrowCprResults.map(r => ({
    ...r,
    ltp: (state[r.symbol] && state[r.symbol].ltp !== null) ? state[r.symbol].ltp : r.ltp,
    matchedAt: narrowCprScanTimestamp,
  }));
}

function computeNarrowCamarillaRange(h, l, c){
  const rangePct = c !== 0 ? Math.abs(h - l) / c * 100 : null;
  return { rangePct };
}

let narrowCamarillaTolerancePct = 1.0;
let narrowCamarillaResults = null;
let narrowCamarillaScanDone = false;
let narrowCamarillaScanTimestamp = null;
let narrowCamarillaDateKey = null;

function checkAndRunNarrowCamarillaScan(){
  const { dateKey, minutes } = getISTDateKeyAndMinutes();
  if(narrowCamarillaDateKey !== dateKey){
    narrowCamarillaDateKey = dateKey;
    narrowCamarillaScanDone = false;
    narrowCamarillaResults = null;
    narrowCamarillaScanTimestamp = null;
  }
  if(!narrowCamarillaScanDone && minutes >= SCREENER_SCAN_TIME_MINUTES){
    const matches = [];
    Object.keys(first5MinLocked).forEach(symbol => {
      const yest = yesterdaySnapshot[symbol];
      const today = first5MinLocked[symbol];
      const s = state[symbol];
      if(!yest || !s || s.prevClose === null) return;
      const { rangePct } = computeNarrowCamarillaRange(yest.dayHigh, yest.dayLow, s.prevClose);
      if(rangePct !== null && rangePct <= narrowCamarillaTolerancePct){
        const cam = computeCamarilla(yest.dayHigh, yest.dayLow, s.prevClose);
        const pp = (yest.dayHigh + yest.dayLow + s.prevClose) / 3;
        const direction = today.close > pp ? 'buy' : 'sell';
        matches.push({ symbol, rangePct, r4: cam.r4, s4: cam.s4, pp, direction, ltp: s.ltp });
      }
    });
    narrowCamarillaResults = matches;
    narrowCamarillaScanDone = true;
    narrowCamarillaScanTimestamp = timeLabel();
    console.log(`Narrow Camarilla scan locked at ${narrowCamarillaScanTimestamp} — ${matches.length} matches at ${narrowCamarillaTolerancePct}% cutoff.`);
    saveNarrowCamarillaResults();
  }
}

function buildNarrowCamarillaRows(){
  if(!narrowCamarillaResults) return [];
  return narrowCamarillaResults.map(r => ({
    ...r,
    ltp: (state[r.symbol] && state[r.symbol].ltp !== null) ? state[r.symbol].ltp : r.ltp,
    matchedAt: narrowCamarillaScanTimestamp,
  }));
}

function computeScreeners() {
  const openEqLow = buildLockedScreenerRows('openlow');
  const openEqHigh = buildLockedScreenerRows('openhigh');
  const gapNeutral = buildLockedScreenerRows('gapneutral');
  const openEqHighSimple = buildLockedScreenerRows('openhighsimple');
  const openEqLowYestLow = buildLockedScreenerRows('openlowyestlow');
  const openEqLowSimple = buildLockedScreenerRows('openlowsimple');
  const openEqLow15m = buildLockedScreener15mRows('openlow');
  const openEqHigh15m = buildLockedScreener15mRows('openhigh');
  const openEqHighSimple15m = buildLockedScreener15mRows('openhighsimple');
  const openEqLowYestLow15m = buildLockedScreener15mRows('openlowyestlow');
  const openEqLowSimple15m = buildLockedScreener15mRows('openlowsimple');

  const withVolume = Object.entries(state).filter(([, s]) => s.volume !== null).map(([symbol, s]) => ({ symbol, volume: s.volume, ltp: s.ltp }));
  withVolume.sort((a, b) => b.volume - a.volume);
  const topCount = Math.max(1, Math.ceil(withVolume.length * 0.05));
  const volumeShockers = withVolume.slice(0, topCount);
  return {
    openEqLow, openEqHigh, gapNeutral, openEqHighSimple, openEqLowYestLow, openEqLowSimple,
    openEqLow15m, openEqHigh15m, openEqHighSimple15m, openEqLowYestLow15m, openEqLowSimple15m,
    volumeShockers, updatedAt: new Date().toISOString(), isLive, lastTickReceivedAt,
  };
}

const PERSIST_DIR = process.env.RAILWAY_VOLUME_MOUNT_PATH || '/data';
const PERSIST_FILE = path.join(PERSIST_DIR, 'slot_history.json');

let slotHistory = { openlow: [], openhigh: [], gapneutral: [], orb5up: [], orb5down: [], orb15up: [], orb15down: [] };
let alreadySeen = { openlow: new Set(), openhigh: new Set(), gapneutral: new Set(), orb5up: new Set(), orb5down: new Set(), orb15up: new Set(), orb15down: new Set() };

function todayDateKey(){
  return getISTDateKeyAndMinutes().dateKey;
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
      if(!slotHistory[key]) slotHistory[key] = [];
    });
    console.log('Restored slot history from disk — survived the restart/redeploy.');
  } catch(err){
    console.log('Could not load persisted history (this is fine if no volume is mounted yet):', err.message);
  }
}

function savePersistedHistory(){
  try{
    if(!fs.existsSync(PERSIST_DIR)) return;
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

const SCREENER_SCAN_PERSIST_FILE = path.join(PERSIST_DIR, 'screener_scan.json');
const BTST_LOCK_PERSIST_FILE = path.join(PERSIST_DIR, 'btst_lock.json');

function loadBtstLock(){
  try{
    if(!fs.existsSync(BTST_LOCK_PERSIST_FILE)) {
      console.log('No persisted BTST lock found — will lock fresh today at 3:10 PM.');
      return;
    }
    const saved = JSON.parse(fs.readFileSync(BTST_LOCK_PERSIST_FILE, 'utf8'));
    if(saved.date !== todayDateKey()){
      console.log('Persisted BTST lock is from a previous day — will lock fresh today.');
      return;
    }
    btstLockedRows = saved.btstLockedRows;
    btstLockDone = saved.btstLockDone;
    btstLockDateKey = saved.date;
    btstLockTimestamp = saved.btstLockTimestamp;
    console.log(`Restored today's BTST lock from disk (locked at ${btstLockTimestamp}) — survived the restart/redeploy.`);
  } catch(err){
    console.log('Could not load persisted BTST lock (this is fine if no volume is mounted yet):', err.message);
  }
}

function saveBtstLock(){
  try{
    if(!fs.existsSync(PERSIST_DIR)) return;
    const toSave = { date: todayDateKey(), btstLockedRows, btstLockDone, btstLockTimestamp };
    fs.writeFileSync(BTST_LOCK_PERSIST_FILE, JSON.stringify(toSave));
  } catch(err){
    console.log('Could not save BTST lock to disk (this is fine if no volume is mounted):', err.message);
  }
}

loadBtstLock();

const NARROW_CPR_LOCK_PERSIST_FILE = path.join(PERSIST_DIR, 'narrow_cpr_lock.json');

function loadNarrowCprLock(){
  try{
    if(!fs.existsSync(NARROW_CPR_LOCK_PERSIST_FILE)) {
      console.log('No persisted Narrow CPR lock found — will lock fresh today at 3:30 PM.');
      return;
    }
    const saved = JSON.parse(fs.readFileSync(NARROW_CPR_LOCK_PERSIST_FILE, 'utf8'));
    if(saved.date !== todayDateKey()){
      console.log('Persisted Narrow CPR lock is from a previous day — will lock fresh today.');
      return;
    }
    narrowCprLockedRows = saved.narrowCprLockedRows;
    narrowCprLockDone = saved.narrowCprLockDone;
    narrowCprLockDateKey = saved.date;
    narrowCprLockTimestamp = saved.narrowCprLockTimestamp;
    console.log(`Restored today's Narrow CPR lock from disk (locked at ${narrowCprLockTimestamp}) — survived the restart/redeploy.`);
  } catch(err){
    console.log('Could not load persisted Narrow CPR lock (this is fine if no volume is mounted yet):', err.message);
  }
}

function saveNarrowCprLock(){
  try{
    if(!fs.existsSync(PERSIST_DIR)) return;
    const toSave = { date: todayDateKey(), narrowCprLockedRows, narrowCprLockDone, narrowCprLockTimestamp };
    fs.writeFileSync(NARROW_CPR_LOCK_PERSIST_FILE, JSON.stringify(toSave));
  } catch(err){
    console.log('Could not save Narrow CPR lock to disk (this is fine if no volume is mounted):', err.message);
  }
}

loadNarrowCprLock();

const NARROW_CAMARILLA_LOCK_PERSIST_FILE = path.join(PERSIST_DIR, 'narrow_camarilla_lock.json');

function loadNarrowCamarillaLock(){
  try{
    if(!fs.existsSync(NARROW_CAMARILLA_LOCK_PERSIST_FILE)) {
      console.log('No persisted Narrow Camarilla lock found — will lock fresh today at 3:30 PM.');
      return;
    }
    const saved = JSON.parse(fs.readFileSync(NARROW_CAMARILLA_LOCK_PERSIST_FILE, 'utf8'));
    if(saved.date !== todayDateKey()){
      console.log('Persisted Narrow Camarilla lock is from a previous day — will lock fresh today.');
      return;
    }
    narrowCamarillaLockedRows = saved.narrowCamarillaLockedRows;
    narrowCamarillaLockDone = saved.narrowCamarillaLockDone;
    narrowCamarillaLockDateKey = saved.date;
    narrowCamarillaLockTimestamp = saved.narrowCamarillaLockTimestamp;
    console.log(`Restored today's Narrow Camarilla lock from disk (locked at ${narrowCamarillaLockTimestamp}) — survived the restart/redeploy.`);
  } catch(err){
    console.log('Could not load persisted Narrow Camarilla lock (this is fine if no volume is mounted yet):', err.message);
  }
}

function saveNarrowCamarillaLock(){
  try{
    if(!fs.existsSync(PERSIST_DIR)) return;
    const toSave = { date: todayDateKey(), narrowCamarillaLockedRows, narrowCamarillaLockDone, narrowCamarillaLockTimestamp };
    fs.writeFileSync(NARROW_CAMARILLA_LOCK_PERSIST_FILE, JSON.stringify(toSave));
  } catch(err){
    console.log('Could not save Narrow Camarilla lock to disk (this is fine if no volume is mounted):', err.message);
  }
}

loadNarrowCamarillaLock();

const TOP3_LOSERS_916_PERSIST_FILE = path.join(PERSIST_DIR, 'top3_losers_916_lock.json');

function loadTop3Losers916Lock(){
  try{
    if(!fs.existsSync(TOP3_LOSERS_916_PERSIST_FILE)) {
      console.log('No persisted Top-3-Losers-at-9:16 lock found — will lock fresh today at 9:16 AM.');
      return;
    }
    const saved = JSON.parse(fs.readFileSync(TOP3_LOSERS_916_PERSIST_FILE, 'utf8'));
    if(saved.date !== todayDateKey()){
      console.log('Persisted Top-3-Losers-at-9:16 lock is from a previous day — will lock fresh today.');
      return;
    }
    top3Losers916Locked = saved.top3Losers916Locked;
    top3Losers916LockedFlag = saved.top3Losers916LockedFlag;
    top3Losers916DateKey = saved.date;
    console.log(`Restored today's Top-3-Losers-at-9:16 lock from disk — survived the restart/redeploy.`);
  } catch(err){
    console.log('Could not load persisted Top-3-Losers-at-9:16 lock (this is fine if no volume is mounted yet):', err.message);
  }
}

function saveTop3Losers916Lock(){
  try{
    if(!fs.existsSync(PERSIST_DIR)) return;
    const toSave = { date: todayDateKey(), top3Losers916Locked, top3Losers916LockedFlag };
    fs.writeFileSync(TOP3_LOSERS_916_PERSIST_FILE, JSON.stringify(toSave));
  } catch(err){
    console.log('Could not save Top-3-Losers-at-9:16 lock to disk (this is fine if no volume is mounted):', err.message);
  }
}

loadTop3Losers916Lock();

// first5MinLocked previously had NO disk persistence at all — a same-day
// restart after 9:20 AM (e.g. a code redeploy in the afternoon) silently
// wiped today's already-locked first-5-min candle for every symbol, with
// no way to recover it until the following day's fresh 9:20 AM lock. This
// follows the exact same save/restore pattern as screener_scan.json above.
const FIRST5MIN_PERSIST_FILE = path.join(PERSIST_DIR, 'first5min_locked.json');

function loadFirst5MinLocked(){
  try{
    if(!fs.existsSync(FIRST5MIN_PERSIST_FILE)){
      console.log('No persisted first-5-min lock found — will lock fresh today at 9:20 AM.');
      return;
    }
    const saved = JSON.parse(fs.readFileSync(FIRST5MIN_PERSIST_FILE, 'utf8'));
    if(saved.date !== todayDateKey()){
      console.log('Persisted first-5-min lock is from a previous day — will lock fresh today.');
      return;
    }
    first5MinLocked = saved.first5MinLocked;
    first5MinLockedFlag = saved.first5MinLockedFlag;
    console.log(`Restored today's first-5-min candle from disk (${Object.keys(first5MinLocked).length} symbols) — survived the restart/redeploy.`);
  } catch(err){
    console.log('Could not load persisted first-5-min lock (this is fine if no volume is mounted yet):', err.message);
  }
}

function saveFirst5MinLocked(){
  try{
    if(!fs.existsSync(PERSIST_DIR)) return;
    const toSave = { date: todayDateKey(), first5MinLocked, first5MinLockedFlag };
    fs.writeFileSync(FIRST5MIN_PERSIST_FILE, JSON.stringify(toSave));
  } catch(err){
    console.log('Could not save first-5-min lock to disk (this is fine if no volume is mounted):', err.message);
  }
}

loadFirst5MinLocked();

function loadScreenerScanResults(){
  try{
    if(!fs.existsSync(SCREENER_SCAN_PERSIST_FILE)) {
      console.log('No persisted screener scan found — will run fresh today.');
      return;
    }
    const saved = JSON.parse(fs.readFileSync(SCREENER_SCAN_PERSIST_FILE, 'utf8'));
    if(saved.date !== todayDateKey()){
      console.log('Persisted screener scan is from a previous day — will run fresh today.');
      return;
    }
    screenerScanResults = saved.screenerScanResults;
    screenerScanDone = saved.screenerScanDone;
    screenerScanDateKey = saved.date;
    screenerScanTimestamp = saved.screenerScanTimestamp;
    console.log(`Restored today's screener scan from disk (locked at ${screenerScanTimestamp}) — survived the restart/redeploy.`);
  } catch(err){
    console.log('Could not load persisted screener scan (this is fine if no volume is mounted yet):', err.message);
  }
}

function saveScreenerScanResults(){
  try{
    if(!fs.existsSync(PERSIST_DIR)) return;
    const toSave = { date: todayDateKey(), screenerScanResults, screenerScanDone, screenerScanTimestamp };
    fs.writeFileSync(SCREENER_SCAN_PERSIST_FILE, JSON.stringify(toSave));
  } catch(err){
    console.log('Could not save screener scan to disk (this is fine if no volume is mounted):', err.message);
  }
}

loadScreenerScanResults();

const SCREENER_SCAN_15M_PERSIST_FILE = path.join(PERSIST_DIR, 'screener_scan_15m.json');

function loadScreenerScan15mResults(){
  try{
    if(!fs.existsSync(SCREENER_SCAN_15M_PERSIST_FILE)) {
      console.log('No persisted 15-min screener scan found — will run fresh today.');
      return;
    }
    const saved = JSON.parse(fs.readFileSync(SCREENER_SCAN_15M_PERSIST_FILE, 'utf8'));
    if(saved.date !== todayDateKey()){
      console.log('Persisted 15-min screener scan is from a previous day — will run fresh today.');
      return;
    }
    screenerScan15mResults = saved.screenerScan15mResults;
    screenerScan15mDone = saved.screenerScan15mDone;
    screenerScan15mDateKey = saved.date;
    screenerScan15mTimestamp = saved.screenerScan15mTimestamp;
    console.log(`Restored today's 15-min screener scan from disk (locked at ${screenerScan15mTimestamp}) — survived the restart/redeploy.`);
  } catch(err){
    console.log('Could not load persisted 15-min screener scan (this is fine if no volume is mounted yet):', err.message);
  }
}

function saveScreenerScan15mResults(){
  try{
    if(!fs.existsSync(PERSIST_DIR)) return;
    const toSave = { date: todayDateKey(), screenerScan15mResults, screenerScan15mDone, screenerScan15mTimestamp };
    fs.writeFileSync(SCREENER_SCAN_15M_PERSIST_FILE, JSON.stringify(toSave));
  } catch(err){
    console.log('Could not save 15-min screener scan to disk (this is fine if no volume is mounted):', err.message);
  }
}

loadScreenerScan15mResults();

const YESTERDAY_SNAPSHOT_FILE = path.join(PERSIST_DIR, 'yesterday_snapshot.json');
const EARLY_EXHAUSTION_PERSIST_FILE = path.join(PERSIST_DIR, 'early_exhaustion_scan.json');

function loadYesterdaySnapshot(){
  try{
    if(!fs.existsSync(YESTERDAY_SNAPSHOT_FILE)) {
      console.log('No saved "yesterday" snapshot found yet — Early Exhaustion Breakdown will show no matches until one full trading day has been captured (at 3:30 PM).');
      return;
    }
    const saved = JSON.parse(fs.readFileSync(YESTERDAY_SNAPSHOT_FILE, 'utf8'));
    const ageDays = (new Date(todayDateKey()) - new Date(saved.date)) / (1000*60*60*24);
    if(ageDays > 5){
      console.log(`Saved snapshot is from ${saved.date}, ${Math.round(ageDays)} days ago — too stale to trust as "yesterday", ignoring it.`);
      return;
    }
    yesterdaySnapshot = saved.yesterdaySnapshot;
    console.log(`Restored "yesterday" snapshot from disk, dated ${saved.date} (${Object.keys(yesterdaySnapshot).length} symbols) — survived the restart/redeploy.`);
  } catch(err){
    console.log('Could not load yesterday snapshot (this is fine if no volume is mounted yet):', err.message);
  }
}

function saveYesterdaySnapshot(){
  try{
    if(!fs.existsSync(PERSIST_DIR)) return;
    fs.writeFileSync(YESTERDAY_SNAPSHOT_FILE, JSON.stringify({ date: todayDateKey(), yesterdaySnapshot }));
  } catch(err){
    console.log('Could not save yesterday snapshot to disk (this is fine if no volume is mounted):', err.message);
  }
}

const YESTERDAY_HALVES_FILE = path.join(PERSIST_DIR, 'yesterday_halves.json');

function loadYesterdayHalves(){
  try{
    if(!fs.existsSync(YESTERDAY_HALVES_FILE)){
      console.log('No saved half-day snapshot found yet — First/Second Half panels will show no data until one full trading day has been captured.');
      return;
    }
    const saved = JSON.parse(fs.readFileSync(YESTERDAY_HALVES_FILE, 'utf8'));
    const ageDays = (new Date(todayDateKey()) - new Date(saved.date)) / (1000*60*60*24);
    if(ageDays > 5){
      console.log(`Saved half-day snapshot is from ${saved.date}, ${Math.round(ageDays)} days ago — too stale, ignoring it.`);
      return;
    }
    yesterdayHalves = saved.yesterdayHalves;
    console.log(`Restored half-day snapshot from disk, dated ${saved.date} — survived the restart/redeploy.`);
  } catch(err){
    console.log('Could not load half-day snapshot (this is fine if no volume is mounted yet):', err.message);
  }
}

function saveYesterdayHalves(){
  try{
    if(!fs.existsSync(PERSIST_DIR)) return;
    fs.writeFileSync(YESTERDAY_HALVES_FILE, JSON.stringify({ date: todayDateKey(), yesterdayHalves }));
  } catch(err){
    console.log('Could not save half-day snapshot to disk (this is fine if no volume is mounted):', err.message);
  }
}

const YESTERDAY_MULTI_STRIKE_HALVES_FILE = path.join(PERSIST_DIR, 'yesterday_multistrike_halves.json');

function loadYesterdayMultiStrikeHalves(){
  try{
    if(!fs.existsSync(YESTERDAY_MULTI_STRIKE_HALVES_FILE)){
      console.log('No saved multi-strike half-day snapshot found yet.');
      return;
    }
    const saved = JSON.parse(fs.readFileSync(YESTERDAY_MULTI_STRIKE_HALVES_FILE, 'utf8'));
    const ageDays = (new Date(todayDateKey()) - new Date(saved.date)) / (1000*60*60*24);
    if(ageDays > 5){
      console.log(`Saved multi-strike half-day snapshot is from ${saved.date}, ${Math.round(ageDays)} days ago — too stale, ignoring it.`);
      return;
    }
    yesterdayMultiStrikeHalves = saved.yesterdayMultiStrikeHalves;
    console.log(`Restored multi-strike half-day snapshot from disk, dated ${saved.date} — survived the restart/redeploy.`);
  } catch(err){
    console.log('Could not load multi-strike half-day snapshot (this is fine if no volume is mounted yet):', err.message);
  }
}

function saveYesterdayMultiStrikeHalves(){
  try{
    if(!fs.existsSync(PERSIST_DIR)) return;
    fs.writeFileSync(YESTERDAY_MULTI_STRIKE_HALVES_FILE, JSON.stringify({ date: todayDateKey(), yesterdayMultiStrikeHalves }));
  } catch(err){
    console.log('Could not save multi-strike half-day snapshot to disk (this is fine if no volume is mounted):', err.message);
  }
}

function loadEarlyExhaustionResults(){
  try{
    if(!fs.existsSync(EARLY_EXHAUSTION_PERSIST_FILE)) return;
    const saved = JSON.parse(fs.readFileSync(EARLY_EXHAUSTION_PERSIST_FILE, 'utf8'));
    if(saved.date !== todayDateKey()) return;
    earlyExhaustionResults = saved.earlyExhaustionResults;
    earlyExhaustionScanDone = saved.earlyExhaustionScanDone;
    earlyExhaustionDateKey = saved.date;
    earlyExhaustionScanTimestamp = saved.earlyExhaustionScanTimestamp;
    console.log(`Restored today's Early Exhaustion Breakdown scan from disk (locked at ${earlyExhaustionScanTimestamp}).`);
  } catch(err){
    console.log('Could not load early exhaustion scan (this is fine if no volume is mounted yet):', err.message);
  }
}

function saveEarlyExhaustionResults(){
  try{
    if(!fs.existsSync(PERSIST_DIR)) return;
    const toSave = { date: todayDateKey(), earlyExhaustionResults, earlyExhaustionScanDone, earlyExhaustionScanTimestamp };
    fs.writeFileSync(EARLY_EXHAUSTION_PERSIST_FILE, JSON.stringify(toSave));
  } catch(err){
    console.log('Could not save early exhaustion scan to disk (this is fine if no volume is mounted):', err.message);
  }
}

const EARLY_BOTTOM_PERSIST_FILE = path.join(PERSIST_DIR, 'early_bottom_scan.json');

function loadEarlyBottomResults(){
  try{
    if(!fs.existsSync(EARLY_BOTTOM_PERSIST_FILE)) return;
    const saved = JSON.parse(fs.readFileSync(EARLY_BOTTOM_PERSIST_FILE, 'utf8'));
    if(saved.date !== todayDateKey()) return;
    earlyBottomResults = saved.earlyBottomResults;
    earlyBottomScanDone = saved.earlyBottomScanDone;
    earlyBottomDateKey = saved.date;
    earlyBottomScanTimestamp = saved.earlyBottomScanTimestamp;
    console.log(`Restored today's Early Bottom Breakout scan from disk (locked at ${earlyBottomScanTimestamp}).`);
  } catch(err){
    console.log('Could not load early bottom scan (this is fine if no volume is mounted yet):', err.message);
  }
}

function saveEarlyBottomResults(){
  try{
    if(!fs.existsSync(PERSIST_DIR)) return;
    const toSave = { date: todayDateKey(), earlyBottomResults, earlyBottomScanDone, earlyBottomScanTimestamp };
    fs.writeFileSync(EARLY_BOTTOM_PERSIST_FILE, JSON.stringify(toSave));
  } catch(err){
    console.log('Could not save early bottom scan to disk (this is fine if no volume is mounted):', err.message);
  }
}

const CAMARILLA_PERSIST_FILE = path.join(PERSIST_DIR, 'camarilla_scan.json');

function loadCamarillaResults(){
  try{
    if(!fs.existsSync(CAMARILLA_PERSIST_FILE)) return;
    const saved = JSON.parse(fs.readFileSync(CAMARILLA_PERSIST_FILE, 'utf8'));
    if(saved.date !== todayDateKey()) return;
    camarillaBuyResults = saved.camarillaBuyResults;
    camarillaSellResults = saved.camarillaSellResults;
    camarillaScanDone = saved.camarillaScanDone;
    camarillaDateKey = saved.date;
    camarillaScanTimestamp = saved.camarillaScanTimestamp;
    console.log(`Restored today's Camarilla R4/S4 scan from disk (locked at ${camarillaScanTimestamp}).`);
  } catch(err){
    console.log('Could not load Camarilla scan (this is fine if no volume is mounted yet):', err.message);
  }
}

function saveCamarillaResults(){
  try{
    if(!fs.existsSync(PERSIST_DIR)) return;
    const toSave = { date: todayDateKey(), camarillaBuyResults, camarillaSellResults, camarillaScanDone, camarillaScanTimestamp };
    fs.writeFileSync(CAMARILLA_PERSIST_FILE, JSON.stringify(toSave));
  } catch(err){
    console.log('Could not save Camarilla scan to disk (this is fine if no volume is mounted):', err.message);
  }
}

const NARROW_CPR_PERSIST_FILE = path.join(PERSIST_DIR, 'narrow_cpr_scan.json');

function loadNarrowCprResults(){
  try{
    if(!fs.existsSync(NARROW_CPR_PERSIST_FILE)) return;
    const saved = JSON.parse(fs.readFileSync(NARROW_CPR_PERSIST_FILE, 'utf8'));
    if(saved.date !== todayDateKey()) return;
    narrowCprResults = saved.narrowCprResults;
    narrowCprScanDone = saved.narrowCprScanDone;
    narrowCprDateKey = saved.date;
    narrowCprScanTimestamp = saved.narrowCprScanTimestamp;
    if(saved.narrowCprTolerancePct !== undefined) narrowCprTolerancePct = saved.narrowCprTolerancePct;
    console.log(`Restored today's Narrow CPR scan from disk (locked at ${narrowCprScanTimestamp}).`);
  } catch(err){
    console.log('Could not load Narrow CPR scan (this is fine if no volume is mounted yet):', err.message);
  }
}

function saveNarrowCprResults(){
  try{
    if(!fs.existsSync(PERSIST_DIR)) return;
    const toSave = { date: todayDateKey(), narrowCprResults, narrowCprScanDone, narrowCprScanTimestamp, narrowCprTolerancePct };
    fs.writeFileSync(NARROW_CPR_PERSIST_FILE, JSON.stringify(toSave));
  } catch(err){
    console.log('Could not save Narrow CPR scan to disk (this is fine if no volume is mounted):', err.message);
  }
}

const NARROW_CAMARILLA_PERSIST_FILE = path.join(PERSIST_DIR, 'narrow_camarilla_scan.json');

function loadNarrowCamarillaResults(){
  try{
    if(!fs.existsSync(NARROW_CAMARILLA_PERSIST_FILE)) return;
    const saved = JSON.parse(fs.readFileSync(NARROW_CAMARILLA_PERSIST_FILE, 'utf8'));
    if(saved.date !== todayDateKey()) return;
    narrowCamarillaResults = saved.narrowCamarillaResults;
    narrowCamarillaScanDone = saved.narrowCamarillaScanDone;
    narrowCamarillaDateKey = saved.date;
    narrowCamarillaScanTimestamp = saved.narrowCamarillaScanTimestamp;
    if(saved.narrowCamarillaTolerancePct !== undefined) narrowCamarillaTolerancePct = saved.narrowCamarillaTolerancePct;
    console.log(`Restored today's Narrow Camarilla scan from disk (locked at ${narrowCamarillaScanTimestamp}).`);
  } catch(err){
    console.log('Could not load Narrow Camarilla scan (this is fine if no volume is mounted yet):', err.message);
  }
}

function saveNarrowCamarillaResults(){
  try{
    if(!fs.existsSync(PERSIST_DIR)) return;
    const toSave = { date: todayDateKey(), narrowCamarillaResults, narrowCamarillaScanDone, narrowCamarillaScanTimestamp, narrowCamarillaTolerancePct };
    fs.writeFileSync(NARROW_CAMARILLA_PERSIST_FILE, JSON.stringify(toSave));
  } catch(err){
    console.log('Could not save Narrow Camarilla scan to disk (this is fine if no volume is mounted):', err.message);
  }
}

const ROUND_NUMBER_HISTORY_PERSIST_FILE = path.join(PERSIST_DIR, 'round_number_history.json');

function loadRoundNumberHistory(){
  try{
    if(!fs.existsSync(ROUND_NUMBER_HISTORY_PERSIST_FILE)) return;
    const saved = JSON.parse(fs.readFileSync(ROUND_NUMBER_HISTORY_PERSIST_FILE, 'utf8'));
    if(saved.date !== todayDateKey()) return;
    roundNumberHistory = saved.roundNumberHistory || [];
    lastRoundNumberSnapshotBucket = saved.lastRoundNumberSnapshotBucket !== undefined ? saved.lastRoundNumberSnapshotBucket : null;
    console.log(`Restored Round Number history from disk — ${roundNumberHistory.length} snapshot(s) so far today.`);
  } catch(err){
    console.log('Could not load Round Number history (this is fine if no volume is mounted yet):', err.message);
  }
}

function saveRoundNumberHistory(){
  try{
    if(!fs.existsSync(PERSIST_DIR)) return;
    const toSave = { date: todayDateKey(), roundNumberHistory, lastRoundNumberSnapshotBucket };
    fs.writeFileSync(ROUND_NUMBER_HISTORY_PERSIST_FILE, JSON.stringify(toSave));
  } catch(err){
    console.log('Could not save Round Number history to disk (this is fine if no volume is mounted):', err.message);
  }
}

loadYesterdaySnapshot();
loadEarlyExhaustionResults();
loadEarlyBottomResults();
loadCamarillaResults();
loadNarrowCprResults();
loadNarrowCamarillaResults();
loadRoundNumberHistory();
loadYesterdayHalves();
loadYesterdayMultiStrikeHalves();

function timeLabel(){
  const now = new Date();
  const istMillis = now.getTime() + (5.5 * 60 * 60 * 1000);
  const ist = new Date(istMillis);
  return `${String(ist.getUTCHours()).padStart(2,'0')}:${String(ist.getUTCMinutes()).padStart(2,'0')}`;
}

function getISTDateKeyAndMinutes(){
  const now = new Date();
  const istMillis = now.getTime() + (5.5 * 60 * 60 * 1000);
  const ist = new Date(istMillis);
  const dateKey = `${ist.getUTCFullYear()}-${String(ist.getUTCMonth()+1).padStart(2,'0')}-${String(ist.getUTCDate()).padStart(2,'0')}`;
  const minutes = ist.getUTCHours()*60 + ist.getUTCMinutes();
  return { dateKey, minutes };
}

const orb5Locked = {};
const orb15Locked = {};
let orb5LockedFlag = false;
let orb15LockedFlag = false;
let orbLockedDateKey = null;

function checkAndLockOpeningRanges(){
  const { dateKey, minutes } = getISTDateKeyAndMinutes();

  if(orbLockedDateKey !== dateKey){
    orbLockedDateKey = dateKey;
    orb5LockedFlag = false;
    orb15LockedFlag = false;
    Object.keys(orb5Locked).forEach(k => delete orb5Locked[k]);
    Object.keys(orb15Locked).forEach(k => delete orb15Locked[k]);
  }

  if(!orb5LockedFlag && minutes >= (9*60+25)){
    Object.keys(state).forEach(symbol => {
      const s = state[symbol];
      if(s.high !== null && s.low !== null) orb5Locked[symbol] = { high: s.high, low: s.low };
    });
    orb5LockedFlag = true;
    console.log(`5-min Opening Range locked for ${Object.keys(orb5Locked).length} symbols.`);
  }
  if(!orb15LockedFlag && minutes >= (9*60+35)){
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

let lastKnownDateKey = null;

function recordMinuteSlot(){
  checkAndLockOpeningRanges();
  checkAndRunScreenerScan();
  checkAndRunBtstLock();
  checkAndRunNarrowCprLock();
  checkAndRunNarrowCamarillaLock();
  checkAndLockTop3Losers916();
  checkAndLockFirst5MinCandle();
  checkAndLockFirst15MinCandle();
  checkAndRunScreenerScan15m();
  checkAndSaveEODSnapshot();
  checkAndRunEarlyExhaustionScan();
  checkAndRunEarlyBottomScan();
  checkAndRunCamarillaScan();
  checkAndRunNarrowCprScan();
  checkAndRunNarrowCamarillaScan();
  checkAndRecordRoundNumberSnapshot();
  checkAndLockPreMarketClose();
  checkAndLockFirstHalf();
  discoverAndSubscribeMultiStrikes();
  checkAndLockSecondHalf();

  const currentDateKey = todayDateKey();
  if(lastKnownDateKey !== null && lastKnownDateKey !== currentDateKey){
    console.log(`Trading day changed (${lastKnownDateKey} -> ${currentDateKey}) — resetting slot history for the new day.`);
    Object.keys(slotHistory).forEach(key => { slotHistory[key] = []; });
    Object.keys(alreadySeen).forEach(key => { alreadySeen[key] = new Set(); });
    roundNumberHistory = [];
    lastRoundNumberSnapshotBucket = null;
  }
  lastKnownDateKey = currentDateKey;

  const orb5 = computeOrbBreakouts(5);
  const orb15 = computeOrbBreakouts(15);
  const groups = {
    orb5up: orb5.up, orb5down: orb5.down, orb15up: orb15.up, orb15down: orb15.down
  };
  const label = timeLabel();

  Object.keys(groups).forEach(key => {
    const freshSymbols = groups[key]
      .map(r => r.symbol)
      .filter(sym => !alreadySeen[key].has(sym));
    freshSymbols.forEach(sym => alreadySeen[key].add(sym));
    slotHistory[key].push({ time: label, symbols: freshSymbols });
  });

  savePersistedHistory();
}

let lastRecordedMinute = null;
setInterval(() => {
  try{
    const label = timeLabel();
    if (label !== lastRecordedMinute) {
      console.log(`Minute changed: ${lastRecordedMinute} -> ${label}, recording new slot.`);
      lastRecordedMinute = label;
      recordMinuteSlot();
      broadcastScreeners();
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

  lastConnectionAttemptAt = Date.now();
  const fullToken = `${APP_ID}:${accessToken}`;
  fyersSocket = fyersDataSocket.getInstance(fullToken, __dirname, false);

  if (typeof fyersSocket.removeAllListeners === 'function') {
    fyersSocket.removeAllListeners();
  }

  fyersSocket.on('connect', () => {
    console.log('Connected to Fyers live data feed. Waiting briefly before subscribing (a brand-new token can take a moment to fully activate on Fyers\' side)...');
    setTimeout(() => {
      console.log('Subscribing to', symbols.length, 'symbols...');
      fyersSocket.subscribe(symbols);
      isLive = true;
    }, 6000); // was 2000ms — bumped up since even RECONNECTS (not just brand-new logins) were sometimes hitting a -15 "invalid token" rejection on the first subscribe attempt, suggesting Fyers' side needs a bit longer to fully accept a new WS session than 2s reliably provides
  });

// Fyers requires the FULL index symbol format for subscription
// ("NSE:NIFTY50-INDEX" etc. - bare "NIFTY" is not a valid Fyers symbol,
// confirmed via Fyers' own community docs), but every OTHER part of this
// codebase (HALF_DAY_SYMBOLS, discoverAndSubscribeMultiStrikes's indices
// array, state['NIFTY'] lookups throughout) expects the bare short name as
// the state key. This map translates an incoming tick's real Fyers symbol
// back to the bare name the rest of the code relies on - added 2026-08-24
// after discovering this translation never existed, which meant these
// three symbols could never populate state at all even once correctly
// subscribed.
const INDEX_TICK_SYMBOL_TO_STATE_KEY = {
  'NSE:NIFTY50-INDEX': 'NIFTY',
  'NSE:NIFTYBANK-INDEX': 'BANKNIFTY',
  'BSE:SENSEX-INDEX': 'SENSEX',
};

  fyersSocket.on('message', tick => {
    const rawSymbol = tick.symbol || tick.s;
    const symbol = (rawSymbol && INDEX_TICK_SYMBOL_TO_STATE_KEY[rawSymbol]) || rawSymbol;
    if (symbol && state[symbol]) {
      updateStateFromTick(symbol, tick);
      lastTickReceivedAt = new Date().toISOString();
      recordSubscribeSuccess(); // a real tick proves the token/subscribe is genuinely working — clear the failure/backoff state
      scheduleBroadcast();
      if (trendScannerAvailable) trendScanner.processTick(symbol, tick); // feed the trend scanner's candle builder / VWAP accumulator
    }

    if (tick && tick.type === 'dp' && symbol) {
      if (symbol === trackedStrikeSymbols.ce) {
        trackedStrikeDepth.ce = computeMaxLevelsFrom5(tick);
        scheduleBroadcast();
      } else if (symbol === trackedStrikeSymbols.pe) {
        trackedStrikeDepth.pe = computeMaxLevelsFrom5(tick);
        scheduleBroadcast();
      }
    }
  });

  fyersSocket.on('error', msg => {
    console.error('Fyers WS error:', msg);
    // code -15 = "Please provide valid token" — a rejected/expired token, not a transient
    // network blip. Track it separately so repeated rejections trigger backoff/circuit-break
    // instead of being retried at the same fixed interval as a genuine network hiccup.
    const reason = (msg && msg.code === -15) ? 'invalid token (-15)' : `error code ${msg && msg.code}`;
    recordSubscribeFailure(reason);
  });
  fyersSocket.on('close', () => { console.log('Fyers WS connection closed.'); isLive = false; });

  fyersSocket.autoreconnect(6);
  fyersSocket.connect();
}

// ============ stall watchdog ============
function isMarketHoursIST(){
  const now = new Date();
  const istOffset = 5.5 * 60;
  const utcMinutes = now.getUTCHours()*60 + now.getUTCMinutes();
  const istMinutes = (utcMinutes + istOffset) % (24*60);
  const day = now.getUTCDay();
  const isWeekday = day >= 1 && day <= 5;
  return isWeekday && istMinutes >= (9*60+15) && istMinutes <= (15*60+30);
}

// 2026-08-24 fix: was 90 seconds, which turned out to be too aggressive —
// during a real incident, this triggered a forced reconnect roughly every
// ~3 minutes, continuously, for hours (including right through market
// open). The reconnect cycle itself takes 6+ seconds before a fresh tick
// can even arrive, and normal quiet periods across even 210 actively-
// traded symbols can plausibly exceed 90 seconds without a false "stall".
// Widened to give real lulls more room, while still catching a genuinely
// dead connection within a few minutes rather than letting it run all day.
const STALL_THRESHOLD_MS = 3 * 60 * 1000; // 3 minutes with no real tick = considered stalled

setInterval(() => {
  if(!currentAccessToken || !isMarketHoursIST()) return; // nothing to watch if not logged in or market closed

  // Circuit breaker: once we've hit MAX_CONSECUTIVE_FAILURES in a row, stop auto-retrying
  // entirely. Hammering Fyers every 30-90s with a token that's already been rejected
  // repeatedly accomplishes nothing and risks tripping rate limits — a human needs to
  // redo the daily login instead. This flag only clears via recordSubscribeSuccess()
  // (a real tick came in) or a fresh /submit-auth-code login.
  if(needsRelogin) return;

  const sinceConnectionStarted = lastConnectionAttemptAt ? Date.now() - lastConnectionAttemptAt : Infinity;
  if(sinceConnectionStarted < STALL_THRESHOLD_MS) return;

  // Exponential backoff: don't retry again until enough time has passed since the
  // last known subscribe failure. If there's been no failure recorded yet (e.g. a
  // genuine silent stall with no error at all), fall through to the normal
  // stale-tick check below at the standard cadence.
  if(lastSubscribeFailureAt){
    const sinceLastFailure = Date.now() - new Date(lastSubscribeFailureAt).getTime();
    if(sinceLastFailure < currentBackoffMs()) return;
  }

  const staleFor = lastTickReceivedAt ? Date.now() - new Date(lastTickReceivedAt).getTime() : sinceConnectionStarted;
  if(staleFor > STALL_THRESHOLD_MS){
    console.log(`No real tick for over ${Math.round(staleFor/1000)}s during market hours — forcing a fresh Fyers reconnect (this SDK is known to go silent without an error).`);
    try{ if(fyersSocket) fyersSocket.close(); } catch(e){ /* ignore */ }
    startFyersConnection(currentAccessToken);
  }
}, 30000); // check every 30 seconds

// ============ web server: auth page + WebSocket relay, sharing one port ============
const server = http.createServer(async (req, res) => {
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

    const statusBanner = needsRelogin
      ? `<p style="background:#fee; border:1px solid #c00; padding:12px; border-radius:6px;">
           <b>⚠ TOKEN REJECTED REPEATEDLY — RELOGIN REQUIRED</b><br>
           ${consecutiveSubscribeFailures} consecutive subscribe failures (last: ${lastSubscribeFailureReason || 'unknown'} at ${lastSubscribeFailureAt || 'unknown'}).<br>
           Auto-retry has stopped. Log in again below to resume.
         </p>`
      : `<p>Status: <b>${isLive ? 'Connected and live' : 'Not connected'}</b>${consecutiveSubscribeFailures > 0 ? ` — ${consecutiveSubscribeFailures} recent subscribe failure(s), retrying with backoff` : ''}</p>`;

    res.writeHead(200, { 'Content-Type': 'text/html' });
    res.end(`
      <html><body style="font-family:sans-serif; max-width:600px; margin:40px auto;">
        <h2>Fyers Live Scanner — Daily Login</h2>
        ${statusBanner}
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
        // A fresh login is a clean slate — clear any circuit-breaker state from before,
        // so the new token gets a full, unhurried set of retry attempts of its own.
        recordSubscribeSuccess();
        startFyersConnection(response.access_token);
        currentAccessToken = response.access_token;

        // Backfill the trend scanner's daily + today's 15-min candle history via
        // Fyers' REST API now, right after login, so EMA20/RSI14/ADX14/SuperTrend on
        // those two timeframes are accurate from the start instead of slowly building
        // up live all day. Runs in the background — doesn't block the login response.
        // Uses the same fyersModel SDK pattern as place-order/track-strike below
        // (rather than hand-rolled HTTP) so the correct endpoint/auth handling is
        // reused instead of duplicated — see trend_scanner.js's 2026-08-16 fix notes
        // for why this replaced an earlier version that could hang indefinitely.
        if (trendScannerAvailable) {
          const fyersForHistory = new fyersModel({ path: __dirname, enableLogging: false });
          fyersForHistory.setAppId(APP_ID);
          fyersForHistory.setAccessToken(response.access_token);
          trendScanner.backfillHistory(fyersForHistory, symbols)
            .then(() => console.log('Trend scanner: history backfill complete.'))
            .catch(err => console.log('Trend scanner backfill failed:', err.message));
        }

        try{
          const FyersTbtSocket = require('fyers-api-v3/tbtsocket/tbtSocket.js');
          const tbtFullToken = `${APP_ID}:${response.access_token}`;
          const tbtSocket = new FyersTbtSocket(tbtFullToken, __dirname, false);

          tbtSocket.on('depth', (symbol, depth) => {
            if (symbol === trackedStrikeSymbols.ce) {
              trackedStrikeDepth.ce = computeMaxLevelsFrom50(depth);
              scheduleBroadcast();
            } else if (symbol === trackedStrikeSymbols.pe) {
              trackedStrikeDepth.pe = computeMaxLevelsFrom50(depth);
              scheduleBroadcast();
            }
          });
          tbtSocket.on('error', (err) => {
            console.log('TBT socket error event:', err && err.message ? err.message : err);
          });
          tbtSocket.on('servererror', (msg) => {
            console.log('TBT socket server error:', msg);
          });
          tbtSocket.on('close', (event) => {
            console.log('TBT socket closed. Event:', event && event.code ? `code=${event.code}` : event);
            currentTbtSocket = null;
          });
          tbtSocket.on('open', () => {
            console.log('TBT socket connected and ready.');
            currentTbtSocket = tbtSocket;
          });
          tbtSocket.connect();
        } catch(err){
          console.log('TBT socket setup threw an error:', err.message);
        }

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

  if (parsed.pathname === '/track-strike' && req.method === 'POST') {
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
        const { strike } = JSON.parse(body);
        const strikeNum = parseFloat(strike);
        if (!strikeNum || strikeNum <= 0) throw new Error('strike must be a positive number');

        const fyers = new fyersModel({ path: __dirname, enableLogging: false });
        fyers.setAppId(APP_ID);
        fyers.setAccessToken(currentAccessToken);

        const chainResponse = await fyers.getOptionChain({
          symbol: 'NSE:NIFTY50-INDEX',
          strikecount: 30,
          timestamp: ''
        });
        if (chainResponse.s !== 'ok' && chainResponse.code !== 200) {
          throw new Error('getOptionChain failed: ' + JSON.stringify(chainResponse));
        }

        const matchCE = chainResponse.data.optionsChain.find(o => o.strike_price === strikeNum && o.option_type === 'CE');
        const matchPE = chainResponse.data.optionsChain.find(o => o.strike_price === strikeNum && o.option_type === 'PE');
        if (!matchCE || !matchPE) {
          throw new Error(`Strike ${strikeNum} not found in the current option chain — check the value and that it's a valid NIFTY strike interval`);
        }

        console.log(`Tracking strike ${strikeNum}: CE=${matchCE.symbol}, PE=${matchPE.symbol}`);

        if (trackedStrikeSymbols.ce || trackedStrikeSymbols.pe) {
          try {
            fyersSocket.unsubscribe([trackedStrikeSymbols.ce, trackedStrikeSymbols.pe].filter(Boolean), 'DepthUpdate');
          } catch(e){ /* best-effort — a failed unsubscribe of the old symbols isn't fatal */ }
        }

        trackedStrikeSymbols = { ce: matchCE.symbol, pe: matchPE.symbol, strike: strikeNum };
        trackedStrikeDepth = { ce: null, pe: null };

        fyersSocket.subscribe([matchCE.symbol, matchPE.symbol], 'DepthUpdate');

        if (currentTbtSocket) {
          try {
            currentTbtSocket.subscribe([matchCE.symbol, matchPE.symbol], 1, 'depth');
          } catch(e){
            console.log('TBT subscribe for tracked strike threw:', e.message);
          }
        }

        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ strike: strikeNum, ce: matchCE.symbol, pe: matchPE.symbol }));
      } catch (err) {
        console.log('track-strike threw an exception:', err.message);
        res.writeHead(400, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ error: err.message }));
      }
    });
    return;
  }

  if (parsed.pathname === '/set-round-tolerance' && req.method === 'POST') {
    if (parsed.query.token !== RELAY_TOKEN) {
      res.writeHead(401, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ error: 'Invalid token' }));
      return;
    }
    let body = '';
    req.on('data', chunk => { body += chunk; });
    req.on('end', () => {
      try {
        const { tolerancePct } = JSON.parse(body);
        const val = parseFloat(tolerancePct);
        if (!(val > 0) || val > 10) throw new Error('tolerancePct must be a positive number, 10 or less');
        roundNumberTolerancePct = val;
        console.log(`Round-number tolerance changed to ${val}%`);
        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ tolerancePct: val }));
      } catch (err) {
        res.writeHead(400, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ error: err.message }));
      }
    });
    return;
  }

  if (parsed.pathname === '/set-cpr-tolerance' && req.method === 'POST') {
    if (parsed.query.token !== RELAY_TOKEN) {
      res.writeHead(401, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ error: 'Invalid token' }));
      return;
    }
    let body = '';
    req.on('data', chunk => { body += chunk; });
    req.on('end', () => {
      try {
        const { tolerancePct } = JSON.parse(body);
        const val = parseFloat(tolerancePct);
        if (!(val > 0) || val > 10) throw new Error('tolerancePct must be a positive number, 10 or less');
        narrowCprTolerancePct = val;
        console.log(`Narrow CPR tolerance changed to ${val}%`);
        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ tolerancePct: val }));
      } catch (err) {
        res.writeHead(400, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ error: err.message }));
      }
    });
    return;
  }

  if (parsed.pathname === '/set-camarilla-tolerance' && req.method === 'POST') {
    if (parsed.query.token !== RELAY_TOKEN) {
      res.writeHead(401, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ error: 'Invalid token' }));
      return;
    }
    let body = '';
    req.on('data', chunk => { body += chunk; });
    req.on('end', () => {
      try {
        const { tolerancePct } = JSON.parse(body);
        const val = parseFloat(tolerancePct);
        if (!(val > 0) || val > 10) throw new Error('tolerancePct must be a positive number, 10 or less');
        narrowCamarillaTolerancePct = val;
        console.log(`Narrow Camarilla tolerance changed to ${val}%`);
        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ tolerancePct: val }));
      } catch (err) {
        res.writeHead(400, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ error: err.message }));
      }
    });
    return;
  }

  if (parsed.pathname === '/status' && req.method === 'GET') {
    // Lightweight JSON status endpoint — useful for checking circuit-breaker state
    // without loading the full HTML login page.
    res.writeHead(200, { 'Content-Type': 'application/json' });
    res.end(JSON.stringify({
      isLive,
      lastTickReceivedAt,
      needsRelogin,
      consecutiveSubscribeFailures,
      lastSubscribeFailureAt,
      lastSubscribeFailureReason,
      nextBackoffSeconds: needsRelogin ? null : Math.round(currentBackoffMs()/1000),
    }));
    return;
  }

  res.writeHead(404);
  res.end('Not found');
});

const wss = new WebSocket.Server({ server, path: '/live' });

function buildHalfDayLevels(){
  const result = {};
  HALF_DAY_SYMBOLS.forEach(symbol => {
    const yFirst = yesterdayHalves[symbol] && yesterdayHalves[symbol].firstHalf;
    const ySecond = yesterdayHalves[symbol] && yesterdayHalves[symbol].secondHalf;
    result[symbol] = {
      firstHalf: firstHalfLocked[symbol] || yFirst || null,
      firstHalfIsToday: !!firstHalfLocked[symbol],
      secondHalf: secondHalfLocked[symbol] || ySecond || null,
      secondHalfIsToday: !!secondHalfLocked[symbol],
    };
  });
  return result;
}

const RELATIVE_POS_ORDER = [-5,-4,-3,-2,-1,0,1,2,3,4,5].map(n => n === 0 ? 'ATM' : (n > 0 ? `ATM+${n}` : `ATM${n}`));

function buildMultiStrikeHalfDayLevels(){
  const result = { NIFTY: [], BANKNIFTY: [], SENSEX: [] };
  const bySymbol = {};

  multiStrikeSymbolList.forEach(symbol => {
    const meta = multiStrikeMeta[symbol];
    if(!meta) return;
    const key = `${meta.index}_${meta.relativePos}_${meta.type}`;
    const yData = yesterdayMultiStrikeHalves[key];
    bySymbol[key] = {
      index: meta.index, relativePos: meta.relativePos, type: meta.type, strike: meta.strike,
      firstHalf: firstHalfLocked[symbol] || (yData && yData.firstHalf) || null,
      firstHalfIsToday: !!firstHalfLocked[symbol],
      secondHalf: secondHalfLocked[symbol] || (yData && yData.secondHalf) || null,
      secondHalfIsToday: !!secondHalfLocked[symbol],
      first5Min: first5MinLocked[symbol] || null,
    };
  });

  Object.values(bySymbol).forEach(row => {
    if(result[row.index]) result[row.index].push(row);
  });

  ['NIFTY', 'BANKNIFTY', 'SENSEX'].forEach(idx => {
    result[idx].sort((a, b) => {
      const posDiff = RELATIVE_POS_ORDER.indexOf(a.relativePos) - RELATIVE_POS_ORDER.indexOf(b.relativePos);
      if(posDiff !== 0) return posDiff;
      return a.type === b.type ? 0 : (a.type === 'CE' ? -1 : 1);
    });
  });
  return result;
}

function buildPayload(){
  const orb5 = computeOrbBreakouts(5);
  const orb15 = computeOrbBreakouts(15);

  // computed as a local var (not inline in the return below) so we can drain
  // and send any queued Telegram notifications right after — this is the
  // ONLY place getStrongWeakPayload() is called per broadcast, so it's the
  // natural spot to also check for new Strong/Weak/Turning-Weak qualifications
  const strongWeakPayload = trendScannerAvailable
    ? trendScanner.getStrongWeakPayload(state)
    : { strong: [], weak: [], turningWeak: [], all: [] };
  checkAndSendStrongWeakNotifications();

  const momentumScannerPayload = trendScannerAvailable
    ? trendScanner.getMomentumScannerPayload(state, momentumScannerSymbols)
    : { matches: [] };

  const btstLivePayload = trendScannerAvailable
    ? trendScanner.getBtstVolumeRatioPayload(state)
    : { rows: [] };

  const narrowCprLivePayload = trendScannerAvailable
    ? trendScanner.getNarrowCprPayload(state)
    : { rows: [] };

  const narrowCamarillaLivePayload = trendScannerAvailable
    ? trendScanner.getNarrowCamarillaPayload(state)
    : { rows: [] };

  return {
    ...computeScreeners(),
    slotHistory,
    screenerScanDone, screenerScanTimestamp, screenerScanTimeTarget: SCREENER_SCAN_TIME_MINUTES,
    screenerScan15mDone, screenerScan15mTimestamp, screenerScan15mTimeTarget: SCREENER_SCAN_15M_TIME_MINUTES,
    orb5Up: orb5.up, orb5Down: orb5.down,
    orb15Up: orb15.up, orb15Down: orb15.down,
    orb5Locked: orb5LockedFlag, orb15Locked: orb15LockedFlag,
    roundNumberMatches: buildRoundNumberRows(), roundNumberTolerancePct, roundNumberHistory,
    earlyExhaustionBreakdown: buildEarlyExhaustionRows(),
    earlyExhaustionScanDone, earlyExhaustionScanTimestamp,
    earlyBottomBreakout: buildEarlyBottomRows(),
    earlyBottomScanDone, earlyBottomScanTimestamp,
    camarillaBuy: buildCamarillaBuyRows(), camarillaSell: buildCamarillaSellRows(),
    camarillaScanDone, camarillaScanTimestamp,
    narrowCpr: buildNarrowCprRows(), narrowCprTolerancePct,
    narrowCprScanDone, narrowCprScanTimestamp,
    narrowCamarilla: buildNarrowCamarillaRows(), narrowCamarillaTolerancePct,
    narrowCamarillaScanDone, narrowCamarillaScanTimestamp,
    hasYesterdaySnapshot: Object.keys(yesterdaySnapshot).length > 0,
    first5MinLocked, first5MinLockedFlag,
    preMarketClose, preMarketCloseLockedFlag,
    halfDayLevels: buildHalfDayLevels(),
    multiStrikeHalfDayLevels: buildMultiStrikeHalfDayLevels(),
    trackedStrike: trackedStrikeSymbols,
    trackedStrikeDepth,
    trendScanner: trendScannerAvailable ? trendScanner.getScannerPayload(state) : [],
    strongWeakScanner: strongWeakPayload,
    momentumScanner: momentumScannerPayload,
    btstScanner: {
      live: btstLivePayload.rows,
      locked: btstLockedRows,
      lockDone: btstLockDone,
      lockTimestamp: btstLockTimestamp,
      lockTimeTarget: BTST_LOCK_TIME_MINUTES,
      volumeRatioThreshold: BTST_VOLUME_RATIO_THRESHOLD,
    },
    // Named narrowCprNextDay (NOT narrowCpr) deliberately - there's already
    // an existing, different "Narrow CPR" screener above (narrowCpr /
    // narrowCprScanDone / narrowCprScanTimestamp) from earlier in this
    // project. This is a separate feature: the Chartink-formula-matched
    // "today's CPR width > 10x tomorrow's projected width" backtest built
    // and validated today - genuinely different logic, needs its own name.
    narrowCprNextDay: {
      live: narrowCprLivePayload.rows,
      locked: narrowCprLockedRows,
      lockDone: narrowCprLockDone,
      lockTimestamp: narrowCprLockTimestamp,
      lockTimeTarget: NARROW_CPR_LOCK_TIME_MINUTES,
    },
    narrowCamarilla: {
      live: narrowCamarillaLivePayload.rows,
      locked: narrowCamarillaLockedRows,
      lockDone: narrowCamarillaLockDone,
      lockTimestamp: narrowCamarillaLockTimestamp,
      lockTimeTarget: NARROW_CAMARILLA_LOCK_TIME_MINUTES,
    },
    top3Losers916: {
      locked: top3Losers916Locked,
      lockDone: top3Losers916LockedFlag,
      lockTimeTarget: TOP3_LOSERS_916_LOCK_MINUTES,
    },
    // Full quote list for every tracked symbol (not just screener matches) —
    // needed by tools like the Gann Square of 9 calculator, which computes
    // levels for any symbol regardless of whether it matched any screener.
    // Kept minimal (just symbol/ltp/prevClose) to keep payload size small
    // across 210 symbols sent on every broadcast.
    allQuotes: Object.entries(state).map(([symbol, s]) => ({
      symbol, ltp: s.ltp, prevClose: s.prevClose, dayHigh: s.high, dayLow: s.low,
    })),
    // circuit-breaker status, so the browser tool can show a clear "needs relogin"
    // banner instead of just quietly showing a stale feed
    connectionHealth: {
      needsRelogin,
      consecutiveSubscribeFailures,
      lastSubscribeFailureAt,
      lastSubscribeFailureReason,
    }
  };
}


wss.on('connection', (ws, req) => {
  const parsed = url.parse(req.url, true);
  if (parsed.query.token !== RELAY_TOKEN) {
    ws.close(4001, 'Invalid token');
    return;
  }
  console.log('Browser tool connected to relay.');
  ws.send(JSON.stringify(buildPayload()));
});

function broadcastScreeners() {
  const payload = JSON.stringify(buildPayload());
  wss.clients.forEach(client => {
    if (client.readyState === WebSocket.OPEN) client.send(payload);
  });
}

let broadcastPending = false;
function scheduleBroadcast() {
  if (broadcastPending) return;
  broadcastPending = true;
  setTimeout(() => { broadcastPending = false; broadcastScreeners(); }, 1000);
}

server.listen(PORT, () => {
  console.log(`*** VERSION CHECK: BUILD-${new Date().toISOString()} — if you don't see this exact marker, this deployment is NOT running the latest code ***`);
  console.log(`Server listening on port ${PORT}. Visit your Railway URL to complete daily login.`);
});
