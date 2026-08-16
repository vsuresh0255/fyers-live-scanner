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
const trendScanner = require('./trend_scanner.js'); // requires trend_scanner.js to be uploaded in this same folder

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

let screenerScanResults = { openlow: null, openhigh: null, gapneutral: null };
let screenerScanDone = false;
let screenerScanDateKey = null;
let screenerScanTimestamp = null;

function checkAndRunScreenerScan(){
  const { dateKey, minutes } = getISTDateKeyAndMinutes();

  if(screenerScanDateKey !== dateKey){
    screenerScanDateKey = dateKey;
    screenerScanDone = false;
    screenerScanResults = { openlow: null, openhigh: null, gapneutral: null };
    screenerScanTimestamp = null;
  }

  if(!screenerScanDone && minutes >= SCREENER_SCAN_TIME_MINUTES){
    const snap = computeScreenersUnrestricted();
    screenerScanResults.openlow = snap.openEqLow;
    screenerScanResults.openhigh = snap.openEqHigh;
    screenerScanResults.gapneutral = snap.gapNeutral;
    screenerScanDone = true;
    screenerScanTimestamp = timeLabel();
    console.log(`Screener scan locked at ${screenerScanTimestamp} — Open=Low: ${screenerScanResults.openlow.length}, Open=High: ${screenerScanResults.openhigh.length}, Gap-Neutral: ${screenerScanResults.gapneutral.length} symbols.`);
    saveScreenerScanResults();
  }
}

function computeScreenersUnrestricted() {
  const openEqLow = [], openEqHigh = [], gapNeutral = [];
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
  });
  return { openEqLow, openEqHigh, gapNeutral };
}

function buildLockedScreenerRows(key){
  const frozen = screenerScanResults[key];
  if(!frozen) return [];
  return frozen.map(r => ({
    ...r,
    ltp: (state[r.symbol] && state[r.symbol].ltp !== null) ? state[r.symbol].ltp : r.ltp,
    matchedAt: screenerScanTimestamp,
  }));
}

const FIRST_5MIN_LOCK_MINUTES = 9 * 60 + 20;
const PRE_MARKET_CLOSE_MINUTES = 9 * 60 + 9;
let preMarketClose = {};
let preMarketCloseLockedFlag = false;
let preMarketCloseDateKey = null;

function checkAndLockPreMarketClose(){
  const { dateKey, minutes } = getISTDateKeyAndMinutes();
  if(preMarketCloseDateKey !== dateKey){
    preMarketCloseDateKey = dateKey;
    preMarketCloseLockedFlag = false;
    preMarketClose = {};
  }
  if(!preMarketCloseLockedFlag && minutes >= PRE_MARKET_CLOSE_MINUTES){
    HALF_DAY_SYMBOLS.forEach(symbol => {
      const s = state[symbol];
      if(s && s.ltp !== null) preMarketClose[symbol] = s.ltp;
    });
    preMarketCloseLockedFlag = true;
    console.log(`Pre-market close captured for ${Object.keys(preMarketClose).length} symbol(s).`);
  }
}

const EOD_SNAPSHOT_MINUTES = 15 * 60 + 30;

let first5MinLocked = {};
let first5MinLockedFlag = false;
let first5MinDateKey = null;

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
const STRIKE_TRACK_RANGE = 5;
const NSE_SYMBOL_MASTER_URL = 'https://public.fyers.in/sym_details/NSE_FO.csv';
const BSE_SYMBOL_MASTER_URL = 'https://public.fyers.in/sym_details/BSE_FO.csv';

let multiStrikeMeta = {};
let multiStrikeSymbolList = [];
let multiStrikeSelectedToday = false;
let multiStrikeDiscoveryInProgress = false;
let yesterdayMultiStrikeHalves = {};

function fetchUrl(targetUrl){
  return new Promise((resolve, reject) => {
    https.get(targetUrl, (res) => {
      let data = '';
      res.on('data', chunk => { data += chunk; });
      res.on('end', () => resolve(data));
    }).on('error', reject);
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

    let meta = {};
    ['NIFTY', 'BANKNIFTY'].forEach(sym => {
      const atm = Math.round(state[sym].ltp / STRIKE_INTERVALS[sym]) * STRIKE_INTERVALS[sym];
      Object.assign(meta, parseStrikesFromCsv(nseCsv, sym, atm, STRIKE_INTERVALS[sym]));
    });
    if(bseCsv){
      const atm = Math.round(state.SENSEX.ltp / STRIKE_INTERVALS.SENSEX) * STRIKE_INTERVALS.SENSEX;
      Object.assign(meta, parseStrikesFromCsv(bseCsv, 'SENSEX', atm, STRIKE_INTERVALS.SENSEX));
    }

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

function checkAndLockFirst5MinCandle(){
  const { dateKey, minutes } = getISTDateKeyAndMinutes();
  if(first5MinDateKey !== dateKey){
    first5MinDateKey = dateKey;
    first5MinLockedFlag = false;
    first5MinLocked = {};
  }
  if(!first5MinLockedFlag && minutes >= FIRST_5MIN_LOCK_MINUTES){
    Object.keys(state).forEach(symbol => {
      const s = state[symbol];
      if(s.high !== null && s.low !== null && s.ltp !== null && s.open !== null) first5MinLocked[symbol] = { open: s.open, high: s.high, low: s.low, close: s.ltp };
    });
    first5MinLockedFlag = true;
    console.log(`First-5-min candle locked for ${Object.keys(first5MinLocked).length} symbols.`);
  }
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

  const withVolume = Object.entries(state).filter(([, s]) => s.volume !== null).map(([symbol, s]) => ({ symbol, volume: s.volume, ltp: s.ltp }));
  withVolume.sort((a, b) => b.volume - a.volume);
  const topCount = Math.max(1, Math.ceil(withVolume.length * 0.05));
  const volumeShockers = withVolume.slice(0, topCount);
  return { openEqLow, openEqHigh, gapNeutral, volumeShockers, updatedAt: new Date().toISOString(), isLive, lastTickReceivedAt };
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
  checkAndLockFirst5MinCandle();
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
    }, 2000);
  });

  fyersSocket.on('message', tick => {
    const symbol = tick.symbol || tick.s;
    if (symbol && state[symbol]) {
      updateStateFromTick(symbol, tick);
      lastTickReceivedAt = new Date().toISOString();
      recordSubscribeSuccess(); // a real tick proves the token/subscribe is genuinely working — clear the failure/backoff state
      scheduleBroadcast();
      trendScanner.processTick(symbol, tick); // feed the trend scanner's candle builder / VWAP accumulator
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

const STALL_THRESHOLD_MS = 90 * 1000; // 90 seconds with no real tick = considered stalled

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
        trendScanner.backfillHistory(APP_ID, response.access_token, symbols)
          .then(() => console.log('Trend scanner: history backfill complete.'))
          .catch(err => console.log('Trend scanner backfill failed:', err.message));

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
  return {
    ...computeScreeners(),
    slotHistory,
    screenerScanDone, screenerScanTimestamp, screenerScanTimeTarget: SCREENER_SCAN_TIME_MINUTES,
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
    trendScanner: trendScanner.getScannerPayload(state),
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
