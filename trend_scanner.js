/**
 * Trend Scanner module
 * =====================
 * A self-contained addition to the existing Railway relay (server.js). Builds
 * 5-min, 15-min, and Daily candles per symbol from the same live tick stream
 * server.js already receives, computes a standard indicator set on each
 * timeframe, and classifies each symbol as Bullish / Bearish / Mixed per
 * timeframe — "Bullish" ONLY when every indicator agrees bullish at once
 * (confirmed spec: strict confluence, not majority vote).
 *
 * Confirmed rules (per your answers):
 *   - RSI bullish:   RSI(14) > 60   (stricter than the standard 50 line)
 *   - ADX bullish:   ADX(14) >= 25  AND  +DI > -DI
 *   - EMA20 bullish: LTP > EMA(20) on that timeframe
 *   - SuperTrend bullish: SuperTrend(10, 3) direction === 'up'
 *   - VWAP bullish:  LTP > day's VWAP  (VWAP is a single intraday value,
 *     reset at market open — applied to the 5-min and 15-min trend checks
 *     only, NOT the Daily trend, since VWAP has no daily-timeframe meaning)
 *   - Daily trend uses: EMA20 + SuperTrend + RSI + ADX (no VWAP)
 *   - 5-min / 15-min trend uses: EMA20 + SuperTrend + RSI + ADX + VWAP (all five)
 *
 * A symbol needs enough closed candles to compute these indicators at all —
 * ADX/RSI/SuperTrend all need >= 14-15 candles minimum, EMA20 needs 20. Until
 * then a timeframe shows status 'warming-up' rather than a wrong/partial
 * trend. The REST backfill on startup (see backfillHistory below) exists
 * specifically to avoid a long "warming-up" period each morning for Daily
 * and 15-min — 5-min still builds live through the day since backfilling
 * intraday 5-min history is usually unnecessary (20 candles = 100 minutes,
 * done well before most trading decisions matter).
 *
 * ---- WIRING INTO server.js (do these 4 things) ----
 * 1. Near the top of server.js, after requiring fyers-api-v3:
 *      const trendScanner = require('./trend_scanner.js');
 *
 * 2. After a successful login in /submit-auth-code, right after
 *    startFyersConnection(response.access_token) is called, build a
 *    fyersModel instance the same way place-order/track-strike already do
 *    (setAppId + setAccessToken), then add:
 *      const fyersForHistory = new fyersModel({ path: __dirname, enableLogging: false });
 *      fyersForHistory.setAppId(APP_ID);
 *      fyersForHistory.setAccessToken(response.access_token);
 *      trendScanner.backfillHistory(fyersForHistory, symbols)
 *        .then(() => console.log('Trend scanner: history backfill complete.'))
 *        .catch(err => console.log('Trend scanner backfill failed:', err.message));
 *
 * 3. Inside the existing fyersSocket.on('message', tick => { ... }) handler,
 *    right after the existing `if (symbol && state[symbol]) { updateStateFromTick(...) }`
 *    block, add:
 *      if (symbol && state[symbol]) {
 *        trendScanner.processTick(symbol, tick);
 *      }
 *
 * 4. Inside buildPayload(), add one new key to the returned object:
 *      trendScanner: trendScanner.getScannerPayload(),
 *
 * That's it — the module manages all its own state internally (candles,
 * indicator history, VWAP accumulators) and resets itself at each new IST
 * trading day automatically, the same way the rest of server.js does.
 */

// (no https require needed — REST history calls now go through the caller's
// fyersModel SDK instance, see backfillHistory() below)

// ============ config ============
const EMA_PERIOD = 20;
const RSI_PERIOD = 14;
const ADX_PERIOD = 14;
const ATR_PERIOD = 14;         // used internally by ADX and SuperTrend
const SUPERTREND_PERIOD = 10;
const SUPERTREND_MULTIPLIER = 3;
const RSI_BULLISH_THRESHOLD = 60;
const ADX_BULLISH_THRESHOLD = 25;
const MAX_CANDLES = 250;       // rolling cap per symbol per timeframe, bounds memory

const BACKFILL_DELAY_MS = 150; // pause between REST calls during startup backfill, to stay clear of Fyers' rate limiter

// ============ per-symbol state ============
// candles[timeframe][symbol] = array of {time, open, high, low, close}, oldest first
const candles = { '5m': {}, '15m': {}, 'D': {} };
// in-progress (not yet closed) candle per symbol per intraday timeframe
const building = { '5m': {}, '15m': {} };
// VWAP accumulators — reset each trading day
const vwapState = {}; // symbol -> { cumPV, cumVol, lastCumVolume }
let vwapDateKey = null;

function getISTDateKeyAndMinutes(){
  const now = new Date();
  const istMillis = now.getTime() + (5.5 * 60 * 60 * 1000);
  const ist = new Date(istMillis);
  const dateKey = `${ist.getUTCFullYear()}-${String(ist.getUTCMonth()+1).padStart(2,'0')}-${String(ist.getUTCDate()).padStart(2,'0')}`;
  const minutes = ist.getUTCHours()*60 + ist.getUTCMinutes();
  const epochSeconds = Math.floor(now.getTime()/1000);
  return { dateKey, minutes, epochSeconds };
}

// "HH:MM" for the current IST time — a local equivalent of server.js's own
// timeLabel(), since that function lives in server.js and isn't available
// to this module.
function timeLabel(){
  const { minutes } = getISTDateKeyAndMinutes();
  return `${String(Math.floor(minutes/60)).padStart(2,'0')}:${String(minutes%60).padStart(2,'0')}`;
}

function bucketStart(epochSeconds, timeframeSeconds){
  return Math.floor(epochSeconds / timeframeSeconds) * timeframeSeconds;
}

function pick(obj, candidatesArr){
  for(const key of candidatesArr){
    if(obj[key] !== undefined && obj[key] !== null) return obj[key];
  }
  return null;
}

// ============ indicator math ============
// Simple EMA (standard, not Wilder's) — used for the 20-period EMA column,
// matching the conventional "20 EMA" meaning in most trend-scanner tools.
function computeEMA(closes, period){
  if(closes.length < period) return null;
  const k = 2/(period+1);
  let ema = closes.slice(0, period).reduce((a,b)=>a+b, 0) / period; // seed with SMA
  for(let i = period; i < closes.length; i++){
    ema = closes[i]*k + ema*(1-k);
  }
  return ema;
}

// EMA as a full series (O(n), single pass) — needed for MACD's signal line,
// which is itself an EMA of the MACD line across many points. computeEMA
// above only returns the final value, which is right for a plain "current
// EMA(20)" reading but would need an expensive O(n^2) re-walk if called
// once per point just to build a series — this does it in one pass instead.
function computeEMASeries(values, period){
  const result = new Array(values.length).fill(null);
  const k = 2 / (period + 1);
  let seedSum = 0, seedCount = 0, ema = null;
  for(let i = 0; i < values.length; i++){
    if(values[i] === null){ result[i] = null; continue; }
    if(ema === null){
      seedSum += values[i];
      seedCount++;
      if(seedCount === period){ ema = seedSum / period; result[i] = ema; }
    } else {
      ema = values[i]*k + ema*(1-k);
      result[i] = ema;
    }
  }
  return result;
}

// MACD Histogram (12,26,9) — returns just the LATEST point's {macdLine,
// signal, histogram}, computed efficiently via the series helper above
// rather than recomputing from scratch per-point. Returns null until
// enough history exists (needs 26 for the slower EMA, plus 9 more for the
// signal line to have real data to smooth).
function computeMACDHistogram(closes){
  if(closes.length < 35) return null;
  const ema12Series = computeEMASeries(closes, 12);
  const ema26Series = computeEMASeries(closes, 26);
  const macdLineSeries = closes.map((_, i) =>
    (ema12Series[i] !== null && ema26Series[i] !== null) ? ema12Series[i] - ema26Series[i] : null
  );
  const signalSeries = computeEMASeries(macdLineSeries, 9);
  const lastIdx = closes.length - 1;
  if(macdLineSeries[lastIdx] === null || signalSeries[lastIdx] === null) return null;
  return {
    macdLine: macdLineSeries[lastIdx],
    signal: signalSeries[lastIdx],
    histogram: macdLineSeries[lastIdx] - signalSeries[lastIdx],
  };
}

// Wilder's RSI(14) — the standard RSI smoothing method (not a simple average
// of gains/losses), matching what every charting platform actually shows.
function computeRSI(closes, period){
  if(closes.length < period+1) return null;
  let gains = 0, losses = 0;
  for(let i = 1; i <= period; i++){
    const diff = closes[i]-closes[i-1];
    if(diff >= 0) gains += diff; else losses += -diff;
  }
  let avgGain = gains/period, avgLoss = losses/period;
  for(let i = period+1; i < closes.length; i++){
    const diff = closes[i]-closes[i-1];
    const gain = diff > 0 ? diff : 0;
    const loss = diff < 0 ? -diff : 0;
    avgGain = (avgGain*(period-1) + gain)/period;
    avgLoss = (avgLoss*(period-1) + loss)/period;
  }
  if(avgLoss === 0) return 100;
  const rs = avgGain/avgLoss;
  return 100 - (100/(1+rs));
}

// True Range + Wilder's ATR(14) — shared building block for both ADX and SuperTrend.
function computeTrueRanges(candlesArr){
  const trs = [];
  for(let i = 1; i < candlesArr.length; i++){
    const cur = candlesArr[i], prev = candlesArr[i-1];
    const tr = Math.max(
      cur.high - cur.low,
      Math.abs(cur.high - prev.close),
      Math.abs(cur.low - prev.close)
    );
    trs.push(tr);
  }
  return trs;
}

function wilderSmooth(values, period){
  if(values.length < period) return [];
  const smoothed = [];
  let sum = values.slice(0, period).reduce((a,b)=>a+b, 0);
  smoothed.push(sum); // first smoothed value is just the sum over the seed window (Wilder's convention)
  for(let i = period; i < values.length; i++){
    sum = sum - (sum/period) + values[i];
    smoothed.push(sum);
  }
  return smoothed;
}

// ADX(14) + +DI/-DI — standard Wilder implementation. Returns null until
// enough candles exist (needs roughly 2x the period for a stable reading).
function computeADX(candlesArr, period){
  if(candlesArr.length < period*2) return null;
  const plusDMs = [], minusDMs = [], trs = [];
  for(let i = 1; i < candlesArr.length; i++){
    const cur = candlesArr[i], prev = candlesArr[i-1];
    const upMove = cur.high - prev.high;
    const downMove = prev.low - cur.low;
    plusDMs.push(upMove > downMove && upMove > 0 ? upMove : 0);
    minusDMs.push(downMove > upMove && downMove > 0 ? downMove : 0);
    trs.push(Math.max(cur.high-cur.low, Math.abs(cur.high-prev.close), Math.abs(cur.low-prev.close)));
  }
  const smoothedPlusDM = wilderSmooth(plusDMs, period);
  const smoothedMinusDM = wilderSmooth(minusDMs, period);
  const smoothedTR = wilderSmooth(trs, period);
  if(!smoothedTR.length) return null;

  const plusDIs = [], minusDIs = [], dxs = [];
  for(let i = 0; i < smoothedTR.length; i++){
    const tr = smoothedTR[i];
    if(tr === 0){ plusDIs.push(0); minusDIs.push(0); dxs.push(0); continue; }
    const pDI = 100 * smoothedPlusDM[i]/tr;
    const mDI = 100 * smoothedMinusDM[i]/tr;
    plusDIs.push(pDI); minusDIs.push(mDI);
    const diSum = pDI+mDI;
    dxs.push(diSum === 0 ? 0 : 100*Math.abs(pDI-mDI)/diSum);
  }
  if(dxs.length < period) return null;
  // ADX = Wilder-smoothed average of DX over `period`
  let adx = dxs.slice(0, period).reduce((a,b)=>a+b,0)/period;
  for(let i = period; i < dxs.length; i++){
    adx = (adx*(period-1) + dxs[i])/period;
  }
  return { adx, plusDI: plusDIs[plusDIs.length-1], minusDI: minusDIs[minusDIs.length-1] };
}

// SuperTrend(10, 3) — standard ATR-band-flip implementation. Returns the
// current value and direction ('up' = bullish / price above the line).
function computeSuperTrend(candlesArr, period, multiplier){
  if(candlesArr.length < period+1) return null;
  const trs = computeTrueRanges(candlesArr);
  if(trs.length < period) return null;

  // simple rolling ATR (not Wilder's) is the common SuperTrend convention
  let atrValues = [];
  let sum = trs.slice(0, period).reduce((a,b)=>a+b,0);
  atrValues.push(sum/period);
  for(let i = period; i < trs.length; i++){
    const atr = (atrValues[atrValues.length-1]*(period-1) + trs[i])/period;
    atrValues.push(atr);
  }

  // walk forward computing basic/final bands and the flip logic, starting
  // from the first candle that has a matching ATR value
  const offset = candlesArr.length - atrValues.length;
  let finalUpper = null, finalLower = null, direction = 'up', stValue = null;

  for(let i = 0; i < atrValues.length; i++){
    const c = candlesArr[offset+i];
    const atr = atrValues[i];
    const hl2 = (c.high+c.low)/2;
    const basicUpper = hl2 + multiplier*atr;
    const basicLower = hl2 - multiplier*atr;

    if(i === 0){
      finalUpper = basicUpper; finalLower = basicLower;
      direction = c.close <= finalUpper ? 'down' : 'up';
      stValue = direction === 'up' ? finalLower : finalUpper;
      continue;
    }

    const prevClose = candlesArr[offset+i-1].close;
    finalUpper = (basicUpper < finalUpper || prevClose > finalUpper) ? basicUpper : finalUpper;
    finalLower = (basicLower > finalLower || prevClose < finalLower) ? basicLower : finalLower;

    if(direction === 'up' && c.close < finalLower) direction = 'down';
    else if(direction === 'down' && c.close > finalUpper) direction = 'up';

    stValue = direction === 'up' ? finalLower : finalUpper;
  }

  return { value: stValue, direction };
}

// ============ pivots (classic daily pivots from the PREVIOUS day's H/L/C) ============
function computeClassicPivots(prevHigh, prevLow, prevClose){
  const pp = (prevHigh+prevLow+prevClose)/3;
  const r1 = 2*pp - prevLow;
  const s1 = 2*pp - prevHigh;
  const r2 = pp + (prevHigh-prevLow);
  const s2 = pp - (prevHigh-prevLow);
  return { pp, r1, r2, s1, s2 };
}

// Builds the "near S1, between S1 & PP" style description used by the
// reference tool, by finding which two adjacent levels straddle the LTP.
function describePivotPosition(ltp, pivots){
  if(ltp == null || !pivots) return '—';
  const levels = [
    { name: 'S2', value: pivots.s2 }, { name: 'S1', value: pivots.s1 },
    { name: 'PP', value: pivots.pp }, { name: 'R1', value: pivots.r1 },
    { name: 'R2', value: pivots.r2 },
  ].sort((a,b) => a.value-b.value);

  for(let i = 0; i < levels.length-1; i++){
    const lo = levels[i], hi = levels[i+1];
    if(ltp >= lo.value && ltp <= hi.value){
      const nearer = (ltp-lo.value) <= (hi.value-ltp) ? lo : hi;
      return `${lo.name}-${hi.name}, near ${nearer.name}`;
    }
  }
  if(ltp < levels[0].value) return `Below ${levels[0].name}`;
  return `Above ${levels[levels.length-1].name}`;
}

// ============ trend classification ============
function classifyTrend(ltp, ema20, superTrend, rsi, adxResult, vwap, includeVwap){
  if(ema20 == null || superTrend == null || rsi == null || adxResult == null){
    return 'warming-up';
  }
  if(includeVwap && vwap == null) return 'warming-up';

  const emaUp = ltp > ema20;
  const stUp = superTrend.direction === 'up';
  const rsiUp = rsi > RSI_BULLISH_THRESHOLD;
  const adxUp = adxResult.adx >= ADX_BULLISH_THRESHOLD && adxResult.plusDI > adxResult.minusDI;
  const vwapUp = includeVwap ? (ltp > vwap) : null;

  const emaDown = ltp < ema20;
  const stDown = superTrend.direction === 'down';
  const rsiDown = rsi < (100-RSI_BULLISH_THRESHOLD); // symmetric bearish threshold, i.e. RSI < 40
  const adxDown = adxResult.adx >= ADX_BULLISH_THRESHOLD && adxResult.minusDI > adxResult.plusDI;
  const vwapDown = includeVwap ? (ltp < vwap) : null;

  const bullishChecks = includeVwap ? [emaUp, stUp, rsiUp, adxUp, vwapUp] : [emaUp, stUp, rsiUp, adxUp];
  const bearishChecks = includeVwap ? [emaDown, stDown, rsiDown, adxDown, vwapDown] : [emaDown, stDown, rsiDown, adxDown];

  if(bullishChecks.every(Boolean)) return 'Bullish';
  if(bearishChecks.every(Boolean)) return 'Bearish';
  return 'Mixed';
}

// ============ VWAP (single intraday running value per symbol) ============
function resetVwapIfNewDay(){
  const { dateKey } = getISTDateKeyAndMinutes();
  if(vwapDateKey !== dateKey){
    vwapDateKey = dateKey;
    Object.keys(vwapState).forEach(sym => delete vwapState[sym]);
  }
}

function updateVwap(symbol, price, cumulativeVolume){
  resetVwapIfNewDay();
  if(cumulativeVolume == null || isNaN(cumulativeVolume)) return;
  if(!vwapState[symbol]){
    vwapState[symbol] = { cumPV: 0, cumVol: 0, lastCumVolume: cumulativeVolume };
    return; // first tick of the day just seeds the baseline, no delta yet
  }
  const s = vwapState[symbol];
  const deltaVol = cumulativeVolume - s.lastCumVolume;
  s.lastCumVolume = cumulativeVolume;
  if(deltaVol <= 0) return; // cumulative volume shouldn't go down, but guard against a bad/duplicate tick
  s.cumPV += price*deltaVol;
  s.cumVol += deltaVol;
}

function getVwap(symbol){
  const s = vwapState[symbol];
  if(!s || s.cumVol === 0) return null;
  return s.cumPV/s.cumVol;
}

// ============ candle building from live ticks ============
function ensureCandleStore(timeframe, symbol){
  if(!candles[timeframe][symbol]) candles[timeframe][symbol] = [];
}

function updateIntradayCandle(timeframe, timeframeSeconds, symbol, price, epochSeconds, cumulativeVolume){
  ensureCandleStore(timeframe, symbol);
  const bStart = bucketStart(epochSeconds, timeframeSeconds);
  const cur = building[timeframe][symbol];

  if(!cur || cur.time !== bStart){
    // a new bucket started — the previous in-progress candle (if any) is now closed
    if(cur){
      // this candle's own volume = cumulative volume at close minus cumulative
      // volume at the moment this candle started, i.e. how much traded DURING
      // this specific candle (not the running day total)
      const candleVolume = (cur.lastCumVolume != null && cur.startCumVolume != null)
        ? Math.max(0, cur.lastCumVolume - cur.startCumVolume)
        : null;
      candles[timeframe][symbol].push({ time: cur.time, open: cur.open, high: cur.high, low: cur.low, close: cur.close, volume: candleVolume });
      if(candles[timeframe][symbol].length > MAX_CANDLES) candles[timeframe][symbol].shift();
    }
    building[timeframe][symbol] = {
      time: bStart, open: price, high: price, low: price, close: price,
      startCumVolume: cumulativeVolume != null ? cumulativeVolume : null,
      lastCumVolume: cumulativeVolume != null ? cumulativeVolume : null,
    };
  } else {
    cur.high = Math.max(cur.high, price);
    cur.low = Math.min(cur.low, price);
    cur.close = price;
    if(cumulativeVolume != null) cur.lastCumVolume = cumulativeVolume;
  }
}

let lastKnownDateKeyForCandles = null;

function resetIntradayCandlesIfNewDay(){
  const { dateKey } = getISTDateKeyAndMinutes();
  if(lastKnownDateKeyForCandles !== null && lastKnownDateKeyForCandles !== dateKey){
    ['5m','15m'].forEach(tf => {
      Object.keys(candles[tf]).forEach(sym => { candles[tf][sym] = []; });
      Object.keys(building[tf]).forEach(sym => { delete building[tf][sym]; });
    });
  }
  lastKnownDateKeyForCandles = dateKey;
}

// Call this from server.js's fyersSocket.on('message', ...) handler for
// every tick belonging to a tracked symbol.
function processTick(symbol, tick){
  resetIntradayCandlesIfNewDay();
  const ltp = pick(tick, ['ltp', 'last_traded_price', 'lp']);
  const volume = pick(tick, ['vol_traded_today', 'volume', 'v']);
  if(ltp === null) return;

  const { epochSeconds } = getISTDateKeyAndMinutes();
  updateIntradayCandle('5m', 300, symbol, ltp, epochSeconds, volume);
  updateIntradayCandle('15m', 900, symbol, ltp, epochSeconds, volume);
  if(volume !== null) updateVwap(symbol, ltp, volume);
}

// ============ REST history backfill (daily + today's 15-min) ============
// 2026-08-16 fix: this originally made its own raw https.request() calls to a
// guessed Fyers REST host/path, with NO timeout — if that connection ever
// stalled (wrong host, network hiccup, anything), the returned Promise simply
// never resolved, freezing the entire sequential 210-symbol backfill loop
// forever with no error and no completion message. That's exactly what
// happened in production (confirmed: neither "backfill complete" nor
// "backfill failed" ever printed, even 13+ minutes after login).
//
// Fix: use the SAME fyersModel SDK instance server.js already uses
// successfully elsewhere (getOptionChain, place_order) instead of hand-rolled
// HTTP — the SDK owns the correct endpoint/auth details, so this is no longer
// guesswork. AND wrap every single call in an explicit hard timeout via
// Promise.race, so even an SDK-level stall can never hang the loop again —
// worst case, one symbol's backfill is skipped and logged, and the loop moves
// on to the next symbol rather than freezing entirely.
const HISTORY_CALL_TIMEOUT_MS = 15000;

function withTimeout(promise, ms, label){
  return Promise.race([
    promise,
    new Promise((resolve) => setTimeout(() => resolve({ s: 'error', message: `timed out after ${ms}ms (${label})` }), ms)),
  ]);
}

function sleep(ms){ return new Promise(resolve => setTimeout(resolve, ms)); }

// `fyers` is an already-configured fyersModel instance (appId + access token
// set) — pass in the same object server.js builds for getOptionChain/place_order,
// so this reuses proven-working auth/endpoint handling instead of duplicating it.
// 2026-08-16 fix: the real fyers-api-v3 SDK's method is named getHistory(), NOT
// history() — the earlier version of this file called the wrong (nonexistent)
// method name, which throws "fyers.history is not a function" every time. That
// specific error IS correctly caught below and counted as a per-symbol failure,
// not a crash — but it meant backfill was silently failing for every symbol.
async function fetchOneHistory(fyers, symbol, resolution, rangeFrom, rangeTo){
  const data = { symbol, resolution, date_format: '0', range_from: String(rangeFrom), range_to: String(rangeTo), cont_flag: '1' };
  try{
    const resp = await withTimeout(fyers.getHistory(data), HISTORY_CALL_TIMEOUT_MS, `${symbol} ${resolution}`);
    return resp;
  } catch(err){
    return { s: 'error', message: err.message };
  }
}

// Backfills ~60 daily candles and today's 15-min candles-so-far, for every
// symbol, sequentially with a small delay to stay clear of rate limits.
// Call this once, right after a successful daily login (see wiring notes
// at the top of this file). Safe to call again on a relogin — it just
// re-populates the same arrays. Never throws — logs per-symbol failures and
// keeps going, since one bad symbol shouldn't block the other 209.
//
// 2026-08-16: wrapped the whole body in try/catch with a full stack-trace log
// on any unexpected failure. This function was mysteriously rejecting with
// "symbols is not iterable" in production despite every reproduction attempt
// (real SDK, real files, byte-identical to what shipped) coming back clean —
// this wrapper exists so that if it happens again, the log shows exactly
// which line threw instead of a bare one-line message with no stack.
async function backfillHistory(fyers, symbols){
 try {
  if(!Array.isArray(symbols)){
    console.log(`Trend scanner backfill: symbols argument is not an array (got ${typeof symbols}: ${JSON.stringify(symbols)}) — aborting backfill.`);
    return;
  }
  const nowSeconds = Math.floor(Date.now()/1000);
  const sixtyDaysAgo = nowSeconds - 60*24*60*60;

  const { epochSeconds } = getISTDateKeyAndMinutes();
  const istOffsetSeconds = 5.5*60*60;
  const istNow = epochSeconds + istOffsetSeconds;
  const marketOpenIstToday = Math.floor(istNow/86400)*86400 + 9*3600 + 15*60;
  const todayRangeFrom = marketOpenIstToday - istOffsetSeconds;

  let dailyOkCount = 0, dailyFailCount = 0, m15OkCount = 0, m15FailCount = 0, m15NoDataCount = 0;

  for(const symbol of symbols){
    // daily candles
    const dailyResp = await fetchOneHistory(fyers, symbol, 'D', sixtyDaysAgo, nowSeconds);
    if(dailyResp && dailyResp.s === 'ok' && Array.isArray(dailyResp.candles)){
      ensureCandleStore('D', symbol);
      candles['D'][symbol] = dailyResp.candles.map(c => ({
        time: c[0], open: c[1], high: c[2], low: c[3], close: c[4], volume: c[5] || 0,
      })).slice(-MAX_CANDLES);
      dailyOkCount++;
    } else {
      dailyFailCount++;
    }
    await sleep(BACKFILL_DELAY_MS);

    // today's 15-min candles so far (only meaningful once the market has been open a while)
    if(nowSeconds > todayRangeFrom){
      const m15Resp = await fetchOneHistory(fyers, symbol, '15', todayRangeFrom, nowSeconds);
      if(m15Resp && m15Resp.s === 'ok' && Array.isArray(m15Resp.candles)){
        ensureCandleStore('15m', symbol);
        candles['15m'][symbol] = m15Resp.candles.map(c => ({
          time: c[0], open: c[1], high: c[2], low: c[3], close: c[4],
        })).slice(-MAX_CANDLES);
        m15OkCount++;
      } else if(m15Resp && m15Resp.s === 'no_data'){
        // 2026-08-16: NOT a failure — Fyers uses s:'no_data' (with code:200) to
        // mean "request succeeded, there just aren't any candles in this range"
        // rather than an actual error. This is expected and correct on any day
        // the market hasn't opened yet (before 9:15 AM) or hasn't opened at all
        // (weekends/holidays) — confirmed root cause of the original "0/210 ok"
        // reading was simply that backfill was run on a Sunday, so "today's"
        // 15-min range genuinely has zero candles. On an actual trading day,
        // once the market has been open a while, this should resolve to real
        // candles via the m15OkCount branch above instead.
        m15NoDataCount++;
      } else {
        m15FailCount++;
        // 2026-08-16 diagnostic: kept in place for any GENUINE future failures
        // (auth errors, malformed requests, etc.) — logs the raw response from
        // the first true failure only, to avoid spamming the log.
        if(m15FailCount === 1){
          console.log(`Trend scanner backfill: sample 15m failure for ${symbol} — raw response:`, JSON.stringify(m15Resp));
        }
      }
      await sleep(BACKFILL_DELAY_MS);
    }
  }

  console.log(`Trend scanner backfill detail: daily ${dailyOkCount} ok / ${dailyFailCount} failed, 15m ${m15OkCount} ok / ${m15NoDataCount} no-data / ${m15FailCount} failed (out of ${symbols.length} symbols).`);
 } catch(err){
   console.log('Trend scanner backfill — UNEXPECTED ERROR (full stack below):');
   console.log(err.stack || err.message || err);
   throw err; // still reject, so server.js's own .catch() logs its usual one-line summary too
 }
}

// ============ building the scanner payload ============
function computeTimeframeIndicators(timeframe, symbol, includeVwap, ltp){
  const arr = candles[timeframe][symbol] || [];
  const closes = arr.map(c => c.close);
  const ema20 = computeEMA(closes, EMA_PERIOD);
  const rsi = computeRSI(closes, RSI_PERIOD);
  const adxResult = computeADX(arr, ADX_PERIOD);
  const superTrend = computeSuperTrend(arr, SUPERTREND_PERIOD, SUPERTREND_MULTIPLIER);
  const vwap = includeVwap ? getVwap(symbol) : null;
  const trend = classifyTrend(ltp, ema20, superTrend, rsi, adxResult, vwap, includeVwap);
  return { ema20, rsi, adx: adxResult ? adxResult.adx : null, plusDI: adxResult ? adxResult.plusDI : null, minusDI: adxResult ? adxResult.minusDI : null, superTrend, vwap, trend };
}

// `state` is server.js's existing per-symbol state object ({open,high,low,ltp,...}),
// passed in so this module doesn't need its own separate LTP tracking.
function getScannerPayload(stateRef){
  const rows = [];
  const symbols = Object.keys(candles['D']).length ? Object.keys(candles['D']) : Object.keys(stateRef || {});

  symbols.forEach(symbol => {
    const s = stateRef ? stateRef[symbol] : null;
    const ltp = s ? s.ltp : null;
    if(ltp === null || ltp === undefined) return;

    const daily = computeTimeframeIndicators('D', symbol, false, ltp);
    const m15 = computeTimeframeIndicators('15m', symbol, true, ltp);
    const m5 = computeTimeframeIndicators('5m', symbol, true, ltp);

    // pivots from the most recently CLOSED daily candle (i.e. yesterday's H/L/C)
    const dailyArr = candles['D'][symbol] || [];
    let pivots = null, pivotDesc = '—';
    if(dailyArr.length >= 1){
      const prev = dailyArr[dailyArr.length-1];
      pivots = computeClassicPivots(prev.high, prev.low, prev.close);
      pivotDesc = describePivotPosition(ltp, pivots);
    }

    rows.push({
      symbol,
      ltp,
      pivots: pivotDesc,
      trend5m: m5.trend,
      trend15m: m15.trend,
      trendDaily: daily.trend,
      // ADX/RSI/VWAP/EMA20/SuperTrend shown at 15-min resolution for the table's
      // single-value columns (matching the reference tool's default 15-min view)
      adx: m15.adx, rsi: m15.rsi, vwap: m15.vwap, ema20: m15.ema20,
      superTrend: m15.superTrend ? m15.superTrend.value : null,
      superTrendDirection: m15.superTrend ? m15.superTrend.direction : null,
    });
  });

  return rows;
}

// ============ Strong Stocks for Intraday Scanner ============
// Confirmed rules:
//   - Strong: LTP > EMA(9) on 5-min candles, AND LTP is at/near today's day
//     high OR at/near yesterday's day high.
//   - Weak: mirror, using EMA(9) below + today's/yesterday's day LOW.
//   - "At/near" uses a small tolerance (STRONG_WEAK_PROXIMITY_PCT below),
//     matching the same pattern as the Round Number / Narrow CPR screeners
//     elsewhere in this codebase — exact equality is too fleeting per-tick
//     to be a usable signal, a small band around the level is what actually
//     shows up ("stock is testing its high", not "stock is at the exact
//     paisa of its high this millisecond").
//   - List is LIVE all day (recomputed on every payload build), but each
//     symbol's FIRST qualification during the 9:30-9:50 AM "note window" is
//     remembered and flagged separately — matching the reference tool's
//     guidance to specifically note the list during that window, without
//     preventing the live view from working the rest of the day too.
//   - "Turning Weak" (reversal / shorting candidates): a symbol whose status
//     was Strong at the First Half boundary (12:30 PM) but is currently Weak,
//     checked continuously once we're past 12:30. Reuses the same First
//     Half / Second Half boundary already established elsewhere in this
//     project (9:15-12:30 / 12:30-15:30).
const STRONG_WEAK_EMA_PERIOD = 9;
const STRONG_WEAK_PROXIMITY_PCT = 0.15; // "at/near" tolerance, as a % of the reference level
const NOTE_WINDOW_START_MINUTES = 9*60 + 30;  // 9:30 AM
const NOTE_WINDOW_END_MINUTES = 9*60 + 50;    // 9:50 AM
const FIRST_HALF_BOUNDARY_MINUTES = 9*60 + 15 + 195; // 12:30 PM — same as the rest of the project

// 2026-08 notification-confluence thresholds — kept as module-level constants
// (single source of truth) so both the live notification check below AND
// backtest_strong_weak.js reference the exact same numbers, never two
// separately-maintained copies that could silently drift apart.
const NOTIFY_MIN_VOLUME_RATIO = 1.8;
const NOTIFY_RSI_BULLISH = 65;
const NOTIFY_RSI_BEARISH = 35;
const NOTIFY_MIN_EMA21_MARGIN_PCT = 0.3;
const NOTIFY_MIN_VWAP_MARGIN_PCT = 0.3;
const NOTIFY_MAX_PER_CATEGORY_PER_DAY = Infinity; // 2026-08-17: cap removed per user request — every qualifying signal notifies now, not just the first 5. Kept as a constant (rather than deleting the check entirely) so a future cap can be reintroduced just by changing this one number.
// 2026-08-17 tightening: today's volume-so-far must exceed DOUBLE yesterday's
// FULL day's volume (a 100%+ day-over-day increase), not just "any increase
// at all." Deliberately the SAME threshold for both Strong and Weak — volume
// change can never go below -100% (volume can't be negative), so a literal
// sign-mirror for Weak would be mathematically impossible to satisfy. High
// volume confirms conviction in EITHER direction; which direction is decided
// by the other 5 conditions (status, RSI, EMA21%, VWAP%, pivot position).
const NOTIFY_MIN_VOLUME_CHANGE_PCT = 100;

// Pure function — given a symbol's current status/metrics, returns which
// notification tiers (if any) it qualifies for right now. No side effects,
// no state — this is what makes it safely reusable by both the live app
// (where it gates an actual Telegram send) and the backtest (where it's
// evaluated against historical data to measure how the signal performs).
//
// 2026-08 redesign: the original 4-factor recipe (Volume Ratio, RSI, EMA21%,
// VWAP%) backtested at ~45-49% hit rate at every horizon tested — no better
// than chance. This version adds two DIFFERENT kinds of confirmation rather
// than just re-tightening the same numbers: today's volume pace vs
// yesterday's (volumeChangePct — a day-over-day comparison, distinct from
// Volume Ratio's candle-over-candle comparison), and price position
// relative to the classic Pivot Point (a support/resistance level, not
// another momentum/oscillator reading). This has NOT itself been
// backtested yet — re-run backtest_strong_weak.js before trusting it.
function evaluateStrongWeakConfluence({ status, turningWeak, volumeRatio, rsi, ema21Pct, vwapPct, volumeChangePct, ltp, pivotPoint }){
  const strongConfluence = status === 'Strong'
    && volumeRatio != null && volumeRatio >= NOTIFY_MIN_VOLUME_RATIO
    && rsi != null && rsi > NOTIFY_RSI_BULLISH
    && ema21Pct != null && ema21Pct >= NOTIFY_MIN_EMA21_MARGIN_PCT
    && vwapPct != null && vwapPct >= NOTIFY_MIN_VWAP_MARGIN_PCT
    && volumeChangePct != null && volumeChangePct > NOTIFY_MIN_VOLUME_CHANGE_PCT
    && ltp != null && pivotPoint != null && ltp > pivotPoint;

  const weakConfluence = status === 'Weak'
    && volumeRatio != null && volumeRatio >= NOTIFY_MIN_VOLUME_RATIO
    && rsi != null && rsi < NOTIFY_RSI_BEARISH
    && ema21Pct != null && ema21Pct <= -NOTIFY_MIN_EMA21_MARGIN_PCT
    && vwapPct != null && vwapPct <= -NOTIFY_MIN_VWAP_MARGIN_PCT
    && volumeChangePct != null && volumeChangePct > NOTIFY_MIN_VOLUME_CHANGE_PCT
    && ltp != null && pivotPoint != null && ltp < pivotPoint;

  const turningWeakConfluence = !!turningWeak
    && volumeRatio != null && volumeRatio >= NOTIFY_MIN_VOLUME_RATIO;

  return { strongConfluence, weakConfluence, turningWeakConfluence };
}

let strongWeakDateKey = null;
let windowFlagged = {};      // symbol -> { status: 'Strong'|'Weak', time: 'HH:MM' } — first qualification during the 9:30-9:50 window, today only
let firstHalfStatusSnapshot = {}; // symbol -> 'Strong'|'Weak'|'Neutral' — status AT the 12:30 boundary, for reversal detection
let firstHalfSnapshotTakenToday = false;

// Telegram notification tracking — separate from windowFlagged (which is
// specifically about the 9:30-9:50 note window). This tracks "has this
// symbol EVER been notified about today, for THIS category" so a
// notification fires exactly once per symbol per category per day, no
// matter how many times per second getStrongWeakPayload() gets called.
let notifiedStrong = {};
let notifiedWeak = {};
let notifiedTurningWeak = {};
let strongNotifyCountToday = 0; // hard daily cap counter, independent of the per-symbol dedup above
let weakNotifyCountToday = 0;
let pendingNotifications = []; // messages queued for server.js to actually send via Telegram
let strongWeakAlertLog = []; // { time, symbol, statusEvent: 'Strong'|'Weak', ltp, volumeChangePct, volumeRatio, ema21Pct, vwapPct, rsi, pivots, dayLow, dayHigh } — one entry per symbol per status per day, same trigger point as Telegram, for the on-page Alert Log table

// Big-jump alert: fires when Vol Change % or Volume Ratio moves by more
// than these amounts from one reading to the next, for the SAME symbol -
// an early-warning signal for a sudden shift in trading activity, before
// (not after) a big price move. Two independently-tunable thresholds since
// the two metrics live on very different scales. Adjust these numbers
// directly based on what you observe in practice - there's no backtest
// behind these starting values, they're reasonable defaults to tune from.
const VOL_CHANGE_JUMP_THRESHOLD_PCT = 50;   // Vol Change % moving by more than 50 percentage points
const VOL_RATIO_JUMP_THRESHOLD = 1.0;       // Volume Ratio moving by more than 1.0x
let previousVolMetrics = {}; // { [symbol]: { volumeChangePct, volumeRatio } } - last reading seen, for detecting a jump

function resetStrongWeakIfNewDay(){
  const { dateKey } = getISTDateKeyAndMinutes();
  if(strongWeakDateKey !== dateKey){
    strongWeakDateKey = dateKey;
    windowFlagged = {};
    firstHalfStatusSnapshot = {};
    firstHalfSnapshotTakenToday = false;
    notifiedStrong = {};
    notifiedWeak = {};
    notifiedTurningWeak = {};
    strongNotifyCountToday = 0;
    weakNotifyCountToday = 0;
    pendingNotifications = [];
    strongWeakAlertLog = [];
    previousVolMetrics = {};
  }
}

// server.js calls this after every getStrongWeakPayload() build, drains
// whatever's queued, and actually sends each one via Telegram (network I/O
// deliberately kept OUT of this module — trend_scanner.js only decides
// WHAT to say, server.js owns HOW it gets sent).
function drainPendingNotifications(){
  const batch = pendingNotifications;
  pendingNotifications = [];
  return batch;
}

function isNear(value, reference, pct){
  if(value == null || reference == null || reference === 0) return false;
  return Math.abs(value - reference) / Math.abs(reference) * 100 <= pct;
}

// Returns 'Strong' | 'Weak' | 'Neutral' for one symbol, given its current LTP,
// today's running day high/low (from server.js's live state), and yesterday's
// day high/low (from the daily candle backfill).
function classifyStrongWeak(ltp, ema9, dayHigh, dayLow, yestHigh, yestLow){
  if(ltp == null || ema9 == null) return 'Neutral';

  const nearDayHigh = dayHigh != null && isNear(ltp, dayHigh, STRONG_WEAK_PROXIMITY_PCT);
  const nearYestHigh = yestHigh != null && (ltp >= yestHigh || isNear(ltp, yestHigh, STRONG_WEAK_PROXIMITY_PCT));
  const nearDayLow = dayLow != null && isNear(ltp, dayLow, STRONG_WEAK_PROXIMITY_PCT);
  const nearYestLow = yestLow != null && (ltp <= yestLow || isNear(ltp, yestLow, STRONG_WEAK_PROXIMITY_PCT));

  if(ltp > ema9 && (nearDayHigh || nearYestHigh)) return 'Strong';
  if(ltp < ema9 && (nearDayLow || nearYestLow)) return 'Weak';
  return 'Neutral';
}

// Ratio of the most recently CLOSED 5-min candle's own traded volume to the
// average per-candle volume across all completed candles today for this
// symbol. >1 means the last candle traded above today's own average pace;
// <1 means below. Needs at least 3 completed candles to be meaningful (a
// ratio computed from only 1-2 candles is too noisy/self-referential to
// trust) — returns null before that, same "warming up" convention used
// elsewhere in this module.
function computeVolumeRatio(candlesArr){
  const withVolume = candlesArr.filter(c => c.volume != null);
  if(withVolume.length < 3) return null;
  const lastVolume = withVolume[withVolume.length - 1].volume;
  const avgVolume = withVolume.reduce((sum, c) => sum + c.volume, 0) / withVolume.length;
  if(avgVolume <= 0) return null;
  return lastVolume / avgVolume;
}

function buildOneStrongWeakRow(symbol, s, minutes, inNoteWindow){
  const ltp = s.ltp;
  if(ltp === null || ltp === undefined) return null;

  const arr5m = candles['5m'][symbol] || [];
  const closes5m = arr5m.map(c => c.close);
  const ema9 = computeEMA(closes5m, STRONG_WEAK_EMA_PERIOD);

  const dailyArr = candles['D'][symbol] || [];
  const yest = dailyArr.length ? dailyArr[dailyArr.length-1] : null;
  const yestHigh = yest ? yest.high : null;
  const yestLow = yest ? yest.low : null;
  const yestVolume = yest ? yest.volume : null;

  const status = classifyStrongWeak(ltp, ema9, s.high, s.low, yestHigh, yestLow);

  // remember the FIRST time this symbol qualifies as Strong/Weak during the
  // 9:30-9:50 note window specifically — once set today, it doesn't get
  // overwritten again even if status flips later in the window or the day
  if(inNoteWindow && (status === 'Strong' || status === 'Weak') && !windowFlagged[symbol]){
    windowFlagged[symbol] = { status, time: timeLabel() };
  }

  // snapshot status at the 12:30 First Half boundary, once per day
  if(!firstHalfSnapshotTakenToday && minutes >= FIRST_HALF_BOUNDARY_MINUTES){
    firstHalfStatusSnapshot[symbol] = status;
  }

  const turningWeak = firstHalfStatusSnapshot[symbol] === 'Strong' && status === 'Weak' && minutes >= FIRST_HALF_BOUNDARY_MINUTES;

  // ---- Volume Ratio, 21 EMA %, VWAP %, RSI — computed here (moved earlier
  // in the function) since the notification confluence check right below
  // needs them, in addition to the table display later on ----
  const ema21 = computeEMA(closes5m, 21);
  const ema21Pct = (ema21 != null && ema21 > 0) ? (ltp - ema21) / ema21 * 100 : null;

  const vwap = getVwap(symbol);
  const vwapPct = (vwap != null && vwap > 0) ? (ltp - vwap) / vwap * 100 : null;

  const rsi = computeRSI(closes5m, RSI_PERIOD);

  const volumeRatio = computeVolumeRatio(arr5m);

  let volumeChangePct = null;
  if(s.volume != null && yestVolume){
    volumeChangePct = (s.volume - yestVolume) / yestVolume * 100;
  }

  // Big-jump alert: compare this reading to the last one seen for this
  // symbol today. Fires independently for each metric (a big Vol Change %
  // move and a big Volume Ratio move are different signals, worth
  // separate alerts). Always updates previousVolMetrics after checking,
  // whether or not a jump fired - so a value that jumps once and then
  // stays elevated doesn't keep re-alerting every tick.
  const prevVol = previousVolMetrics[symbol];
  if(prevVol){
    if(volumeChangePct != null && prevVol.volumeChangePct != null){
      const delta = volumeChangePct - prevVol.volumeChangePct;
      if(Math.abs(delta) >= VOL_CHANGE_JUMP_THRESHOLD_PCT){
        const arrow = delta > 0 ? '📈' : '📉';
        pendingNotifications.push(`${arrow} BIG VOL CHANGE JUMP: ${symbol} — Vol Chg% moved ${delta > 0 ? '+' : ''}${delta.toFixed(1)} points (${prevVol.volumeChangePct.toFixed(1)}% → ${volumeChangePct.toFixed(1)}%) at LTP ${ltp} — ${timeLabel()}`);
      }
    }
    if(volumeRatio != null && prevVol.volumeRatio != null){
      const delta = volumeRatio - prevVol.volumeRatio;
      if(Math.abs(delta) >= VOL_RATIO_JUMP_THRESHOLD){
        const arrow = delta > 0 ? '📈' : '📉';
        pendingNotifications.push(`${arrow} BIG VOLUME RATIO JUMP: ${symbol} — Vol Ratio moved ${delta > 0 ? '+' : ''}${delta.toFixed(2)}x (${prevVol.volumeRatio.toFixed(2)}x → ${volumeRatio.toFixed(2)}x) at LTP ${ltp} — ${timeLabel()}`);
      }
    }
  }
  previousVolMetrics[symbol] = { volumeChangePct, volumeRatio };

  const pivots = yest ? computeClassicPivots(yest.high, yest.low, yest.close) : null;
  const pivotDesc = pivots ? describePivotPosition(ltp, pivots) : '—';

  // 2026-08 redesign: the original confluence recipe (EMA9/EMA21/VWAP/RSI/
  // Volume Ratio all agreeing) backtested at ~45-49% hit rate across every
  // horizon tested (15/30/60min and end-of-day) — statistically no better
  // than a coin flip. Rather than just re-tightening the same numbers, this
  // adds two DIFFERENT kinds of confirmation on top: today's volume pace
  // vs yesterday's (volumeChangePct), and price position relative to the
  // classic Pivot Point — a support/resistance-based signal, not another
  // momentum/oscillator reading like the other four. Re-run
  // backtest_strong_weak.js against this version before trusting it any
  // more than the last one — this has NOT been backtested yet itself.
  const { strongConfluence, weakConfluence, turningWeakConfluence } =
    evaluateStrongWeakConfluence({
      status, turningWeak, volumeRatio, rsi, ema21Pct, vwapPct,
      volumeChangePct, ltp, pivotPoint: pivots ? pivots.pp : null,
    });

  // queue a one-time-per-symbol-per-day Telegram notification the moment
  // each CONFLUENCE condition first becomes true (not just the bare
  // status) — this check-and-mark pattern is what keeps it from re-firing
  // every second for the rest of the day once it's fired once. The
  // per-category counts are also capped, independent of the per-symbol
  // dedup above (that guards against the SAME symbol repeating; this
  // guards against too many DIFFERENT symbols in one day).
  const timeNow = timeLabel();
  if(strongConfluence && !notifiedStrong[symbol] && strongNotifyCountToday < NOTIFY_MAX_PER_CATEGORY_PER_DAY){
    notifiedStrong[symbol] = true;
    strongNotifyCountToday++;
    pendingNotifications.push(`🟢 STRONG (confirmed) [signal #${strongNotifyCountToday} today]: ${symbol} at LTP ${ltp} — above PP ${pivots ? pivots.pp.toFixed(2) : 'N/A'}, Vol Chg +${volumeChangePct.toFixed(1)}%, Vol Ratio ${volumeRatio.toFixed(2)}x, RSI ${rsi.toFixed(1)}, EMA21 +${ema21Pct.toFixed(2)}%, VWAP +${vwapPct.toFixed(2)}% — ${timeNow}`);
    strongWeakAlertLog.push({ time: timeNow, symbol, statusEvent: 'Strong', ltp, volumeChangePct, volumeRatio, ema21Pct, vwapPct, rsi, pivots: pivotDesc, dayLow: s.low, dayHigh: s.high });
  }
  if(weakConfluence && !notifiedWeak[symbol] && weakNotifyCountToday < NOTIFY_MAX_PER_CATEGORY_PER_DAY){
    notifiedWeak[symbol] = true;
    weakNotifyCountToday++;
    pendingNotifications.push(`🔴 WEAK (confirmed) [signal #${weakNotifyCountToday} today]: ${symbol} at LTP ${ltp} — below PP ${pivots ? pivots.pp.toFixed(2) : 'N/A'}, Vol Chg +${volumeChangePct.toFixed(1)}%, Vol Ratio ${volumeRatio.toFixed(2)}x, RSI ${rsi.toFixed(1)}, EMA21 ${ema21Pct.toFixed(2)}%, VWAP ${vwapPct.toFixed(2)}% — ${timeNow}`);
    strongWeakAlertLog.push({ time: timeNow, symbol, statusEvent: 'Weak', ltp, volumeChangePct, volumeRatio, ema21Pct, vwapPct, rsi, pivots: pivotDesc, dayLow: s.low, dayHigh: s.high });
  }
  if(turningWeakConfluence && !notifiedTurningWeak[symbol]){
    // deliberately uncapped — already rare by construction (requires the
    // 12:30 PM snapshot + a full reversal + volume confirmation)
    notifiedTurningWeak[symbol] = true;
    pendingNotifications.push(`⚠️ TURNING WEAK (confirmed): ${symbol} at LTP ${ltp} — was Strong in the first half, now Weak on Vol ${volumeRatio.toFixed(2)}x (reversal watch) — ${timeNow}`);
  }

  return {
    symbol,
    ltp,
    status,
    volumeChangePct,
    pivots: pivotDesc,
    dayLow: s.low, dayHigh: s.high,
    firstFlaggedInWindow: windowFlagged[symbol] ? windowFlagged[symbol].time : null,
    firstFlaggedStatus: windowFlagged[symbol] ? windowFlagged[symbol].status : null,
    turningWeak,
    volumeRatio, ema21Pct, vwapPct, rsi,
  };
}

// `stateRef` is server.js's live per-symbol state object, same as
// getScannerPayload() above — passed in for the same reason (LTP, day
// high/low, and cumulative volume all live there, not in this module).
function getStrongWeakPayload(stateRef){
  resetStrongWeakIfNewDay();
  const { minutes } = getISTDateKeyAndMinutes();
  const inNoteWindow = minutes >= NOTE_WINDOW_START_MINUTES && minutes <= NOTE_WINDOW_END_MINUTES;

  const rows = [];
  Object.keys(stateRef || {}).forEach(symbol => {
    const row = buildOneStrongWeakRow(symbol, stateRef[symbol], minutes, inNoteWindow);
    if(row) rows.push(row);
  });

  if(!firstHalfSnapshotTakenToday && minutes >= FIRST_HALF_BOUNDARY_MINUTES){
    firstHalfSnapshotTakenToday = true;
    console.log(`Strong/Weak scanner: First Half status snapshot taken for ${Object.keys(firstHalfStatusSnapshot).length} symbols at 12:30 boundary.`);
  }

  return {
    strong: rows.filter(r => r.status === 'Strong'),
    weak: rows.filter(r => r.status === 'Weak'),
    turningWeak: rows.filter(r => r.turningWeak),
    all: rows,
    alertLog: strongWeakAlertLog,
  };
}

// ============================================================
// Momentum Scanner — 8-condition mix of daily + 5-min live signals
// ============================================================
// Reference conditions (Market Cap dropped — no live market-cap data source
// exists in this pipeline; relies on the existing F&O-eligible symbol
// universe, which already skews toward larger, more liquid names):
//   1. Price > Open Price (today, live)
//   2. 1 Day Unusual Volume: today's volume-so-far > 2x the 20-day average
//      daily volume (the last 20 COMPLETED days, not including today)
//   3. RSI(14) daily >= 60
//   4. MACD Histogram (daily) >= 0
//   5. EMA(5) > EMA(20), daily
//   6. EMA(20) > EMA(100), daily
//   7. MACD Histogram (5-min) >= 0
//   8. EMA(5) > EMA(20), 5-min
//
// "Daily" indicators are computed using historical daily closes WITH
// today's live LTP appended as the still-forming current day's close —
// matching how a live scanner actually shows daily-timeframe readings
// updating throughout the day, not frozen at yesterday's close.
function buildOneMomentumScannerRow(symbol, s){
  if(s.ltp == null || s.open == null || s.volume == null) return null;

  const dailyArr = candles['D'][symbol] || [];
  const arr5m = candles['5m'][symbol] || [];
  if(dailyArr.length < 100 || arr5m.length < 35) return null; // need 100 for daily EMA100, 35 for 5-min MACD

  const dailyClosesHistorical = dailyArr.map(c => c.close);
  const dailyClosesWithToday = [...dailyClosesHistorical, s.ltp];
  const closes5m = arr5m.map(c => c.close);

  // ---- condition 1: Price > Open ----
  const priceAboveOpen = s.ltp > s.open;

  // ---- condition 2: Unusual Volume (today vs 20-day average, excluding today) ----
  const last20DailyVolumes = dailyArr.slice(-20).map(c => c.volume).filter(v => v != null);
  const avg20DayVolume = last20DailyVolumes.length >= 20
    ? last20DailyVolumes.reduce((a,b) => a+b, 0) / last20DailyVolumes.length
    : null;
  const volumeRatioVsAvg = avg20DayVolume ? s.volume / avg20DayVolume : null;
  const unusualVolume = volumeRatioVsAvg !== null && volumeRatioVsAvg > 2;

  // ---- conditions 3-6: daily RSI/MACD/EMA (using today's live LTP as the current day's close) ----
  const dailyRSI = computeRSI(dailyClosesWithToday, 14);
  const dailyMACD = computeMACDHistogram(dailyClosesWithToday);
  const dailyEMA5 = computeEMA(dailyClosesWithToday, 5);
  const dailyEMA20 = computeEMA(dailyClosesWithToday, 20);
  const dailyEMA100 = computeEMA(dailyClosesWithToday, 100);

  const rsiCondition = dailyRSI !== null && dailyRSI >= 60;
  const macdDailyCondition = dailyMACD !== null && dailyMACD.histogram >= 0;
  const emaDailyCondition = dailyEMA5 !== null && dailyEMA20 !== null && dailyEMA5 > dailyEMA20;
  const emaLongCondition = dailyEMA20 !== null && dailyEMA100 !== null && dailyEMA20 > dailyEMA100;

  // ---- conditions 7-8: 5-min MACD/EMA ----
  const macd5m = computeMACDHistogram(closes5m);
  const ema5_5m = computeEMA(closes5m, 5);
  const ema20_5m = computeEMA(closes5m, 20);

  const macd5mCondition = macd5m !== null && macd5m.histogram >= 0;
  const ema5mCondition = ema5_5m !== null && ema20_5m !== null && ema5_5m > ema20_5m;

  const allConditionsMet = priceAboveOpen && unusualVolume && rsiCondition
    && macdDailyCondition && emaDailyCondition && emaLongCondition
    && macd5mCondition && ema5mCondition;

  if(!allConditionsMet) return null;

  return {
    symbol, ltp: s.ltp, open: s.open,
    volumeRatioVsAvg, rsi: dailyRSI,
    macdHistogramDaily: dailyMACD.histogram,
    ema5Daily: dailyEMA5, ema20Daily: dailyEMA20, ema100Daily: dailyEMA100,
    macdHistogram5m: macd5m.histogram,
    ema5_5m, ema20_5m,
  };
}

// `allowedSymbols`: optional array (or null) — when provided, only these
// symbols are evaluated (used for the Market Cap >= 10,000 Cr proxy filter,
// applied ONLY here, not to any other screener — see server.js's
// momentumScannerSymbols for how this gets loaded). null/undefined means
// "no filter, evaluate every symbol in stateRef" — the original behavior.
function getMomentumScannerPayload(stateRef, allowedSymbols){
  const allowedSet = allowedSymbols ? new Set(allowedSymbols) : null;
  const rows = [];
  Object.keys(stateRef || {}).forEach(symbol => {
    if(allowedSet && !allowedSet.has(symbol)) return;
    const row = buildOneMomentumScannerRow(symbol, stateRef[symbol]);
    if(row) rows.push(row);
  });
  return { matches: rows };
}

// ============================================================
// BTST Scanner — live volume-ratio side only
// ============================================================
// Delivery percentage isn't available server-side at all (it comes from a
// separate NSE report the user downloads and uploads via the Setup page,
// not from Fyers) — so this only computes the volume-ratio half of the
// BTST backtest's two filters. The frontend page cross-references this
// live payload against the browser's own uploaded delivery data to get
// the final, combined qualification.
//
// Matches the backtest's own definition exactly: today's cumulative volume
// so far, divided by the average of the last 10 COMPLETED daily volumes
// (not including today).
function buildOneBtstVolumeRow(symbol, s){
  if(s.ltp == null || s.volume == null) return null;
  const dailyArr = candles['D'][symbol] || [];
  if(dailyArr.length < 10) return null;

  const recentVolumes = dailyArr.slice(-10).map(c => c.volume).filter(v => v != null);
  if(recentVolumes.length < 10) return null;
  const avgDailyVolume = recentVolumes.reduce((a,b) => a+b, 0) / recentVolumes.length;
  const volumeRatio = avgDailyVolume > 0 ? s.volume / avgDailyVolume : null;
  if(volumeRatio === null) return null;

  return { symbol, ltp: s.ltp, volumeRatio };
}

function getBtstVolumeRatioPayload(stateRef){
  const rows = [];
  Object.keys(stateRef || {}).forEach(symbol => {
    const row = buildOneBtstVolumeRow(symbol, stateRef[symbol]);
    if(row) rows.push(row);
  });
  return { rows };
}

// ============================================================
// Narrow CPR (Next-Day) — matches the exact formula validated in
// backtest_narrow_cpr.js: today's CPR width > 10x tomorrow's PROJECTED
// CPR width (computed from today's still-forming H/L/C), price 500-10000.
// "Tomorrow's projected CPR" genuinely changes throughout the day as
// today's H/L/C evolves - this is intentional, matching how the backtest
// itself defines the signal, and only becomes FINAL once today's candle
// closes at 3:30 PM (see server.js's checkAndRunNarrowCprLock).
// ============================================================
const NARROW_CPR_PRICE_MIN = 500, NARROW_CPR_PRICE_MAX = 10000;
const NARROW_CPR_WIDTH_RATIO_THRESHOLD = 10;

function computeCPR(dayCandle){
  const pivot = (dayCandle.high + dayCandle.low + dayCandle.close) / 3;
  const bc = (dayCandle.high + dayCandle.low) / 2;
  const tc = 2*pivot - bc;
  const width = Math.abs(tc - bc);
  return { pivot, bc, tc, width };
}

function buildOneNarrowCprRow(symbol, s){
  if(s.ltp == null || s.high == null || s.low == null || s.open == null) return null;
  if(s.ltp <= NARROW_CPR_PRICE_MIN || s.ltp >= NARROW_CPR_PRICE_MAX) return null;

  const dailyArr = candles['D'][symbol] || [];
  if(dailyArr.length < 1) return null; // need at least 1 completed daily candle - only "yesterday" is ever read below

  const yesterday = dailyArr[dailyArr.length - 1]; // most recent COMPLETED daily candle
  const todayCPR = computeCPR(yesterday); // "today's" own CPR, from yesterday's H/L/C

  // "tomorrow's" PROJECTED CPR, from TODAY's still-forming H/L/C (updates live all day)
  const todaySoFar = { high: s.high, low: s.low, close: s.ltp };
  const tomorrowCPR = computeCPR(todaySoFar);

  if(todayCPR.width <= tomorrowCPR.width * NARROW_CPR_WIDTH_RATIO_THRESHOLD) return null;

  return {
    symbol, ltp: s.ltp,
    todayWidth: todayCPR.width,
    tomorrowTC: tomorrowCPR.tc, tomorrowBC: tomorrowCPR.bc, tomorrowPivot: tomorrowCPR.pivot,
    tomorrowWidthPct: (tomorrowCPR.tc - tomorrowCPR.bc) / tomorrowCPR.pivot * 100,
  };
}

function getNarrowCprPayload(stateRef){
  const rows = [];
  Object.keys(stateRef || {}).forEach(symbol => {
    const row = buildOneNarrowCprRow(symbol, stateRef[symbol]);
    if(row) rows.push(row);
  });
  return { rows };
}

// ============================================================
// Narrow Camarilla — matches the exact formula validated in
// backtest_narrow_camarilla.js: today's Camarilla range (R3/S3/R4/S4,
// computed from today's still-forming H/L/C) must sit FULLY INSIDE
// yesterday's (the most recent completed daily candle), on all four
// levels at once. Backtest found this the most trustworthy of the three
// "narrow range" approaches tested - only ~8% of days were genuinely
// unresolvable intraday, vs ~52% for the CPR versions. Recommended trade:
// 1% target / 0.5% stop, entry at whichever of R3/S3 breaks first.
// ============================================================
function computeCamarilla(h, l, c){
  const rng = h - l;
  return {
    r4: c + rng*1.1/2,
    r3: c + rng*1.1/4,
    s3: c - rng*1.1/4,
    s4: c - rng*1.1/2,
  };
}

function buildOneNarrowCamarillaRow(symbol, s){
  if(s.ltp == null || s.high == null || s.low == null) return null;

  const dailyArr = candles['D'][symbol] || [];
  if(dailyArr.length < 1) return null; // need at least 1 completed daily candle ("yesterday")

  const yesterday = dailyArr[dailyArr.length - 1];
  if(yesterday.high <= 0 || yesterday.low <= 0 || yesterday.close <= 0) return null;
  const camYesterday = computeCamarilla(yesterday.high, yesterday.low, yesterday.close);

  const todaySoFar = { high: s.high, low: s.low, close: s.ltp };
  if(todaySoFar.high <= 0 || todaySoFar.low <= 0 || todaySoFar.close <= 0) return null;
  const camToday = computeCamarilla(todaySoFar.high, todaySoFar.low, todaySoFar.close);

  const cond1 = camToday.r3 < camYesterday.r3;
  const cond2 = camToday.s3 > camYesterday.s3;
  const cond3 = camToday.r4 < camYesterday.r4;
  const cond4 = camToday.s4 > camYesterday.s4;
  if(!(cond1 && cond2 && cond3 && cond4)) return null;

  const todayInnerRange = camToday.r3 - camToday.s3;
  const yesterdayInnerRange = camYesterday.r3 - camYesterday.s3;
  const shrinkPct = yesterdayInnerRange > 0 ? (yesterdayInnerRange - todayInnerRange) / yesterdayInnerRange * 100 : 0;

  return { symbol, ltp: s.ltp, r3: camToday.r3, s3: camToday.s3, r4: camToday.r4, s4: camToday.s4, shrinkPct };
}

function getNarrowCamarillaPayload(stateRef){
  const rows = [];
  Object.keys(stateRef || {}).forEach(symbol => {
    const row = buildOneNarrowCamarillaRow(symbol, stateRef[symbol]);
    if(row) rows.push(row);
  });
  return { rows };
}

// ============================================================
// Top-3-Losers-at-9:16, Loser #2 short — matches the exact formula
// validated in backtest_top_losers_916.js (71-day, +0.311% EV, the
// second-strongest confirmed edge of the whole day's testing):
//   - At 9:16 AM, rank every stock by (open - ltp)/open*100 (biggest
//     drop-from-open first). The #2 biggest dropper is the actionable one.
//   - Entry (short) = that stock's 9:16 price
//   - Stop = today's open (the opposite side)
//   - Target = entry - (open - entry), i.e. 1:1, extending further down
//   - Exit at 9:30 AM if neither is hit (handled by whoever is watching
//     live - this function only identifies the setup, it doesn't manage
//     the trade's later 9:30 exit)
// This is a ONE-TIME-PER-DAY ranking, unlike the other live scanners -
// called once by server.js at/after 9:16 AM, not on every tick.
// ============================================================
function computeTop3LosersAt916(stateRef){
  const drops = [];
  Object.keys(stateRef || {}).forEach(symbol => {
    const s = stateRef[symbol];
    if(s.ltp == null || s.open == null || s.open <= 0) return;
    const dropPct = (s.open - s.ltp) / s.open * 100;
    drops.push({ symbol, open: s.open, price916: s.ltp, dropPct });
  });
  drops.sort((a, b) => b.dropPct - a.dropPct); // biggest drop first

  const top3 = drops.slice(0, 3).map((d, i) => {
    const rank = i + 1;
    const riskDistance = d.open - d.price916; // always positive by construction
    const target = d.price916 - riskDistance; // 1:1, extending further down (short)
    return {
      rank, symbol: d.symbol, dropPct: d.dropPct,
      open: d.open, entryPrice: d.price916, stopPrice: d.open, targetPrice: target,
      actionable: rank === 2, // Loser #2 specifically is the backtested, actionable one
    };
  });
  return { rows: top3 };
}

module.exports = {
  processTick,
  backfillHistory,
  getScannerPayload,
  getStrongWeakPayload,
  getMomentumScannerPayload,
  getBtstVolumeRatioPayload,
  getNarrowCprPayload,
  getNarrowCamarillaPayload,
  computeTop3LosersAt916,
  drainPendingNotifications,
  // Exported specifically so backtest_strong_weak.js can reuse the EXACT
  // same pure math/classification functions the live app uses — a backtest
  // that reimplemented this logic separately could silently drift out of
  // sync with production and give misleading results.
  computeEMA,
  computeMACDHistogram,
  computeRSI,
  computeVolumeRatio,
  classifyStrongWeak,
  computeClassicPivots,
  describePivotPosition,
  evaluateStrongWeakConfluence,
  NOTIFY_MIN_VOLUME_RATIO,
  NOTIFY_RSI_BULLISH,
  NOTIFY_RSI_BEARISH,
  NOTIFY_MIN_EMA21_MARGIN_PCT,
  NOTIFY_MIN_VWAP_MARGIN_PCT,
  NOTIFY_MIN_VOLUME_CHANGE_PCT,
  NOTIFY_MAX_PER_CATEGORY_PER_DAY,
};
