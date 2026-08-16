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

function updateIntradayCandle(timeframe, timeframeSeconds, symbol, price, epochSeconds){
  ensureCandleStore(timeframe, symbol);
  const bStart = bucketStart(epochSeconds, timeframeSeconds);
  const cur = building[timeframe][symbol];

  if(!cur || cur.time !== bStart){
    // a new bucket started — the previous in-progress candle (if any) is now closed
    if(cur){
      candles[timeframe][symbol].push(cur);
      if(candles[timeframe][symbol].length > MAX_CANDLES) candles[timeframe][symbol].shift();
    }
    building[timeframe][symbol] = { time: bStart, open: price, high: price, low: price, close: price };
  } else {
    cur.high = Math.max(cur.high, price);
    cur.low = Math.min(cur.low, price);
    cur.close = price;
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
  updateIntradayCandle('5m', 300, symbol, ltp, epochSeconds);
  updateIntradayCandle('15m', 900, symbol, ltp, epochSeconds);
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
async function fetchOneHistory(fyers, symbol, resolution, rangeFrom, rangeTo){
  const data = { symbol, resolution, date_format: '0', range_from: String(rangeFrom), range_to: String(rangeTo), cont_flag: '1' };
  try{
    const resp = await withTimeout(fyers.history(data), HISTORY_CALL_TIMEOUT_MS, `${symbol} ${resolution}`);
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
async function backfillHistory(fyers, symbols){
  const nowSeconds = Math.floor(Date.now()/1000);
  const sixtyDaysAgo = nowSeconds - 60*24*60*60;

  const { epochSeconds } = getISTDateKeyAndMinutes();
  const istOffsetSeconds = 5.5*60*60;
  const istNow = epochSeconds + istOffsetSeconds;
  const marketOpenIstToday = Math.floor(istNow/86400)*86400 + 9*3600 + 15*60;
  const todayRangeFrom = marketOpenIstToday - istOffsetSeconds;

  let dailyOkCount = 0, dailyFailCount = 0, m15OkCount = 0, m15FailCount = 0;

  for(const symbol of symbols){
    // daily candles
    const dailyResp = await fetchOneHistory(fyers, symbol, 'D', sixtyDaysAgo, nowSeconds);
    if(dailyResp && dailyResp.s === 'ok' && Array.isArray(dailyResp.candles)){
      ensureCandleStore('D', symbol);
      candles['D'][symbol] = dailyResp.candles.map(c => ({
        time: c[0], open: c[1], high: c[2], low: c[3], close: c[4],
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
      } else {
        m15FailCount++;
      }
      await sleep(BACKFILL_DELAY_MS);
    }
  }

  console.log(`Trend scanner backfill detail: daily ${dailyOkCount} ok / ${dailyFailCount} failed, 15m ${m15OkCount} ok / ${m15FailCount} failed (out of ${symbols.length} symbols).`);
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

module.exports = {
  processTick,
  backfillHistory,
  getScannerPayload,
};
