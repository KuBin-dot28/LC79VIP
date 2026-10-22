'use strict';

try { require('dotenv').config(); } catch (_) { /* Environment variables may be supplied by the host instead. */ }

const express = require('express');
const axios = require('axios');
const crypto = require('crypto');
const path = require('path');
const fs = require('fs');
const { io } = require('socket.io-client');

const app = express();
app.disable('x-powered-by');
app.use(express.json({ limit: '32kb' }));
app.use('/assets', express.static(path.join(__dirname, 'public'), { etag: true, maxAge: '5m' }));

const PORT = Number(process.env.PORT || 3000);
const GAME_ORIGIN = String(process.env.GAME_ORIGIN || 'https://wtxmd52.tele68.com').replace(/\/$/, '');
const GAME_NAMESPACE = process.env.GAME_NAMESPACE || '/txmd5';
const SOCKET_PATH = process.env.SOCKET_PATH || '/txmd5/';
const LOGIN_URL = process.env.LOGIN_URL || 'https://apifo88daigia.tele68.com/api';
const LOBBY_URL = process.env.LOBBY_URL || 'https://wlb.tele68.com/v1/lobby/auth/login?cp=R&cl=R&pf=web&at=';
const DATA_DIR = path.resolve(process.env.DATA_DIR || path.join(__dirname, 'data'));
const DATA_FILE = path.join(DATA_DIR, 'lc79-auto-state.json');
const MAX_HISTORY = 2000;
const MAX_PLAYER_HISTORY = 500;
const MAX_BET = 100_000_000;
const GLOBAL_HISTORY = [];
const HISTORY_KEYS = new Set();
const PLAYERS = new Map();
const SESSIONS = new Map();
let COLLECTOR = null;
let collectorSessionId = null;

const DEEP = { enable_smart_capital: true, smart_cap_max_boost: 1.3 };

function md5(value) {
  return crypto.createHash('md5').update(String(value), 'utf8').digest('hex');
}
function clampNumber(value, min, max, fallback) {
  const number = Number(value);
  return Number.isFinite(number) ? Math.min(max, Math.max(min, number)) : fallback;
}
function toSideString(history) {
  return history.map((value) => value === 'TAI' ? 'T' : 'X').join('');
}

/**
 * Thuật toán soi cầu VIP nâng cấp:
 * 1. Phân tích ngữ cảnh Markov động (Context Depth 2..8) với Laplace Smoothing.
 * 2. Nhận diện bệt/cầu bệt (Streak Detection) & chống bẻ cầu bệt sớm.
 * 3. Phân tích chu kỳ dao động (Symmetry / Alternating Pattern Detection - Cầu 1-1, 2-2).
 * 4. Suy luận xác suất tổng hợp theo mô hình Bayes có trọng số suy giảm thời gian (Exponential Decay Weighting).
 */
function makePrediction() {
  const sides = toSideString(GLOBAL_HISTORY.slice(-MAX_HISTORY));
  const n = sides.length;
  
  if (n < 15) {
    return { 
      prediction: null, 
      confidence: 0, 
      patternType: 'normal', 
      boost: 1, 
      reason: `Cần thêm dữ liệu lịch sử (${n}/15 kết quả)` 
    };
  }

  // 1. Baseline Tần suất gần đây với Suy giảm theo thời gian (Recent Weighted Frequency)
  const recentWindow = Math.min(80, n);
  const recent = sides.slice(-recentWindow);
  let weightedTai = 2;
  let weightedTotal = 4;
  
  for (let i = 0; i < recent.length; i++) {
    const weight = 0.5 + Math.pow((i + 1) / recent.length, 1.5) * 1.2;
    if (recent[i] === 'T') weightedTai += weight;
    weightedTotal += weight;
  }
  const baselineTai = weightedTai / weightedTotal;

  // 2. Phát hiện Chuỗi bệt hiện tại (Current Streak Filter)
  let currentStreakLen = 0;
  const lastChar = sides[n - 1];
  for (let i = n - 1; i >= 0; i--) {
    if (sides[i] === lastChar) currentStreakLen++;
    else break;
  }

  // 3. Phân tích Markov Context (Ngữ cảnh 2 -> 8 kết quả) với Lọc nhiễu Laplace
  let markovWeightedProb = baselineTai * 2.0;
  let markovTotalWeight = 2.0;
  let totalMatchesFound = 0;
  let bestPattern = null;
  let maxPatternScore = 0;

  const maxContext = Math.min(8, Math.floor(n / 3));
  for (let length = 2; length <= maxContext; length++) {
    const context = sides.slice(-length);
    let tai = 0;
    let xiu = 0;
    let matches = 0;
    const cutoff = n - length;

    for (let i = length; i < cutoff; i++) {
      if (sides.slice(i - length, i) !== context) continue;
      if (sides[i] === 'T') tai++;
      else xiu++;
      matches++;
    }

    if (matches < 2) continue;

    // Smoothing Laplace (k=1)
    const posteriorTai = (tai + 1) / (matches + 2);
    // Trọng số mô hình tăng theo độ dài chuỗi khớp và số lượng mẫu
    const patternWeight = Math.sqrt(matches) * Math.pow(1.25, length);
    
    markovWeightedProb += posteriorTai * patternWeight;
    markovTotalWeight += patternWeight;
    totalMatchesFound += matches;

    const patternScore = matches * length;
    if (patternScore > maxPatternScore) {
      maxPatternScore = patternScore;
      bestPattern = { length, matches, tai, xiu, posteriorTai };
    }
  }

  const finalProbTai = markovWeightedProb / markovTotalWeight;
  let rawPrediction = finalProbTai >= 0.5 ? 'TAI' : 'XIU';
  
  // 4. Bỏ qua nếu lệch không đủ lớn (Lọc tín hiệu nhiễu)
  let edge = Math.abs(finalProbTai - 0.5);
  let minimumEdge = 0.052;

  // Xử lý logic chống bẻ bệt: Nếu bệt dài >= 5, ưu tiên bám bệt trừ khi mô hình có độ tin cậy vượt trội
  let isStreakMode = false;
  if (currentStreakLen >= 5) {
    const streakSide = lastChar === 'T' ? 'TAI' : 'XIU';
    if (rawPrediction !== streakSide && edge < 0.12) {
      rawPrediction = streakSide; // Bám bệt thay vì bẻ
      isStreakMode = true;
      edge += 0.05;
    }
  }

  if (edge < minimumEdge) {
    return {
      prediction: null,
      confidence: Math.round(50 + edge * 100),
      patternType: bestPattern ? `context-${bestPattern.length}` : 'normal',
      boost: 1,
      reason: `Tín hiệu chưa đủ mạnh (Độ lệch ${(edge * 100).toFixed(1)}% < ${(minimumEdge * 100).toFixed(1)}%)`,
    };
  }

  // Tính điểm tự tin (Confidence)
  const supportBonus = Math.min(8, Math.floor(totalMatchesFound / 4));
  const confidence = Math.min(88, Math.round(52 + edge * 105 + supportBonus));
  
  const patternType = isStreakMode 
    ? `streak-follow-${currentStreakLen}` 
    : (bestPattern ? `pattern-${bestPattern.length}` : 'frequency-weighted');

  let reason = '';
  if (isStreakMode) {
    reason = `Cầu bệt ${currentStreakLen} tay (${lastChar === 'T' ? 'Tài' : 'Xỉu'}): Theo xu hướng bệt an toàn`;
  } else if (bestPattern) {
    reason = `Mẫu ${bestPattern.length} ký tự khớp ${bestPattern.matches} lần; Tỷ lệ nổ Tài ${(bestPattern.posteriorTai * 100).toFixed(0)}%`;
  } else {
    reason = `Phân tích tần suất có trọng số (${recentWindow} phiên gần nhất); baseline Tài ${(baselineTai * 100).toFixed(0)}%`;
  }

  // Đề xuất tăng cược linh hoạt dựa vào độ tự tin
  let boost = 1;
  if (confidence >= 75 && totalMatchesFound >= 8) boost = 1.3;
  else if (confidence >= 68 && totalMatchesFound >= 5) boost = 1.15;

  return {
    prediction: rawPrediction,
    confidence,
    patternType,
    boost,
    reason,
  };
}

async function loginAndGetToken(username, password) {
  try {
    const loginUrl = new URL(LOGIN_URL);
    loginUrl.searchParams.set('c', '3');
    loginUrl.searchParams.set('un', username);
    loginUrl.searchParams.set('pw', md5(password));
    loginUrl.searchParams.set('cp', 'R');
    loginUrl.searchParams.set('cl', 'R');
    loginUrl.searchParams.set('pf', 'web');
    loginUrl.searchParams.set('at', '');
    const response = await axios.get(loginUrl.toString(), { timeout: 15000 });
    const data = response.data;
    if (!data || !data.success) return { _error: `Đăng nhập game thất bại: ${data?.message || 'Sai thông tin hoặc máy chủ từ chối'}` };
    if (!data.sessionKey || !data.accessToken) return { _error: 'Phản hồi đăng nhập thiếu sessionKey/accessToken' };
    const encoded = data.sessionKey + '='.repeat((4 - (data.sessionKey.length % 4)) % 4);
    const decoded = JSON.parse(Buffer.from(encoded, 'base64').toString('utf8'));
    const nickname = decoded.nickname || decoded.nickName;
    if (!nickname) return { _error: 'Không đọc được nickname từ sessionKey' };
    const lobbyUrl = LOBBY_URL;
    const lobbyResponse = await axios.post(lobbyUrl, { nickName: nickname, accessToken: data.accessToken }, {
      headers: { 'content-type': 'application/json' }, timeout: 15000,
    });
    const token = lobbyResponse.data?.token;
    if (!token) return { _error: 'Máy chủ lobby không trả token xác thực' };
    return { token, nickname, username, money: Number(lobbyResponse.data?.remoteLoginResp?.money || 0) };
  } catch (error) {
    const message = error.response?.data?.message || error.message || 'Lỗi không xác định';
    return { _error: `Lỗi kết nối đăng nhập: ${String(message).slice(0, 140)}` };
  }
}

function pushHistoryOnce(roundId, result) {
  if (!['TAI', 'XIU'].includes(result)) return;
  const key = String(roundId || `unknown-${Date.now()}-${result}`);
  if (HISTORY_KEYS.has(key)) return;
  HISTORY_KEYS.add(key);
  GLOBAL_HISTORY.push(result);
  if (GLOBAL_HISTORY.length > MAX_HISTORY) GLOBAL_HISTORY.shift();
  savePersistentState();
  if (HISTORY_KEYS.size > MAX_HISTORY * 3) {
    const trimmed = Array.from(HISTORY_KEYS).slice(-MAX_HISTORY * 2);
    HISTORY_KEYS.clear();
    for (const item of trimmed) HISTORY_KEYS.add(item);
  }
}

function initPlayer(id, login) {
  return {
    id,
    token: login.token,
    nickname: login.nickname,
    loginName: login.username || login.loginName || null,
    money: Number(login.money || 0),
    connected: false,
    connecting: true,
    error: null,
    sock: null,
    createdAt: Date.now(),
    state: {
      sessionId: null,
      currentPrediction: null,
      lastConfidence: 0,
      lastPatternType: 'normal',
      predictionReason: 'Đang chờ dữ liệu lịch sử',
      smartCapitalBoost: 1,
      autoBet: false,
      betAmount: 10000,
      hasBetThisSession: false,
      waitingForResult: false,
      wins: 0,
      losses: 0,
      profitLoss: 0,
      winStreak: 0,
      x2Enabled: false,
      x2Mode: 'mode1',
      x2Multiplier: 1,
      autoCapitalEnabled: false,
      autoInitialCapital: 0,
      autoCurrentCapital: 0,
      autoLevel: 1,
      autoMaxLevel: 7,
      autoRiskMode: 'balanced',
      autoStopLoss: 0,
      targetProfit: 0,
      autoSessionCount: 0,
      autoWinCount: 0,
      autoLoseCount: 0,
      skippedSignals: 0,
      history: [],
      lastRoundKey: null,
    },
  };
}

let persistTimer = null;
function playerForDisk(player) {
  return {
    id: player.id,
    token: player.token,
    nickname: player.nickname,
    loginName: player.loginName || null,
    money: Number(player.money) || 0,
    createdAt: player.createdAt,
    lastNotice: player.lastNotice || '',
    lastResultNotice: player.lastResultNotice || '',
    state: player.state,
  };
}

function writePersistentStateSync() {
  try {
    fs.mkdirSync(DATA_DIR, { recursive: true });
    const payload = {
      version: 1,
      savedAt: new Date().toISOString(),
      globalHistory: GLOBAL_HISTORY.slice(-MAX_HISTORY),
      historyKeys: Array.from(HISTORY_KEYS).slice(-MAX_HISTORY * 2),
      players: Array.from(PLAYERS.values()).map(playerForDisk),
      sessions: Array.from(SESSIONS.entries()).slice(-5000),
    };
    const temp = `${DATA_FILE}.tmp`;
    fs.writeFileSync(temp, JSON.stringify(payload), { mode: 0o600 });
    fs.renameSync(temp, DATA_FILE);
    try { fs.chmodSync(DATA_FILE, 0o600); } catch (_) {}
  } catch (error) {
    console.error(`Không thể lưu dữ liệu tự động: ${error.message}`);
  }
}

function savePersistentState() {
  if (persistTimer) clearTimeout(persistTimer);
  persistTimer = setTimeout(() => {
    persistTimer = null;
    writePersistentStateSync();
  }, 150);
  if (typeof persistTimer.unref === 'function') persistTimer.unref();
}

function loadPersistentState() {
  if (!fs.existsSync(DATA_FILE)) return;
  try {
    const saved = JSON.parse(fs.readFileSync(DATA_FILE, 'utf8'));
    if (Array.isArray(saved.globalHistory)) GLOBAL_HISTORY.push(...saved.globalHistory.filter(x => x === 'TAI' || x === 'XIU').slice(-MAX_HISTORY));
    if (Array.isArray(saved.historyKeys)) saved.historyKeys.slice(-MAX_HISTORY * 2).forEach(key => HISTORY_KEYS.add(String(key)));
    if (Array.isArray(saved.sessions)) {
      for (const entry of saved.sessions.slice(-5000)) {
        if (Array.isArray(entry) && entry.length === 2 && entry[1] && entry[1].chatId) SESSIONS.set(String(entry[0]), entry[1]);
      }
    }
    if (Array.isArray(saved.players)) {
      for (const record of saved.players) {
        if (!record || !record.id || !record.token || !record.nickname) continue;
        const player = initPlayer(String(record.id), { token: record.token, nickname: record.nickname, username: record.loginName || null, money: record.money });
        const dataState = record.state && typeof record.state === 'object' ? record.state : {};
        Object.assign(player.state, dataState);
        if (!Array.isArray(player.state.history)) player.state.history = [];
        player.state.history = player.state.history.slice(0, MAX_PLAYER_HISTORY);
        player.loginName = record.loginName || null;
        player.connected = false;
        player.connecting = true;
        player.error = 'Đang khôi phục kết nối sau khi máy chủ khởi động lại';
        player.createdAt = Number(record.createdAt) || Date.now();
        player.lastNotice = String(record.lastNotice || '');
        player.lastResultNotice = String(record.lastResultNotice || '');
        PLAYERS.set(player.id, player);
      }
    }
    console.log(`Đã khôi phục ${PLAYERS.size} phiên, ${GLOBAL_HISTORY.length} kết quả lịch sử từ ${DATA_FILE}`);
  } catch (error) {
    console.error(`Không đọc được dữ liệu lưu trước đó: ${error.message}`);
  }
}

function calcX2Multiplier(state) {
  if (!state.x2Enabled) return 1;
  const wins = state.winStreak;
  if (state.x2Mode === 'mode1') return wins >= 1 ? 2 : 1;
  if (state.x2Mode === 'mode2') return wins >= 2 ? 2 : 1;
  if (state.x2Mode === 'mode3') return wins <= 0 ? 1 : wins === 1 ? 2 : wins === 2 ? 4 : 8;
  if (state.x2Mode === 'mode4') return wins >= 3 ? 2 : 1;
  return 1;
}

function calcAutoCapitalBet(state) {
  const capital = Math.max(0, Number(state.autoCurrentCapital) || 0);
  if (!state.autoCapitalEnabled || capital <= 0) return state.betAmount;
  let basePercent;
  let martingaleFactor;
  if (state.autoRiskMode === 'antoan') { basePercent = 0.008; martingaleFactor = 1.8; }
  else if (state.autoRiskMode === 'manh') { basePercent = 0.02; martingaleFactor = 2.2; }
  else { basePercent = 0.012; martingaleFactor = 2; }
  
  const boost = Math.min(DEEP.smart_cap_max_boost, Math.max(1, state.smartCapitalBoost || 1));
  basePercent *= boost;
  
  const unit = Math.max(1000, Math.floor(capital * basePercent / 1000) * 1000);
  const level = Math.min(state.autoLevel, state.autoMaxLevel);
  let bet = unit;
  for (let i = 1; i < level; i++) bet = Math.floor(bet * martingaleFactor);
  bet = Math.max(1000, Math.floor(bet / 1000) * 1000);
  const maxBet = Math.floor((capital * (0.35 + (boost - 1) * 0.02)) / 1000) * 1000;
  return Math.max(0, Math.min(bet, maxBet, Math.floor(capital / 1000) * 1000));
}

function calcCurrentBet(state) {
  if (state.autoCapitalEnabled) return calcAutoCapitalBet(state);
  state.x2Multiplier = calcX2Multiplier(state);
  return Math.min(MAX_BET, Math.max(1000, Math.floor((state.betAmount * state.x2Multiplier) / 1000) * 1000));
}

function stopAllAuto(player, reason) {
  const state = player.state;
  state.autoBet = false;
  state.x2Enabled = false;
  state.x2Multiplier = 1;
  state.autoCapitalEnabled = false;
  player.lastNotice = reason;
  savePersistentState();
}

function onSessionResult(player, data) {
  const state = player.state;
  const result = data?.resultTruyenThong;
  const roundId = data?.id ?? data?.sessionId ?? state.sessionId;
  if (result === 'TAI' || result === 'XIU') pushHistoryOnce(roundId, result);

  const resolvedSessionId = roundId == null ? state.sessionId : String(roundId);
  let sessionKey = `${player.id}:${String(resolvedSessionId)}`;
  let ticket = SESSIONS.get(sessionKey);
  
  if (!ticket) {
    const pending = [...SESSIONS.entries()].filter(([, value]) => value.chatId === player.id && !value.processed);
    if (pending.length === 1) [sessionKey, ticket] = pending[0];
  }
  if (!ticket || ticket.processed || (result !== 'TAI' && result !== 'XIU')) return;
  ticket.processed = true;

  const won = ticket.prediction === result;
  const profit = won ? Math.floor(ticket.amount * 0.98) : -ticket.amount;
  if (won) {
    state.wins++;
    state.winStreak++;
    state.profitLoss += profit;
    if (state.autoCapitalEnabled) {
      state.autoCurrentCapital += profit;
      state.autoWinCount++;
      state.autoLevel = 1;
    }
  } else {
    state.losses++;
    state.winStreak = 0;
    state.profitLoss -= ticket.amount;
    if (state.autoCapitalEnabled) {
      state.autoCurrentCapital = Math.max(0, state.autoCurrentCapital - ticket.amount);
      state.autoLoseCount++;
      state.autoLevel = Math.min(state.autoMaxLevel + 1, state.autoLevel + 1);
    }
    if (state.x2Enabled && state.x2Mode === 'mode1') state.x2Enabled = false;
  }
  state.autoSessionCount++;
  state.x2Multiplier = calcX2Multiplier(state);
  state.history.unshift({
    sessionId: ticket.sessionId,
    prediction: ticket.prediction,
    result,
    betAmount: ticket.amount,
    profit,
    isWin: won,
    confidence: ticket.confidence,
    patternType: ticket.patternType,
    dices: Array.isArray(data?.dices) ? data.dices : [],
    settledAt: Date.now(),
    balanceAfter: Number(player.money) || 0,
  });
  if (state.history.length > MAX_PLAYER_HISTORY) state.history.pop();
  state.waitingForResult = false;
  ticket.result = result;
  ticket.profit = profit;
  ticket.isWin = won;

  const target = Number(state.targetProfit) || 0;
  if (target > 0 && state.profitLoss >= target) stopAllAuto(player, 'Đã đạt mục tiêu lãi — tự động dừng');
  if (state.autoCapitalEnabled) {
    const floor = Number(state.autoStopLoss) || 0;
    if (state.autoCurrentCapital <= 0 || (floor > 0 && state.autoCurrentCapital <= floor)) {
      stopAllAuto(player, 'Đã chạm mức dừng lỗ/vốn — tự động dừng');
    }
  }
  player.lastResultNotice = `${won ? 'THẮNG' : 'THUA'} phiên #${ticket.sessionId}: ${profit > 0 ? '+' : ''}${profit}`;
  savePersistentState();
  if (SESSIONS.size > 5000) {
    for (const [key, oldTicket] of SESSIONS.entries()) {
      if (oldTicket.processed) SESSIONS.delete(key);
      if (SESSIONS.size <= 4000) break;
    }
  }
}

function attachPlayerSocket(player) {
  const id = player.id;
  const sock = io(`${GAME_ORIGIN}${GAME_NAMESPACE.startsWith('/') ? GAME_NAMESPACE : `/${GAME_NAMESPACE}`}`, {
    path: SOCKET_PATH,
    transports: ['websocket'],
    auth: { token: player.token },
    reconnection: true,
    reconnectionAttempts: Infinity,
    reconnectionDelay: 2000,
    reconnectionDelayMax: 15000,
    timeout: 20000,
    autoConnect: false,
    extraHeaders: { 'User-Agent': 'Mozilla/5.0' },
  });
  player.sock = sock;

  sock.on('connect', () => {
    player.connected = true;
    player.connecting = false;
    player.error = null;
    console.log(`[${id}] Socket connected namespace=${GAME_NAMESPACE} path=${SOCKET_PATH}`);
  });
  sock.on('disconnect', (reason) => {
    player.connected = false;
    player.connecting = true;
    player.error = `Mất kết nối: ${reason}`;
    console.warn(`[${id}] Socket disconnected: ${reason}`);
  });
  sock.on('connect_error', (error) => {
    player.connected = false;
    player.connecting = false;
    player.error = error?.message || 'Socket.IO connect_error không rõ nguyên nhân';
    console.error(`[${id}] connect_error: ${player.error}`);
  });
  sock.on('new-session', (data = {}) => {
    try {
      const state = player.state;
      state.sessionId = String(data.id ?? data.sessionId ?? data.roundId ?? 'N/A');
      state.hasBetThisSession = false;
      state.waitingForResult = false;
      const target = Number(state.targetProfit) || 0;
      if (target > 0 && state.profitLoss >= target) {
        stopAllAuto(player, 'Đã đạt mục tiêu lãi — tự động dừng');
      }
      const prediction = makePrediction();
      state.currentPrediction = prediction.prediction;
      state.lastConfidence = prediction.confidence || 0;
      state.lastPatternType = prediction.patternType || 'normal';
      state.predictionReason = prediction.reason || '';
      state.smartCapitalBoost = DEEP.enable_smart_capital ? Math.min(DEEP.smart_cap_max_boost, prediction.boost || 1) : 1;
      state.currentBet = calcCurrentBet(state);
      savePersistentState();
      console.log(`[${id}] Phiên #${state.sessionId} prediction=${state.currentPrediction || 'SKIP'} confidence=${state.lastConfidence}%`);
    } catch (error) {
      player.error = `Lỗi xử lý phiên mới: ${error.message}`;
      console.error(`[${id}] new-session error:`, error);
    }
  });
  sock.on('tick-update', (data = {}) => {
    const state = player.state;
    if (data.state !== 'BETTING' || !state.autoBet || !state.currentPrediction || state.hasBetThisSession || !player.connected) return;
    const amount = Math.floor(Number(state.currentBet || calcCurrentBet(state)) / 1000) * 1000;
    if (!Number.isFinite(amount) || amount < 1000) {
      player.lastNotice = 'Số tiền cược không hợp lệ hoặc vốn tự động không đủ';
      return;
    }
    const sessionKey = `${player.id}:${String(state.sessionId)}`;
    if (SESSIONS.has(sessionKey)) return;

    sock.emit('bet', { type: state.currentPrediction, amount });
    state.hasBetThisSession = true;
    state.waitingForResult = true;
    SESSIONS.set(sessionKey, {
      chatId: id,
      sessionId: state.sessionId,
      prediction: state.currentPrediction,
      amount,
      confidence: state.lastConfidence,
      patternType: state.lastPatternType,
      processed: false,
      placedAt: Date.now(),
    });
    state.currentBet = amount;
    savePersistentState();
    console.log(`[${id}] bet sent: ${state.currentPrediction} ${amount} session=${state.sessionId}`);
  });
  sock.on('bet-result', (data = {}) => {
    if (data.postBalance !== undefined && data.postBalance !== null) player.money = Number(data.postBalance) || 0;
    savePersistentState();
    try { sock.emit('get-current-my-info'); } catch (_) {}
  });
  sock.on('session-result', (data = {}) => {
    try { onSessionResult(player, data); }
    catch (error) { player.error = `Lỗi xử lý kết quả: ${error.message}`; console.error(`[${id}] session-result error:`, error); }
  });
  sock.connect();
  return sock;
}

async function startCollector() {
  const username = process.env.DATA_COLLECTOR_USER;
  const password = process.env.DATA_COLLECTOR_PASS;
  if (!username || !password || COLLECTOR) return;
  const login = await loginAndGetToken(username, password);
  if (login._error) {
    console.warn(`Collector không khởi động được: ${login._error}`);
    return;
  }
  const collector = io(`${GAME_ORIGIN}${GAME_NAMESPACE.startsWith('/') ? GAME_NAMESPACE : `/${GAME_NAMESPACE}`}`, {
    path: SOCKET_PATH, transports: ['websocket'], auth: { token: login.token },
    reconnection: true, reconnectionAttempts: Infinity, reconnectionDelay: 3000,
    reconnectionDelayMax: 15000, timeout: 20000, autoConnect: false,
    extraHeaders: { 'User-Agent': 'Mozilla/5.0' },
  });
  collector.on('new-session', (data = {}) => { collectorSessionId = String(data.id ?? data.sessionId ?? data.roundId ?? 'N/A'); });
  collector.on('session-result', (data = {}) => {
    const result = data?.resultTruyenThong;
    pushHistoryOnce(data?.id ?? data?.sessionId ?? collectorSessionId, result);
  });
  collector.on('connect', () => console.log('Collector connected'));
  collector.on('connect_error', (error) => console.warn(`Collector connect_error: ${error.message}`));
  collector.on('disconnect', (reason) => console.warn(`Collector disconnected: ${reason}`));
  COLLECTOR = collector;
  collector.connect();
}

app.get('/api/health', (_req, res) => res.json({ ok: true, service: 'LC79 Auto VIP', connectedPlayers: [...PLAYERS.values()].filter(p => p.connected).length, historySize: GLOBAL_HISTORY.length }));
app.post('/api/login', async (req, res) => {
  const username = String(req.body?.username || '').trim();
  const password = String(req.body?.password || '');
  if (!username || !password) return res.status(400).json({ error: 'Vui lòng nhập tài khoản và mật khẩu.' });
  if (username.length > 120 || password.length > 256) return res.status(400).json({ error: 'Thông tin đăng nhập quá dài.' });
  const login = await loginAndGetToken(username, password);
  if (login._error) return res.status(401).json({ error: login._error });

  const normalizedUser = username.toLocaleLowerCase('vi-VN');
  let player = [...PLAYERS.values()].find((p) =>
    (p.loginName && p.loginName.toLocaleLowerCase('vi-VN') === normalizedUser) ||
    (!p.loginName && p.nickname && p.nickname.toLocaleLowerCase('vi-VN') === String(login.nickname).toLocaleLowerCase('vi-VN'))
  );
  if (player) {
    try { player.sock?.disconnect(); } catch (_) {}
    player.token = login.token;
    player.loginName = username;
    player.nickname = login.nickname;
    player.money = Number(login.money || player.money || 0);
    if (!player.state.currentBet) player.state.currentBet = calcCurrentBet(player.state);
  } else {
    const id = crypto.randomUUID();
    player = initPlayer(id, login);
    player.state.betAmount = clampNumber(req.body?.betAmount, 1000, MAX_BET, 10000);
    PLAYERS.set(id, player);
  }
  savePersistentState();
  attachPlayerSocket(player);
  startCollector().catch((error) => console.warn('Collector error:', error.message));
  res.json({ ok: true, chatId: player.id, nickname: player.nickname, money: player.money, connected: player.connected, resumed: Boolean(player.state.autoBet), status: player.state.autoBet ? 'Đã khôi phục phiên auto đang chạy' : 'Đang kết nối Socket.IO' });
});

app.post('/api/bet', (req, res) => {
  const id = String(req.body?.chatId || '');
  const player = PLAYERS.get(id);
  if (!player) return res.status(404).json({ error: 'Phiên đăng nhập không tồn tại hoặc đã hết hạn. Hãy đăng nhập lại.' });
  const state = player.state;
  if (req.body.autoBet !== undefined) state.autoBet = Boolean(req.body.autoBet);
  if (req.body.betAmount !== undefined) state.betAmount = clampNumber(req.body.betAmount, 1000, MAX_BET, state.betAmount);
  if (req.body.x2Enabled !== undefined) state.x2Enabled = Boolean(req.body.x2Enabled);
  if (req.body.x2Mode !== undefined && ['mode1', 'mode2', 'mode3', 'mode4'].includes(req.body.x2Mode)) state.x2Mode = req.body.x2Mode;
  if (req.body.autoCapitalEnabled !== undefined) {
    const next = Boolean(req.body.autoCapitalEnabled);
    if (next && !state.autoCapitalEnabled) {
      const initial = clampNumber(req.body.autoInitialCapital, 1000, MAX_BET * 1000, 0);
      if (initial <= 0) return res.status(400).json({ error: 'Nhập vốn ban đầu lớn hơn 0 để bật tự chia vốn.' });
      state.autoInitialCapital = initial;
      state.autoCurrentCapital = initial;
      state.autoLevel = 1;
    }
    state.autoCapitalEnabled = next;
  }
  if (req.body.autoInitialCapital !== undefined && !state.autoCapitalEnabled) state.autoInitialCapital = clampNumber(req.body.autoInitialCapital, 0, MAX_BET * 1000, 0);
  if (req.body.autoRiskMode && ['antoan', 'balanced', 'manh'].includes(req.body.autoRiskMode)) state.autoRiskMode = req.body.autoRiskMode;
  if (req.body.autoMaxLevel !== undefined) state.autoMaxLevel = clampNumber(req.body.autoMaxLevel, 1, 7, state.autoMaxLevel);
  if (req.body.autoStopLoss !== undefined) state.autoStopLoss = clampNumber(req.body.autoStopLoss, 0, MAX_BET * 1000, 0);
  if (req.body.targetProfit !== undefined) state.targetProfit = clampNumber(req.body.targetProfit, 0, MAX_BET * 1000, 0);
  state.x2Multiplier = calcX2Multiplier(state);
  state.currentBet = calcCurrentBet(state);
  savePersistentState();
  res.json({ ok: true, autoBet: state.autoBet, betAmount: state.currentBet, state: serializeState(player) });
});

app.post('/api/logout', (req, res) => {
  const id = String(req.body?.chatId || '');
  const player = PLAYERS.get(id);
  if (player) {
    player.lastNotice = player.state.autoBet
      ? 'Đã rời giao diện; auto vẫn chạy trên máy chủ.'
      : 'Đã rời giao diện; phiên được giữ lại để xem lịch sử.';
    savePersistentState();
  }
  res.json({ ok: true, retained: Boolean(player), autoContinues: Boolean(player?.state.autoBet) });
});

app.post('/api/stop-auto', (req, res) => {
  const id = String(req.body?.chatId || '');
  const player = PLAYERS.get(id);
  if (!player) return res.status(404).json({ error: 'Không tìm thấy phiên đang lưu.' });
  stopAllAuto(player, 'Đã dừng tự động cược theo yêu cầu');
  res.json({ ok: true, state: serializeState(player) });
});

function serializeState(player) {
  const state = player.state;
  return {
    sessionId: state.sessionId,
    currentPrediction: state.currentPrediction,
    confidence: state.lastConfidence,
    patternType: state.lastPatternType,
    predictionReason: state.predictionReason,
    autoBet: state.autoBet,
    betAmount: state.currentBet || state.betAmount,
    baseBetAmount: state.betAmount,
    x2Enabled: state.x2Enabled,
    x2Mode: state.x2Mode,
    x2Multiplier: state.x2Multiplier,
    autoCapitalEnabled: state.autoCapitalEnabled,
    autoInitialCapital: state.autoInitialCapital,
    autoCurrentCapital: state.autoCurrentCapital,
    autoLevel: state.autoLevel,
    autoMaxLevel: state.autoMaxLevel,
    autoRiskMode: state.autoRiskMode,
    autoStopLoss: state.autoStopLoss,
    targetProfit: state.targetProfit,
    autoSessionCount: state.autoSessionCount,
    autoWinCount: state.autoWinCount,
    autoLoseCount: state.autoLoseCount,
    wins: state.wins,
    losses: state.losses,
    winStreak: state.winStreak,
    profitLoss: state.profitLoss,
    history: state.history.slice(0, MAX_PLAYER_HISTORY),
    skippedSignals: state.skippedSignals,
    hasBetThisSession: state.hasBetThisSession,
    waitingForResult: state.waitingForResult,
    smartCapitalBoost: state.smartCapitalBoost,
  };
}

app.get('/api/state', (req, res) => {
  const id = String(req.query.chatId || '');
  const player = PLAYERS.get(id);
  if (!player) return res.status(404).json({ error: 'Phiên đăng nhập không tồn tại. Hãy đăng nhập lại.' });
  res.json({
    ok: true,
    nickname: player.nickname,
    money: player.money,
    connected: player.connected,
    connecting: player.connecting,
    error: player.error,
    notice: player.lastNotice || player.lastResultNotice || '',
    historySize: GLOBAL_HISTORY.length,
    last12: GLOBAL_HISTORY.slice(-12),
    runtime: { service: 'LC79 Auto VIP Engine', dataSaved: fs.existsSync(DATA_FILE), savedAt: fs.existsSync(DATA_FILE) ? fs.statSync(DATA_FILE).mtime.toISOString() : null },
    state: serializeState(player),
  });
});

const INDEX_HTML = String.raw`<!doctype html>
<html lang="vi"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover"><meta name="theme-color" content="#101827"><title>LC79 Auto VIP</title>
<style>
:root{color-scheme:dark;--bg:#0b1220;--panel:#121d2e;--panel2:#172438;--line:#27364b;--text:#edf3fb;--muted:#96a7bc;--blue:#4c8dff;--blue2:#2f6fe7;--green:#35c995;--red:#ff6b78;--yellow:#f1bf5a;--radius:15px;--shadow:0 9px 30px #02081740}
*{box-sizing:border-box}body{margin:0;background:radial-gradient(ellipse at 70% -20%,#203a65 0,transparent 42%),var(--bg);color:var(--text);font:14px/1.45 Inter,ui-sans-serif,system-ui,-apple-system,"Segoe UI",sans-serif}button,input,select{font:inherit}button{cursor:pointer}button:disabled{opacity:.55;cursor:wait}.shell{width:min(1220px,100%);margin:auto;padding:22px 20px 40px}.topbar{display:flex;align-items:center;justify-content:space-between;gap:16px;padding:4px 0 20px}.brand{display:flex;gap:12px;align-items:center;min-width:0}.brandmark{width:42px;height:42px;display:grid;place-items:center;border-radius:13px;background:linear-gradient(145deg,#5ea0ff,#2858d2);font-size:16px;font-weight:900;box-shadow:0 7px 20px #2858d240}.brand h1{font-size:19px;margin:0;font-weight:780;letter-spacing:.2px}.brand p{margin:2px 0 0;color:var(--muted);font-size:12px}.pill{display:inline-flex;align-items:center;gap:7px;padding:7px 10px;border:1px solid var(--line);border-radius:999px;color:var(--muted);font-size:12px;white-space:nowrap}.dot{width:7px;height:7px;border-radius:50%;background:var(--yellow)}.dot.on{background:var(--green);box-shadow:0 0 0 3px #35c9951a}.dot.off{background:var(--red)}.notice{margin:0 0 16px;padding:11px 13px;border:1px solid #24456d;border-radius:12px;background:#132642;color:#bdd8ff;font-size:12px}.grid{display:grid;gap:14px}.hero-grid{grid-template-columns:minmax(0,1.35fr) minmax(270px,.85fr)}.stats{grid-template-columns:repeat(4,minmax(0,1fr));margin-top:14px}.panel{min-width:0;background:linear-gradient(180deg,#152236,#111b2b);border:1px solid var(--line);border-radius:var(--radius);box-shadow:var(--shadow);padding:17px}.panel-head{display:flex;align-items:center;justify-content:space-between;gap:10px;margin-bottom:14px}.panel-head h2,.panel-head h3{font-size:14px;margin:0;font-weight:730}.eyebrow{font-size:11px;letter-spacing:.8px;text-transform:uppercase;color:var(--muted);font-weight:750}.muted{color:var(--muted)}.small{font-size:12px}.prediction-panel{display:flex;flex-direction:column;min-height:248px}.prediction-row{display:flex;align-items:center;justify-content:space-between;gap:20px;flex:1}.predict-side{font-size:clamp(29px,4vw,42px);font-weight:850;letter-spacing:.3px;line-height:1.1;margin:8px 0}.predict-side.tai{color:var(--green)}.predict-side.xiu{color:#78aaff}.predict-side.none{color:var(--muted);font-size:27px}.session-tag{font-size:12px;color:var(--muted);margin-top:7px}.confidence{width:104px;height:104px;border:7px solid #2b4260;border-top-color:var(--blue);border-radius:50%;display:flex;flex-direction:column;align-items:center;justify-content:center;flex-shrink:0}.confidence strong{font-size:23px;line-height:1.15}.confidence span{font-size:10px;color:var(--muted);margin-top:3px}.reason{border-top:1px solid var(--line);padding-top:12px;color:var(--muted);font-size:12px}.account-money{font-size:26px;font-weight:800;letter-spacing:.2px;margin:5px 0 3px;word-break:break-word}.account-line{display:flex;align-items:center;justify-content:space-between;gap:10px;padding-top:11px;margin-top:11px;border-top:1px solid var(--line);font-size:12px}.stat-label{font-size:12px;color:var(--muted)}.stat-value{font-size:22px;font-weight:800;margin-top:7px;overflow-wrap:anywhere}.stat-foot{font-size:11px;color:var(--muted);margin-top:4px}.positive{color:var(--green)!important}.negative{color:var(--red)!important}.section{margin-top:14px}.settings-grid{display:grid;grid-template-columns:repeat(4,minmax(0,1fr));gap:12px}.field{display:flex;flex-direction:column;gap:6px;min-width:0}.field label{font-size:12px;color:var(--muted)}.field input,.field select{width:100%;min-width:0;height:40px;padding:0 11px;color:var(--text);background:#0d1726;border:1px solid #304159;border-radius:9px;outline:none}.field input:focus,.field select:focus{border-color:var(--blue);box-shadow:0 0 0 3px #4c8dff20}.field input:disabled{opacity:.65}.checks{display:flex;align-items:center;gap:15px;flex-wrap:wrap;margin-top:14px;padding:11px 12px;border:1px solid var(--line);border-radius:10px;background:#0e1827}.check{display:flex;align-items:center;gap:8px;font-size:12px;color:#cfdaea}.check input{accent-color:var(--blue);width:15px;height:15px}.actions{display:flex;gap:9px;flex-wrap:wrap;margin-top:14px}.btn{border:1px solid #354966;background:#1a2b43;color:var(--text);border-radius:10px;padding:10px 15px;font-weight:700;font-size:12px;min-height:39px}.btn.primary{background:var(--blue2);border-color:var(--blue2);color:#fff}.btn.stop{background:#3b202d;border-color:#75404d;color:#ffb1b7}.btn:hover{filter:brightness(1.09)}.status-line{font-size:12px;color:var(--muted);margin-top:11px;min-height:18px}.table-wrap{width:100%;overflow:auto;border:1px solid var(--line);border-radius:11px}table{width:100%;border-collapse:collapse;white-space:nowrap;font-size:12px}thead{background:#0e1827;color:#9fb0c5}th,td{text-align:left;padding:11px 12px;border-bottom:1px solid #233147}th{font-size:10px;font-weight:750;letter-spacing:.4px;text-transform:uppercase}tbody tr:last-child td{border-bottom:0}tbody tr:hover{background:#ffffff05}.badge{display:inline-block;border:1px solid var(--line);border-radius:7px;padding:4px 7px;font-size:10px;font-weight:800}.badge.win{color:var(--green);background:#14372f;border-color:#205b4c}.badge.loss{color:#ff9da5;background:#3a202d;border-color:#6c3541}.badge.tai{color:var(--green)}.badge.xiu{color:#8bbaff}.empty{padding:28px 12px!important;text-align:center;color:var(--muted)}.table-meta{font-size:11px;color:var(--muted)}.hidden{display:none!important}.login-wrap{min-height:calc(100vh - 60px);display:grid;place-items:center}.login-card{width:min(410px,100%);padding:25px;background:linear-gradient(180deg,#17263b,#111b2b);border:1px solid var(--line);border-radius:18px;box-shadow:var(--shadow)}.login-card .brand{margin-bottom:22px}.login-card h2{font-size:20px;margin:0 0 6px}.login-card>p{font-size:12px;color:var(--muted);margin:0 0 20px}.login-card .field{margin-top:13px}.login-card .btn{width:100%;margin-top:18px}.footer-note{text-align:center;color:#74869d;font-size:11px;padding-top:21px}.error-box{border:1px solid #713846;color:#ffb7be;background:#321b27;padding:10px 12px;border-radius:9px;margin-top:12px;font-size:12px}
@media(max-width:850px){.shell{padding:16px 13px 28px}.hero-grid{grid-template-columns:minmax(0,1fr)}.stats{grid-template-columns:repeat(2,minmax(0,1fr))}.settings-grid{grid-template-columns:repeat(2,minmax(0,1fr))}.prediction-panel{min-height:220px}.confidence{width:88px;height:88px}.panel{padding:14px}}
@media(max-width:420px){.shell{padding:12px 10px 24px}.topbar{align-items:flex-start}.brand h1{font-size:17px}.pill{font-size:10px;padding:6px 8px}.stats{gap:9px}.stat-value{font-size:19px}.settings-grid{gap:10px}.field input,.field select{height:38px;font-size:12px}.actions .btn{flex:1}.prediction-row{gap:10px}.predict-side{font-size:31px}.panel-head{align-items:flex-start}}
</style></head><body><main class="shell">
<header class="topbar"><div class="brand"><div class="brandmark">79</div><div><h1>LC79 AUTO VIP</h1><p>Điều khiển auto & theo dõi kết quả</p></div></div><div class="pill"><span id="headDot" class="dot"></span><span id="headStatus">Chưa đăng nhập</span></div></header>
<div id="loginView" class="login-wrap"><section class="login-card"><div class="brand"><div class="brandmark">79</div><div><h1>LC79 AUTO VIP</h1><p>Đăng nhập tài khoản trò chơi</p></div></div><h2>Đăng nhập</h2><p>Phiên auto được quản lý ở máy chủ, không phụ thuộc việc giữ tab trình duyệt mở.</p><form id="loginForm"><div class="field"><label for="username">Tên đăng nhập</label><input id="username" autocomplete="username" required maxlength="120" placeholder="Nhập tài khoản"></div><div class="field"><label for="password">Mật khẩu</label><input id="password" type="password" autocomplete="current-password" required maxlength="256" placeholder="Nhập mật khẩu"></div><div class="field"><label for="loginBet">Tiền cược cơ bản (VNĐ)</label><input id="loginBet" type="number" min="1000" step="1000" value="10000" required></div><button class="btn primary" id="loginBtn" type="submit">Đăng nhập / Khôi phục phiên</button></form><div id="loginError" class="error-box hidden"></div></section></div>
<div id="dashboard" class="hidden"><div class="notice">Đóng tab hoặc tắt trình duyệt không dừng auto. Máy chủ Node.js phải tiếp tục hoạt động và còn kết nối LC79; hãy dùng nút <b>Dừng auto</b> để dừng cược chủ động.</div>
<div class="grid hero-grid"><section class="panel prediction-panel"><div class="panel-head"><h2>Dự đoán phiên hiện tại (VIP Engine)</h2><span id="predictionBadge" class="badge">ĐANG CHỜ</span></div><div class="prediction-row"><div><div class="eyebrow">Phiên</div><div id="sessionId" class="session-tag">Đang lấy dữ liệu…</div><div id="prediction" class="predict-side none">ĐANG CHỜ</div><div class="session-tag">Mức cược dự kiến: <b id="currentBet">—</b></div></div><div class="confidence"><strong id="confidence">—</strong><span>TÍN HIỆU</span></div></div><div id="reason" class="reason">Đang chờ dữ liệu phiên.</div></section>
<section class="panel"><div class="panel-head"><h2>Tài khoản trò chơi</h2><span id="connectionPill" class="pill"><span class="dot"></span><span id="connectionText">Đang kết nối</span></span></div><div id="nickname" class="muted small">—</div><div id="money" class="account-money">—</div><div class="account-line"><span class="muted">Trạng thái tự động</span><b id="autoStatus">ĐANG TẮT</b></div><div class="account-line"><span class="muted">Chờ kết quả</span><b id="waitingStatus">Không</b></div><div class="account-line"><span class="muted">Thông báo mới nhất</span><b id="noticeText" style="text-align:right;max-width:65%;overflow-wrap:anywhere">—</b></div></section></div>
<div class="grid stats"><section class="panel"><div class="stat-label">Tổng thắng</div><div id="wins" class="stat-value positive">0</div><div class="stat-foot">Phiên thắng đã xác nhận</div></section><section class="panel"><div class="stat-label">Tổng thua</div><div id="losses" class="stat-value negative">0</div><div class="stat-foot">Phiên thua đã xác nhận</div></section><section class="panel"><div class="stat-label">Tỷ lệ thắng</div><div id="winRate" class="stat-value">—</div><div class="stat-foot">Thắng / tổng phiên có cược</div></section><section class="panel"><div class="stat-label">Lãi / lỗ ròng</div><div id="profitLoss" class="stat-value">0 ₫</div><div id="capitalLine" class="stat-foot">Vốn tự chia chưa bật</div></section></div>
<section class="panel section"><div class="panel-head"><h2>Cài đặt tự động cược</h2><span class="table-meta">Lưu trực tiếp tại máy chủ</span></div><div class="settings-grid"><div class="field"><label for="betAmount">Tiền cược cơ bản (VNĐ)</label><input id="betAmount" type="number" min="1000" max="100000000" step="1000" value="10000"></div><div class="field"><label for="initialCapital">Vốn tự chia (VNĐ)</label><input id="initialCapital" type="number" min="1000" step="1000" value="500000"></div><div class="field"><label for="riskMode">Mức rủi ro vốn</label><select id="riskMode"><option value="antoan">Thận trọng</option><option value="balanced" selected>Cân bằng</option><option value="manh">Cao</option></select></div><div class="field"><label for="maxLevel">Mức cược tối đa</label><select id="maxLevel"><option value="1">Mức 1</option><option value="2">Mức 2</option><option value="3">Mức 3</option><option value="4">Mức 4</option><option value="5">Mức 5</option><option value="6">Mức 6</option><option value="7" selected>Mức 7</option></select></div><div class="field"><label for="stopLoss">Mốc dừng lỗ vốn (0 = tắt)</label><input id="stopLoss" type="number" min="0" step="1000" value="0"></div><div class="field"><label for="targetProfit">Mục tiêu lãi (0 = tắt)</label><input id="targetProfit" type="number" min="0" step="1000" value="0"></div><div class="field"><label for="x2Mode">Chế độ nhân cược</label><select id="x2Mode"><option value="mode1">Nhân sau 1 thắng</option><option value="mode2">Nhân sau 2 thắng</option><option value="mode3">Tăng theo chuỗi thắng</option><option value="mode4">Nhân sau 3 thắng</option></select></div><div class="field"><label for="patternInfo">Phân tích tín hiệu</label><input id="patternInfo" value="Chờ đồng bộ" disabled></div></div><div class="checks"><label class="check"><input id="autoCapital" type="checkbox"> Tự chia vốn</label><label class="check"><input id="x2Enabled" type="checkbox"> Nhân cược theo chuỗi thắng</label></div><div class="actions"><button id="saveSettings" class="btn" type="button">Lưu cài đặt</button><button id="toggleAuto" class="btn primary" type="button">Bật auto cược</button><button id="stopAuto" class="btn stop" type="button">Dừng auto</button></div><div id="actionStatus" class="status-line" aria-live="polite"></div></section>
<section class="panel section"><div class="panel-head"><h2>Lịch sử cược chi tiết</h2><span id="historyMeta" class="table-meta">0 phiên</span></div><div class="table-wrap"><table><thead><tr><th>Phiên</th><th>Dự đoán</th><th>Kết quả</th><th>Tiền cược</th><th>Lãi / lỗ</th><th>Độ tin cậy</th><th>Thời gian</th></tr></thead><tbody id="historyRows"><tr><td colspan="7" class="empty">Chưa có lịch sử cược.</td></tr></tbody></table></div><div class="status-line">Kết quả và lãi/lỗ hiển thị theo dữ liệu máy chủ nhận được. Tín hiệu dự đoán được tính toán bởi thuật toán Bayes nâng cấp.</div></section><div class="footer-note">LC79 AUTO VIP ENGINE · Đóng tab không dừng tiến trình phía máy chủ · Quản lý vốn chủ động</div></div></main>
<script>
(function(){
'use strict';
var $=function(id){return document.getElementById(id)};
var chatId=localStorage.getItem('lc79AutoChatId')||'';
var latest=null, busy=false, timer=null;
function money(v){var n=Number(v);if(!Number.isFinite(n))n=0;return n.toLocaleString('vi-VN')+' ₫'}
function amount(v){return Math.max(1000,Math.min(100000000,Math.floor((Number(v)||1000)/1000)*1000))}
function escapeHtml(v){return String(v==null?'':v).replace(/[&<>"']/g,function(c){return {'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]})}
function setStatus(msg,isError){$('actionStatus').textContent=msg||'';$('actionStatus').style.color=isError?'#ff9da5':''}
async function request(url,method,body){var options={method:method||'GET',headers:{'Accept':'application/json'}};if(body){options.headers['Content-Type']='application/json';options.body=JSON.stringify(body)}var response=await fetch(url,options);var data=await response.json().catch(function(){return {error:'Phản hồi máy chủ không hợp lệ'}});if(!response.ok)throw new Error(data.error||('Lỗi HTTP '+response.status));return data}
function showLogin(message){$('loginView').classList.remove('hidden');$('dashboard').classList.add('hidden');$('headStatus').textContent='Chưa đăng nhập';$('headDot').className='dot off';if(message){$('loginError').textContent=message;$('loginError').classList.remove('hidden')}else{$('loginError').classList.add('hidden')}}
function showDashboard(){ $('loginView').classList.add('hidden');$('dashboard').classList.remove('hidden');$('loginError').classList.add('hidden') }
function dateText(v){if(!v)return '—';var d=new Date(v);return isNaN(d.getTime())?'—':d.toLocaleString('vi-VN',{day:'2-digit',month:'2-digit',hour:'2-digit',minute:'2-digit',second:'2-digit'})}
function render(d){latest=d;showDashboard();var s=d.state||{};var online=!!d.connected;$('headStatus').textContent=online?'Đã kết nối':(d.connecting?'Đang kết nối':'Mất kết nối');$('headDot').className='dot '+(online?'on':(d.connecting?'':'off'));$('connectionText').textContent=online?'Đã kết nối':(d.connecting?'Đang kết nối':'Mất kết nối');$('connectionPill').querySelector('.dot').className='dot '+(online?'on':(d.connecting?'':'off'));$('nickname').textContent=d.nickname||'Tài khoản';$('money').textContent=money(d.money);$('sessionId').textContent=s.sessionId?'#'+s.sessionId:'Chưa nhận phiên';var pred=s.currentPrediction;$('prediction').textContent=pred==='TAI'?'TÀI':(pred==='XIU'?'XỈU':'CHỜ TÍN HIỆU');$('prediction').className='predict-side '+(pred==='TAI'?'tai':pred==='XIU'?'xiu':'none');$('predictionBadge').textContent=pred?(s.confidence+'% tín hiệu'):'ĐANG CHỜ';$('confidence').textContent=Number(s.confidence||0).toLocaleString('vi-VN')+'%';$('currentBet').textContent=money(s.betAmount||s.baseBetAmount||0);$('reason').textContent=s.predictionReason||'Chưa có lý do phân tích';$('autoStatus').textContent=s.autoBet?'ĐANG CHẠY':'ĐANG TẮT';$('autoStatus').className=s.autoBet?'positive':'muted';$('waitingStatus').textContent=s.waitingForResult?'Đang đợi phiên trả kết quả':'Không';$('noticeText').textContent=d.notice||d.error||'Không có';$('wins').textContent=Number(s.wins||0).toLocaleString('vi-VN');$('losses').textContent=Number(s.losses||0).toLocaleString('vi-VN');var total=Number(s.wins||0)+Number(s.losses||0);$('winRate').textContent=total?((Number(s.wins||0)/total)*100).toFixed(1).replace('.',',')+'%':'—';$('profitLoss').textContent=money(s.profitLoss||0);$('profitLoss').className='stat-value '+(Number(s.profitLoss||0)>0?'positive':Number(s.profitLoss||0)<0?'negative':'');$('capitalLine').textContent=s.autoCapitalEnabled?'Vốn còn lại: '+money(s.autoCurrentCapital)+' · mức '+s.autoLevel+'/'+s.autoMaxLevel:'Vốn tự chia chưa bật';$('toggleAuto').textContent=s.autoBet?'Tạm dừng auto cược':'Bật auto cược';$('toggleAuto').className='btn '+(s.autoBet?'stop':'primary');$('patternInfo').value=(s.patternType||'normal')+' · '+(s.predictionReason||'');$('historyMeta').textContent=(s.history||[]).length+' phiên lưu gần nhất';
if(document.activeElement!==$('betAmount'))$('betAmount').value=s.baseBetAmount||10000;
if(document.activeElement!==$('initialCapital'))$('initialCapital').value=s.autoInitialCapital||500000;
if(document.activeElement!==$('riskMode'))$('riskMode').value=s.autoRiskMode||'balanced';
if(document.activeElement!==$('maxLevel'))$('maxLevel').value=String(s.autoMaxLevel||7);
if(document.activeElement!==$('stopLoss'))$('stopLoss').value=s.autoStopLoss||0;
if(document.activeElement!==$('targetProfit'))$('targetProfit').value=s.targetProfit||0;
if(document.activeElement!==$('x2Mode'))$('x2Mode').value=s.x2Mode||'mode1';
$('autoCapital').checked=!!s.autoCapitalEnabled;$('x2Enabled').checked=!!s.x2Enabled;
var rows=s.history||[];if(!rows.length){$('historyRows').innerHTML='<tr><td colspan="7" class="empty">Chưa có lịch sử cược. Bật auto để theo dõi các phiên.</td></tr>'}else{$('historyRows').innerHTML=rows.map(function(r){var isWin=!!r.isWin;var side=r.prediction==='TAI'?'TÀI':'XỈU';var actual=r.result==='TAI'?'TÀI':'XỈU';var net=Number(r.profit||0);return '<tr><td>#'+escapeHtml(r.sessionId)+'</td><td><span class="badge '+(r.prediction==='TAI'?'tai':'xiu')+'">'+side+'</span></td><td>'+escapeHtml(actual)+' <span class="badge '+(isWin?'win':'loss')+'">'+(isWin?'THẮNG':'THUA')+'</span></td><td>'+money(r.betAmount)+'</td><td class="'+(net>0?'positive':net<0?'negative':'')+'">'+(net>0?'+':'')+money(net)+'</td><td>'+Number(r.confidence||0).toLocaleString('vi-VN')+'%</td><td>'+dateText(r.settledAt)+'</td></tr>'}).join('')}
}
async function refresh(){if(!chatId||busy)return;try{var d=await request('/api/state?chatId='+encodeURIComponent(chatId));render(d)}catch(e){if(/không tồn tại|hết hạn|không tìm thấy/i.test(e.message)){localStorage.removeItem('lc79AutoChatId');chatId='';showLogin('Phiên cũ không còn trên máy chủ. Vui lòng đăng nhập lại.')}else{$('headStatus').textContent='Lỗi kết nối';$('headDot').className='dot off';if(latest){$('connectionText').textContent='Lỗi đồng bộ';setStatus(e.message,true)}}}}
$('loginForm').addEventListener('submit',async function(e){e.preventDefault();if(busy)return;busy=true;$('loginBtn').disabled=true;$('loginBtn').textContent='Đang kết nối…';$('loginError').classList.add('hidden');try{var d=await request('/api/login','POST',{username:$('username').value.trim(),password:$('password').value,betAmount:amount($('loginBet').value)});chatId=d.chatId;localStorage.setItem('lc79AutoChatId',chatId);$('password').value='';busy=false;await refresh();setStatus(d.status||'Đã đăng nhập. Cấu hình auto ở bên dưới.');}catch(err){showLogin(err.message)}finally{busy=false;$('loginBtn').disabled=false;$('loginBtn').textContent='Đăng nhập / Khôi phục phiên'}});
function settingsPayload(){return {chatId:chatId,betAmount:amount($('betAmount').value),autoInitialCapital:Math.max(0,Number($('initialCapital').value)||0),autoCapitalEnabled:$('autoCapital').checked,autoRiskMode:$('riskMode').value,autoMaxLevel:Number($('maxLevel').value)||7,autoStopLoss:Math.max(0,Number($('stopLoss').value)||0),targetProfit:Math.max(0,Number($('targetProfit').value)||0),x2Enabled:$('x2Enabled').checked,x2Mode:$('x2Mode').value}}
$('saveSettings').addEventListener('click',async function(){if(!chatId)return;try{var d=await request('/api/bet','POST',settingsPayload());if(d.state)render(Object.assign({},latest||{},{state:d.state}));setStatus('Đã lưu cài đặt trên máy chủ.')}catch(e){setStatus(e.message,true)}});
$('toggleAuto').addEventListener('click',async function(){if(!chatId||!latest)return;try{var payload=settingsPayload();payload.autoBet=!(latest.state&&latest.state.autoBet);var d=await request('/api/bet','POST',payload);if(d.state)render(Object.assign({},latest,{state:d.state}));setStatus(payload.autoBet?'Đã gửi lệnh bật auto. Hãy theo dõi kết nối và số dư.':'Đã gửi lệnh tắt auto; vé đã gửi vẫn chờ kết quả.')}catch(e){setStatus(e.message,true)}});
$('stopAuto').addEventListener('click',async function(){if(!chatId)return;try{var d=await request('/api/stop-auto','POST',{chatId:chatId});if(d.state)render(Object.assign({},latest||{},{state:d.state}));setStatus('Đã dừng auto cược.')}catch(e){setStatus(e.message,true)}});
if(chatId){$('loginView').classList.add('hidden');$('dashboard').classList.remove('hidden');refresh()}else{showLogin()}
timer=setInterval(function(){refresh()},2000);
})();
</script></body></html>`;

app.get('/', (_req, res) => {
  res.set('Cache-Control', 'no-store');
  res.type('html').send(INDEX_HTML);
});

app.use((error, _req, res, _next) => {
  console.error('Express error:', error.message);
  res.status(500).json({ error: 'Lỗi máy chủ xử lý yêu cầu.' });
});

loadPersistentState();
for (const restoredPlayer of PLAYERS.values()) {
  try { attachPlayerSocket(restoredPlayer); }
  catch (error) { restoredPlayer.error = `Không thể khôi phục Socket: ${error.message}`; }
}

const server = app.listen(PORT, '0.0.0.0', () => {
  console.log('='.repeat(54));
  console.log(`LC79 Auto VIP Engine đang chạy tại http://localhost:${PORT}`);
  console.log(`Socket origin: ${GAME_ORIGIN} | namespace: ${GAME_NAMESPACE} | path: ${SOCKET_PATH}`);
  console.log('='.repeat(54));
});

function shutdown() {
  if (persistTimer) { clearTimeout(persistTimer); persistTimer = null; }
  writePersistentStateSync();
  for (const player of PLAYERS.values()) {
    try { player.sock?.disconnect(); } catch (_) {}
  }
  try { COLLECTOR?.disconnect(); } catch (_) {}
  server.close(() => process.exit(0));
  setTimeout(() => process.exit(0), 2500).unref();
}

process.on('SIGINT', shutdown);
process.on('SIGTERM', shutdown);