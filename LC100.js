import fastify from "fastify";
import cors from "@fastify/cors";
import * as path from "node:path";
import { fileURLToPath } from "node:url";
import fetch from "node-fetch";

// --- CẤU HÌNH CAO CẤP ---
const PORT = 3000;
const API_URL = "https://wtxmd52.tele68.com/v1/txmd5/sessions";

// --- GLOBAL STATE ---
let txHistory = []; 
let currentSessionId = null; 
let fetchInterval = null; 

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

// ==================== UTILITIES ====================
function parseLines(data) {
    if (!data || !Array.isArray(data.list)) return [];
    const sortedList = data.list.sort((a, b) => b.id - a.id);
    return sortedList.map(item => ({
        session: item.id,
        dice: item.dices,
        total: item.point,
        result: item.resultTruyenThong,
        tx: item.point >= 11 ? 'T' : 'X'
    })).sort((a, b) => a.session - b.session);
}

function lastN(arr, n) {
    const start = Math.max(0, arr.length - n);
    return arr.slice(start);
}

function majority(obj) {
    let maxK = null, maxV = -Infinity;
    for (const k in obj) if (obj[k] > maxV) { maxV = obj[k]; maxK = k; }
    return { key: maxK, val: maxV };
}

function sum(nums) { return nums.reduce((a, b) => a + b, 0); }
function avg(nums) { return nums.length ? sum(nums) / nums.length : 0; }

function entropy(arr) {
    if (!arr.length) return 0;
    const freq = {};
    for (const v of arr) freq[v] = (freq[v] || 0) + 1;
    let e = 0, n = arr.length;
    for (const k in freq) { const p = freq[k] / n; e -= p * Math.log2(p); }
    return e;
}

function similarity(a, b) {
    if (a.length !== b.length) return 0;
    let m = 0;
    for (let i = 0; i < a.length; i++) if (a[i] === b[i]) m++;
    return m / a.length;
}

// ==================== FEATURE ENGINEERING ====================
function extractFeatures(history) {
    const tx = history.map(h => h.tx);
    const totals = history.map(h => h.total);
    const dice1 = history.map(h => h.dice[0]);
    const dice2 = history.map(h => h.dice[1]);
    const dice3 = history.map(h => h.dice[2]);
    
    const freq = {};
    for (const v of tx) freq[v] = (freq[v] || 0) + 1;
    
    let runs = [], cur = tx[0], len = 1;
    for (let i = 1; i < tx.length; i++) {
        if (tx[i] === cur) len++;
        else { runs.push({ val: cur, len }); cur = tx[i]; len = 1; }
    }
    if (tx.length) runs.push({ val: cur, len });
    
    const meanTotal = avg(totals);
    const variance = avg(totals.map(t => Math.pow(t - meanTotal, 2)));
    
    return {
        tx, totals, dice1, dice2, dice3, freq, runs,
        maxRun: runs.reduce((m, r) => Math.max(m, r.len), 0),
        meanTotal, stdTotal: Math.sqrt(variance),
        entropy: entropy(tx),
        last3Pattern: tx.slice(-3).join(''),
        last5Pattern: tx.slice(-5).join(''),
        last8Pattern: tx.slice(-8).join('')
    };
}

// ==================== THUẬT TOÁN PHÂN TÍCH CẦU ====================

// 1. CẦU 1-1 (Xen kẽ)
function analyzeCau11(history) {
    const tx = history.map(h => h.tx);
    if (tx.length < 10) return null;
    const last6 = tx.slice(-6);
    let is11 = true;
    for (let i = 1; i < last6.length; i++) {
        if (last6[i] === last6[i-1]) { is11 = false; break; }
    }
    if (is11) return last6[last6.length-1] === 'T' ? 'X' : 'T';
    return null;
}

// 2. CẦU BỆT (dài)
function analyzeCauBet(history) {
    const runs = extractFeatures(history).runs;
    if (runs.length === 0) return null;
    const lastRun = runs[runs.length-1];
    if (lastRun.len >= 4) {
        if (lastRun.len >= 7) return lastRun.val === 'T' ? 'X' : 'T';
        return lastRun.val;
    }
    return null;
}

// 3. CẦU 2-2 (XX YY XX YY)
function analyzeCau22(history) {
    const runs = extractFeatures(history).runs;
    if (runs.length < 4) return null;
    const last4 = runs.slice(-4);
    if (last4.every(r => r.len === 2)) {
        const isAlt = last4[0].val !== last4[1].val && last4[1].val !== last4[2].val && last4[2].val !== last4[3].val;
        if (isAlt) return last4[3].val === 'T' ? 'X' : 'T';
    }
    return null;
}

// 4. CẦU 3-3 (XXX YYY XXX YYY)
function analyzeCau33(history) {
    const runs = extractFeatures(history).runs;
    if (runs.length < 4) return null;
    const last4 = runs.slice(-4);
    if (last4.every(r => r.len === 3)) {
        const isAlt = last4[0].val !== last4[1].val && last4[1].val !== last4[2].val && last4[2].val !== last4[3].val;
        if (isAlt) return last4[3].val === 'T' ? 'X' : 'T';
    }
    return null;
}

// 5. CẦU 1-2-1 (T XX T XX T)
function analyzeCau121(history) {
    const runs = extractFeatures(history).runs;
    if (runs.length < 5) return null;
    const last5 = runs.slice(-5);
    const pattern = last5.map(r => r.len).join('');
    if (pattern === '12121') {
        const vals = last5.map(r => r.val);
        const isAlt = vals[0] !== vals[1] && vals[2] !== vals[3];
        if (isAlt) return vals[4] === 'T' ? 'X' : 'T';
    }
    return null;
}

// 6. CẦU 2-1-2 (TT X TT X TT)
function analyzeCau212(history) {
    const runs = extractFeatures(history).runs;
    if (runs.length < 5) return null;
    const last5 = runs.slice(-5);
    const pattern = last5.map(r => r.len).join('');
    if (pattern === '21212') {
        const vals = last5.map(r => r.val);
        const isAlt = vals[0] !== vals[1] && vals[2] !== vals[3];
        if (isAlt) return vals[4] === 'T' ? 'T' : 'X';
    }
    return null;
}

// 7. CẦU 3-2-3 (TTT XX TTT XX)
function analyzeCau323(history) {
    const runs = extractFeatures(history).runs;
    if (runs.length < 5) return null;
    const last5 = runs.slice(-5);
    const pattern = last5.map(r => r.len).join('');
    if (pattern === '32323') {
        const vals = last5.map(r => r.val);
        if (vals[0] !== vals[2] && vals[2] !== vals[4]) return vals[4] === 'T' ? 'X' : 'T';
    }
    return null;
}

// 8. CẦU 4-2-4 (TTTT XX TTTT XX)
function analyzeCau424(history) {
    const runs = extractFeatures(history).runs;
    if (runs.length < 5) return null;
    const last5 = runs.slice(-5);
    const pattern = last5.map(r => r.len).join('');
    if (pattern === '42424') {
        const vals = last5.map(r => r.val);
        if (vals[0] !== vals[2] && vals[2] !== vals[4]) return vals[4] === 'T' ? 'X' : 'T';
    }
    return null;
}

// 9. PHÂN TÍCH TỔNG ĐIỂM (Mean Reversion)
function analyzeMeanReversion(history) {
    if (history.length < 20) return null;
    const totals = history.map(h => h.total);
    const recentAvg = avg(totals.slice(-20));
    const overallAvg = avg(totals);
    if (recentAvg > 12.5 && overallAvg > 11) return 'X';
    if (recentAvg < 8.5 && overallAvg < 10) return 'T';
    return null;
}

// 10. PHÂN TÍCH XÚC XẮC (tổng 3 mặt)
function analyzeDiceTrend(history) {
    if (history.length < 30) return null;
    const sums = history.map(h => h.dice[0] + h.dice[1] + h.dice[2]);
    const recentSums = sums.slice(-15);
    const avgSum = avg(recentSums);
    if (avgSum > 12) return 'X';
    if (avgSum < 9) return 'T';
    return null;
}

// 11. PHÂN TÍCH CHÊNH LỆCH TÀI XỈU
function analyzeBalance(history) {
    if (history.length < 40) return null;
    const tx = history.map(h => h.tx);
    const tCount = tx.filter(v => v === 'T').length;
    const xCount = tx.filter(v => v === 'X').length;
    const diff = Math.abs(tCount - xCount);
    const total = tCount + xCount;
    if (diff / total > 0.25) {
        return tCount > xCount ? 'X' : 'T';
    }
    return null;
}

// 12. PHÂN TÍCH CHU KỲ (Periodic)
function analyzeCycle(history) {
    if (history.length < 60) return null;
    const tx = history.map(h => h.tx);
    for (let cycle = 2; cycle <= 10; cycle++) {
        let matches = 0;
        for (let i = cycle; i < tx.length; i++) {
            if (tx[i] === tx[i - cycle]) matches++;
        }
        const ratio = matches / (tx.length - cycle);
        if (ratio > 0.7) {
            return tx[tx.length - cycle];
        }
    }
    return null;
}

// 13. PHÂN TÍCH MOMENTUM (đà tăng/giảm)
function analyzeMomentum(history) {
    if (history.length < 30) return null;
    const tx = history.map(h => h.tx);
    const half = Math.floor(tx.length / 2);
    const firstHalf = tx.slice(0, half);
    const secondHalf = tx.slice(-half);
    const firstT = firstHalf.filter(v => v === 'T').length;
    const secondT = secondHalf.filter(v => v === 'T').length;
    if (Math.abs(secondT - firstT) > half * 0.3) {
        return secondT > firstT ? 'T' : 'X';
    }
    return null;
}

// 14. PHÂN TÍCH HỒI QUY ĐƠN GIẢN
function analyzeRegression(history) {
    if (history.length < 50) return null;
    const totals = history.map(h => h.total);
    const n = totals.length;
    let sumX = 0, sumY = 0, sumXY = 0, sumX2 = 0;
    for (let i = 0; i < n; i++) {
        sumX += i;
        sumY += totals[i];
        sumXY += i * totals[i];
        sumX2 += i * i;
    }
    const slope = (n * sumXY - sumX * sumY) / (n * sumX2 - sumX * sumX);
    if (slope > 0.05) return 'X';
    if (slope < -0.05) return 'T';
    return null;
}

// 15. THUẬT TOÁN ĐA SỐ (Voting từ nhiều cầu)
function analyzeMultiPattern(history) {
    const results = [];
    const cau11 = analyzeCau11(history);
    const cauBet = analyzeCauBet(history);
    const cau22 = analyzeCau22(history);
    const cau33 = analyzeCau33(history);
    const cau121 = analyzeCau121(history);
    const cau212 = analyzeCau212(history);
    const meanRev = analyzeMeanReversion(history);
    const balance = analyzeBalance(history);
    
    if (cau11) results.push(cau11);
    if (cauBet) results.push(cauBet);
    if (cau22) results.push(cau22);
    if (cau33) results.push(cau33);
    if (cau121) results.push(cau121);
    if (cau212) results.push(cau212);
    if (meanRev) results.push(meanRev);
    if (balance) results.push(balance);
    
    if (results.length === 0) return null;
    const tCount = results.filter(r => r === 'T').length;
    const xCount = results.filter(r => r === 'X').length;
    if (Math.abs(tCount - xCount) >= 2) {
        return tCount > xCount ? 'T' : 'X';
    }
    return null;
}

// ==================== ENSEMBLE TỔNG HỢP ====================
class CauAnalyst {
    constructor() {
        this.history = [];
        this.lastPrediction = null;
        this.correctCount = 0;
        this.totalCount = 0;
    }
    
    loadInitial(lines) {
        this.history = lines;
        console.log(`📊 Đã tải ${lines.length} phiên lịch sử cho phân tích cầu`);
    }
    
    pushRecord(record) {
        this.history.push(record);
        if (this.history.length > 500) this.history = this.history.slice(-450);
        
        // Kiểm tra độ chính xác
        if (this.lastPrediction && this.lastPrediction === record.tx) {
            this.correctCount++;
        }
        this.totalCount++;
        
        // Dự đoán mới
        this.lastPrediction = this.predict();
        
        const accuracy = this.totalCount > 0 ? (this.correctCount / this.totalCount * 100).toFixed(1) : 0;
        console.log(`🎲 ${record.session} → ${record.result} | Dự đoán tiếp: ${this.lastPrediction === 'T' ? 'TÀI' : 'XỈU'} | Acc: ${accuracy}%`);
    }
    
    predict() {
        if (this.history.length < 15) return 'T';
        
        // Lấy kết quả từ các thuật toán
        const cau11 = analyzeCau11(this.history);
        const cauBet = analyzeCauBet(this.history);
        const cau22 = analyzeCau22(this.history);
        const cau33 = analyzeCau33(this.history);
        const cau121 = analyzeCau121(this.history);
        const cau212 = analyzeCau212(this.history);
        const cau323 = analyzeCau323(this.history);
        const cau424 = analyzeCau424(this.history);
        const meanRev = analyzeMeanReversion(this.history);
        const diceTrend = analyzeDiceTrend(this.history);
        const balance = analyzeBalance(this.history);
        const cycle = analyzeCycle(this.history);
        const momentum = analyzeMomentum(this.history);
        const regression = analyzeRegression(this.history);
        const multi = analyzeMultiPattern(this.history);
        
        // Gộp tất cả dự đoán
        const votes = { T: 0, X: 0 };
        const addVote = (pred, weight = 1) => { if (pred) votes[pred] += weight; };
        
        addVote(cau11, 1.2);
        addVote(cauBet, 1.5);
        addVote(cau22, 1.2);
        addVote(cau33, 1.2);
        addVote(cau121, 1.3);
        addVote(cau212, 1.3);
        addVote(cau323, 1.3);
        addVote(cau424, 1.3);
        addVote(meanRev, 1.0);
        addVote(diceTrend, 1.0);
        addVote(balance, 1.2);
        addVote(cycle, 1.1);
        addVote(momentum, 1.0);
        addVote(regression, 0.8);
        addVote(multi, 1.4);
        
        if (votes.T === 0 && votes.X === 0) {
            const lastTx = this.history[this.history.length-1]?.tx;
            return lastTx === 'T' ? 'X' : 'T';
        }
        
        return votes.T > votes.X ? 'T' : 'X';
    }
    
    getPrediction() {
        const pred = this.lastPrediction || this.predict();
        const confidence = this.totalCount > 50 ? 
            Math.min(0.95, (this.correctCount / this.totalCount) + 0.3) : 0.75;
        return {
            prediction: pred === 'T' ? 'tài' : 'xỉu',
            confidence,
            rawPrediction: pred
        };
    }
}

const cauAnalyst = new CauAnalyst();

// ==================== FETCH & UPDATE ====================
async function fetchAndProcessHistory() {
    try {
        const response = await fetch(API_URL);
        const data = await response.json();
        const newHistory = parseLines(data);
        
        if (newHistory.length === 0) return;
        
        const lastSessionInHistory = newHistory.at(-1);
        
        if (!currentSessionId) {
            cauAnalyst.loadInitial(newHistory);
            txHistory = newHistory;
            currentSessionId = lastSessionInHistory.session;
            console.log(`✅ Đã tải ${newHistory.length} phiên lịch sử.`);
        } else if (lastSessionInHistory.session > currentSessionId) {
            const newRecords = newHistory.filter(r => r.session > currentSessionId);
            for (const record of newRecords) cauAnalyst.pushRecord(record);
            txHistory.push(...newRecords);
            if (txHistory.length > 500) txHistory = txHistory.slice(-450);
            currentSessionId = lastSessionInHistory.session;
            if (newRecords.length > 0) console.log(`🆕 Cập nhật ${newRecords.length} phiên.`);
        }
    } catch (e) {
        console.error("❌ Lỗi fetch:", e.message);
    }
}

// ==================== API SERVER ====================
const app = fastify({ logger: false });
await app.register(cors, { origin: "*" });

// Khởi động fetch
fetchAndProcessHistory();
clearInterval(fetchInterval);
fetchInterval = setInterval(fetchAndProcessHistory, 5000);
console.log(`🔄 AI Phân Tích Cầu đang chạy (interval 5s)`);

// API Endpoints
app.get("/api/cau", async () => {
    const lastResult = txHistory.at(-1) || null;
    const prediction = cauAnalyst.getPrediction();
    
    // Phân tích cầu hiện tại
    const runs = txHistory.length > 0 ? extractFeatures(txHistory).runs : [];
    const currentRun = runs.length > 0 ? runs[runs.length-1] : null;
    const last10Tx = txHistory.slice(-10).map(h => h.tx).join('');
    
    let activeCau = "không xác định";
    if (analyzeCau11(txHistory)) activeCau = "Cầu 1-1 (Xen kẽ)";
    else if (analyzeCauBet(txHistory)) activeCau = "Cầu Bệt";
    else if (analyzeCau22(txHistory)) activeCau = "Cầu 2-2";
    else if (analyzeCau33(txHistory)) activeCau = "Cầu 3-3";
    else if (analyzeCau121(txHistory)) activeCau = "Cầu 1-2-1";
    else if (analyzeCau212(txHistory)) activeCau = "Cầu 2-1-2";
    
    return {
        status: "success",
        last_session: lastResult?.session || null,
        last_result: lastResult?.result?.toLowerCase() || null,
        last_total: lastResult?.total || null,
        last_dice: lastResult?.dice || null,
        active_pattern: activeCau,
        current_run: currentRun ? `${currentRun.val === 'T' ? 'TÀI' : 'XỈU'} (${currentRun.len} phiên)` : "chưa có",
        last10_sequence: last10Tx.replace(/T/g, 'T').replace(/X/g, 'X'),
        next_prediction: prediction.prediction,
        confidence: `${(prediction.confidence * 100).toFixed(0)}%`,
        algorithm_stats: {
            total_predictions: cauAnalyst.totalCount,
            correct_predictions: cauAnalyst.correctCount,
            accuracy: cauAnalyst.totalCount > 0 ? 
                (cauAnalyst.correctCount / cauAnalyst.totalCount * 100).toFixed(1) + "%" : "0%"
        }
    };
});

app.get("/api/cau/history", async () => {
    if (!txHistory.length) return { message: "no data" };
    const reversed = [...txHistory].sort((a, b) => b.session - a.session).slice(0, 100);
    return reversed.map(h => ({
        session: h.session,
        dice: h.dice,
        total: h.total,
        result: h.result.toLowerCase(),
        tx: h.tx
    }));
});

app.get("/api/cau/analysis", async () => {
    if (txHistory.length < 20) return { message: "cần ít nhất 20 phiên để phân tích" };
    
    const runs = extractFeatures(txHistory).runs;
    const last10Runs = runs.slice(-10);
    
    return {
        total_sessions: txHistory.length,
        runs_analysis: {
            total_runs: runs.length,
            avg_run_length: avg(runs.map(r => r.len)).toFixed(2),
            max_run_length: Math.max(...runs.map(r => r.len)),
            current_run: runs[runs.length-1]?.len || 0,
            current_run_type: runs[runs.length-1]?.val === 'T' ? 'TÀI' : 'XỈU'
        },
        cau_detected: {
            cau11: analyzeCau11(txHistory) ? "active" : "inactive",
            cau22: analyzeCau22(txHistory) ? "active" : "inactive",
            cau33: analyzeCau33(txHistory) ? "active" : "inactive",
            cau121: analyzeCau121(txHistory) ? "active" : "inactive",
            cau212: analyzeCau212(txHistory) ? "active" : "inactive",
            cau323: analyzeCau323(txHistory) ? "active" : "inactive",
            cau424: analyzeCau424(txHistory) ? "active" : "inactive",
            cau_bet: analyzeCauBet(txHistory) ? "active" : "inactive"
        },
        last_10_runs: last10Runs.map(r => ({ type: r.val === 'T' ? 'TÀI' : 'XỈU', length: r.len }))
    };
});

app.get("/", async () => {
    return {
        name: "AI Phân Tích Cầu Tài Xỉu",
        version: "2.0",
        description: "Phân tích 15+ loại cầu khác nhau",
        endpoints: [
            "GET /api/cau - Dự đoán phiên tiếp theo",
            "GET /api/cau/history - Lịch sử 100 phiên gần nhất",
            "GET /api/cau/analysis - Phân tích chi tiết cầu đang chạy"
        ]
    };
});

// ==================== START SERVER ====================
const start = async () => {
    try {
        await app.listen({ port: PORT, host: "0.0.0.0" });
    } catch (err) {
        console.error("Lỗi server:", err.message);
        process.exit(1);
    }
    
    let publicIP = "0.0.0.0";
    try {
        const res = await fetch("https://ifconfig.me/ip");
        publicIP = (await res.text()).trim();
    } catch (e) {}
    
    console.log("\n╔════════════════════════════════════════════╗");
    console.log("║   🎲 AI PHÂN TÍCH CẦU TÀI XỈU 🎲        ║");
    console.log("╚════════════════════════════════════════════╝");
    console.log(`   Local:   http://localhost:${PORT}`);
    console.log(`   Network: http://${publicIP}:${PORT}\n`);
    console.log("   Các loại cầu hỗ trợ:");
    console.log("   • Cầu 1-1 (xen kẽ)");
    console.log("   • Cầu bệt (dài)");
    console.log("   • Cầu 2-2, 3-3");
    console.log("   • Cầu 1-2-1, 2-1-2");
    console.log("   • Cầu 3-2-3, 4-2-4");
    console.log("   • Mean Reversion, Momentum, Chu kỳ...\n");
};

start();
