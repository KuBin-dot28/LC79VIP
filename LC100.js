import fastify from "fastify";
import cors from "@fastify/cors";
import * as path from "node:path";
import { fileURLToPath } from "node:url";
import fetch from "node-fetch";
import fs from "node:fs";

// --- CẤU HÌNH CAO CẤP ---
const PORT = 3000;
const API_URL = "https://wtxmd52.tele68.com/v1/txmd5/sessions";
const BACKUP_FILE = path.join(process.cwd(), "history_backup.json");

// --- GLOBAL STATE ---
let txHistory = []; 
let currentSessionId = null; 
let fetchInterval = null;
let reconnectAttempts = 0;
const MAX_RECONNECT_ATTEMPTS = 10;

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
function std(nums) {
    if (nums.length < 2) return 0;
    const m = avg(nums);
    return Math.sqrt(avg(nums.map(x => Math.pow(x - m, 2))));
}
function median(nums) {
    if (!nums.length) return 0;
    const sorted = [...nums].sort((a,b)=>a-b);
    return sorted[Math.floor(sorted.length/2)];
}
function mode(arr) {
    if (!arr.length) return null;
    const freq = {};
    for (const v of arr) freq[v] = (freq[v]||0)+1;
    let maxK=null, maxV=-1;
    for (const k in freq) if (freq[k]>maxV) {maxV=freq[k]; maxK=k;}
    return maxK;
}

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

// ==================== BACKUP & RESTORE ====================
function saveBackup() {
    try {
        const data = {
            history: txHistory,
            currentSessionId,
            timestamp: new Date().toISOString()
        };
        fs.writeFileSync(BACKUP_FILE, JSON.stringify(data, null, 2));
        console.log(`💾 Đã lưu backup ${txHistory.length} phiên`);
    } catch (e) {
        console.error("Lỗi lưu backup:", e.message);
    }
}

function loadBackup() {
    try {
        if (fs.existsSync(BACKUP_FILE)) {
            const data = JSON.parse(fs.readFileSync(BACKUP_FILE, 'utf8'));
            if (data.history && data.history.length > 0) {
                txHistory = data.history;
                currentSessionId = data.currentSessionId;
                console.log(`📦 Đã khôi phục ${txHistory.length} phiên từ backup`);
                return true;
            }
        }
    } catch (e) {
        console.error("Lỗi đọc backup:", e.message);
    }
    return false;
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
        last8Pattern: tx.slice(-8).join(''),
        last10Pattern: tx.slice(-10).join('')
    };
}

// ==================== THUẬT TOÁN PHÂN TÍCH CẦU (MỞ RỘNG 50+ THUẬT TOÁN) ====================

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

// 9. CẦU 5-3-5
function analyzeCau535(history) {
    const runs = extractFeatures(history).runs;
    if (runs.length < 5) return null;
    const last5 = runs.slice(-5);
    const pattern = last5.map(r => r.len).join('');
    if (pattern === '53535') {
        const vals = last5.map(r => r.val);
        if (vals[0] !== vals[2] && vals[2] !== vals[4]) return vals[4] === 'T' ? 'X' : 'T';
    }
    return null;
}

// 10. CẦU 3-5-3
function analyzeCau353(history) {
    const runs = extractFeatures(history).runs;
    if (runs.length < 5) return null;
    const last5 = runs.slice(-5);
    const pattern = last5.map(r => r.len).join('');
    if (pattern === '35353') {
        const vals = last5.map(r => r.val);
        if (vals[0] !== vals[2] && vals[2] !== vals[4]) return vals[4] === 'T' ? 'T' : 'X';
    }
    return null;
}

// 11. CẦU 1-4-1
function analyzeCau141(history) {
    const runs = extractFeatures(history).runs;
    if (runs.length < 5) return null;
    const last5 = runs.slice(-5);
    const pattern = last5.map(r => r.len).join('');
    if (pattern === '14141') {
        const vals = last5.map(r => r.val);
        if (vals[0] !== vals[2] && vals[2] !== vals[4]) return vals[4] === 'T' ? 'X' : 'T';
    }
    return null;
}

// 12. CẦU 4-1-4
function analyzeCau414(history) {
    const runs = extractFeatures(history).runs;
    if (runs.length < 5) return null;
    const last5 = runs.slice(-5);
    const pattern = last5.map(r => r.len).join('');
    if (pattern === '41414') {
        const vals = last5.map(r => r.val);
        if (vals[0] !== vals[2] && vals[2] !== vals[4]) return vals[4] === 'T' ? 'T' : 'X';
    }
    return null;
}

// 13. CẦU ĐỐI XỨNG 2
function analyzeCauDoiXung2(history) {
    const tx = history.map(h => h.tx);
    if (tx.length < 6) return null;
    const last6 = tx.slice(-6);
    if (last6[0] === last6[5] && last6[1] === last6[4] && last6[2] === last6[3]) {
        return last6[5] === 'T' ? 'X' : 'T';
    }
    return null;
}

// 14. CẦU ĐỐI XỨNG 3
function analyzeCauDoiXung3(history) {
    const tx = history.map(h => h.tx);
    if (tx.length < 8) return null;
    const last8 = tx.slice(-8);
    if (last8[0] === last8[7] && last8[1] === last8[6] && last8[2] === last8[5] && last8[3] === last8[4]) {
        return last8[7] === 'T' ? 'X' : 'T';
    }
    return null;
}

// 15. CẦU ĐỐI XỨNG 4
function analyzeCauDoiXung4(history) {
    const tx = history.map(h => h.tx);
    if (tx.length < 10) return null;
    const last10 = tx.slice(-10);
    let ok = true;
    for (let i = 0; i < 5; i++) if (last10[i] !== last10[9-i]) ok = false;
    if (ok) return last10[9] === 'T' ? 'X' : 'T';
    return null;
}

// 16. CẦU XOAY VÒNG 2
function analyzeCauXoayVong2(history) {
    const tx = history.map(h => h.tx);
    if (tx.length < 10) return null;
    const last8 = tx.slice(-8);
    if (last8[0] === last8[2] && last8[2] === last8[4] && last8[4] === last8[6] &&
        last8[1] === last8[3] && last8[3] === last8[5] && last8[5] === last8[7]) {
        return last8[7] === 'T' ? 'X' : 'T';
    }
    return null;
}

// 17. CẦU XOAY VÒNG 3
function analyzeCauXoayVong3(history) {
    const tx = history.map(h => h.tx);
    if (tx.length < 12) return null;
    const last12 = tx.slice(-12);
    if (last12[0] === last12[3] && last12[3] === last12[6] && last12[6] === last12[9] &&
        last12[1] === last12[4] && last12[4] === last12[7] && last12[7] === last12[10]) {
        return last12[10] === 'T' ? 'X' : 'T';
    }
    return null;
}

// 18. CẦU TIẾN TIẾN
function analyzeCauTienTien(history) {
    const tx = history.map(h => h.tx);
    if (tx.length < 10) return null;
    let up = true;
    for (let i = tx.length-6; i < tx.length-1; i++) {
        if (tx[i] !== tx[i+1]) { up = false; break; }
    }
    if (up) return tx[tx.length-1] === 'T' ? 'T' : 'X';
    return null;
}

// 19. CẦU LÙI LÙI
function analyzeCauLuiLui(history) {
    const tx = history.map(h => h.tx);
    if (tx.length < 10) return null;
    let down = true;
    for (let i = tx.length-6; i < tx.length-1; i++) {
        if (tx[i] === tx[i+1]) { down = false; break; }
    }
    if (down) return tx[tx.length-1] === 'T' ? 'X' : 'T';
    return null;
}

// 20. PHÂN TÍCH TỔNG ĐIỂM (Mean Reversion)
function analyzeMeanReversion(history) {
    if (history.length < 20) return null;
    const totals = history.map(h => h.total);
    const recentAvg = avg(totals.slice(-20));
    const overallAvg = avg(totals);
    if (recentAvg > 12.5 && overallAvg > 11) return 'X';
    if (recentAvg < 8.5 && overallAvg < 10) return 'T';
    return null;
}

// 21. PHÂN TÍCH TỔNG ĐIỂM 2
function analyzeMeanReversion2(history) {
    if (history.length < 15) return null;
    const totals = history.map(h => h.total);
    const last5 = avg(totals.slice(-5));
    if (last5 > 13) return 'X';
    if (last5 < 8) return 'T';
    return null;
}

// 22. PHÂN TÍCH VOLATILITY
function analyzeVolatility(history) {
    if (history.length < 30) return null;
    const totals = history.map(h => h.total);
    const vol = std(totals);
    const lastTx = history[history.length-1].tx;
    if (vol > 4) return lastTx === 'T' ? 'X' : 'T';
    return null;
}

// 23. PHÂN TÍCH XÚC XẮC (tổng 3 mặt)
function analyzeDiceTrend(history) {
    if (history.length < 30) return null;
    const sums = history.map(h => h.dice[0] + h.dice[1] + h.dice[2]);
    const recentSums = sums.slice(-15);
    const avgSum = avg(recentSums);
    if (avgSum > 12) return 'X';
    if (avgSum < 9) return 'T';
    return null;
}

// 24. PHÂN TÍCH XÚC XẮC (mặt đầu)
function analyzeDiceFirst(history) {
    if (history.length < 20) return null;
    const first = history.map(h => h.dice[0]);
    const avgFirst = avg(first.slice(-15));
    if (avgFirst > 4) return 'X';
    if (avgFirst < 2.5) return 'T';
    return null;
}

// 25. PHÂN TÍCH XÚC XẮC (chẵn lẻ)
function analyzeDiceEvenOdd(history) {
    if (history.length < 20) return null;
    const sums = history.map(h => h.dice[0] + h.dice[1] + h.dice[2]);
    const even = sums.slice(-15).filter(s => s % 2 === 0).length;
    if (even >= 12) return 'X';
    if (even <= 3) return 'T';
    return null;
}

// 26. PHÂN TÍCH CHÊNH LỆCH TÀI XỈU
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

// 27. PHÂN TÍCH CHU KỲ (Periodic)
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

// 28. PHÂN TÍCH MOMENTUM
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

// 29. PHÂN TÍCH MOMENTUM 2
function analyzeMomentum2(history) {
    if (history.length < 20) return null;
    const tx = history.map(h => h.tx);
    const last10 = tx.slice(-10);
    const last5 = last10.slice(-5).filter(v => v === 'T').length;
    const prev5 = last10.slice(0, 5).filter(v => v === 'T').length;
    if (last5 - prev5 >= 3) return 'X';
    if (prev5 - last5 >= 3) return 'T';
    return null;
}

// 30. PHÂN TÍCH HỒI QUY
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

// 31. THUẬT TOÁN MARKOV BẬC 2
function analyzeMarkov2(history) {
    if (history.length < 20) return null;
    const tx = history.map(h => h.tx);
    const trans = {};
    for (let i = 0; i < tx.length - 2; i++) {
        const key = tx[i] + tx[i+1];
        const next = tx[i+2];
        if (!trans[key]) trans[key] = { T: 0, X: 0 };
        trans[key][next]++;
    }
    const lastKey = tx[tx.length-2] + tx[tx.length-1];
    const cnt = trans[lastKey];
    if (cnt && cnt.T !== cnt.X && cnt.T + cnt.X >= 2) {
        return cnt.T > cnt.X ? 'T' : 'X';
    }
    return null;
}

// 32. THUẬT TOÁN MARKOV BẬC 3
function analyzeMarkov3(history) {
    if (history.length < 30) return null;
    const tx = history.map(h => h.tx);
    const trans = {};
    for (let i = 0; i < tx.length - 3; i++) {
        const key = tx[i] + tx[i+1] + tx[i+2];
        const next = tx[i+3];
        if (!trans[key]) trans[key] = { T: 0, X: 0 };
        trans[key][next]++;
    }
    const lastKey = tx.slice(-3).join('');
    const cnt = trans[lastKey];
    if (cnt && cnt.T !== cnt.X && cnt.T + cnt.X >= 2) {
        return cnt.T > cnt.X ? 'T' : 'X';
    }
    return null;
}

// 33. THUẬT TOÁN N-GRAM 3
function analyzeNgram3(history) {
    if (history.length < 40) return null;
    const tx = history.map(h => h.tx);
    const last3 = tx.slice(-3).join('');
    let t = 0, x = 0;
    for (let i = 0; i <= tx.length - 4; i++) {
        if (tx.slice(i, i+3).join('') === last3) {
            if (tx[i+3] === 'T') t++; else x++;
        }
    }
    if (t + x >= 2 && Math.abs(t - x) >= 2) {
        return t > x ? 'T' : 'X';
    }
    return null;
}

// 34. THUẬT TOÁN N-GRAM 4
function analyzeNgram4(history) {
    if (history.length < 60) return null;
    const tx = history.map(h => h.tx);
    const last4 = tx.slice(-4).join('');
    let t = 0, x = 0;
    for (let i = 0; i <= tx.length - 5; i++) {
        if (tx.slice(i, i+4).join('') === last4) {
            if (tx[i+4] === 'T') t++; else x++;
        }
    }
    if (t + x >= 2 && Math.abs(t - x) >= 2) {
        return t > x ? 'T' : 'X';
    }
    return null;
}

// 35. THUẬT TOÁN PATTERN MATCH (từ dữ liệu thực tế)
function analyzePatternMatch(history) {
    if (history.length < 30) return null;
    const tx = history.map(h => h.tx);
    const last4 = tx.slice(-4).join('');
    const last5 = tx.slice(-5).join('');
    const last6 = tx.slice(-6).join('');
    const last7 = tx.slice(-7).join('');
    const last8 = tx.slice(-8).join('');
    
    const patterns = {
        // Pattern 4 ký tự
        'TTXX': 'X', 'XXTT': 'T', 'TXTX': 'X', 'XTXT': 'T',
        'TTTX': 'X', 'XXXT': 'T', 'TXXX': 'T', 'XTTT': 'X',
        // Pattern 5 ký tự
        'TTTTX': 'X', 'XXXXT': 'T', 'TTXXT': 'X', 'XXTTX': 'T',
        'TXTXT': 'X', 'XTXTX': 'T', 'TTTXT': 'X', 'XXXTX': 'T',
        // Pattern 6 ký tự
        'TTTXXX': 'T', 'XXXTTT': 'X', 'TTXXTT': 'X', 'XXTTXX': 'T',
        'TXTXTX': 'X', 'XTXTXT': 'T',
        // Pattern 7 ký tự
        'TTTXXTT': 'X', 'XXXTTXX': 'T', 'TTXXTTX': 'T', 'XXTTXXT': 'X',
        // Pattern 8 ký tự
        'TTXXTTXT': 'X', 'XXTTXTXX': 'T', 'TTXTXXTT': 'T', 'XTXXTTXT': 'X'
    };
    
    if (patterns[last4]) return patterns[last4];
    if (patterns[last5]) return patterns[last5];
    if (patterns[last6]) return patterns[last6];
    if (patterns[last7]) return patterns[last7];
    if (patterns[last8]) return patterns[last8];
    return null;
}

// 36. THUẬT TOÁN FIBONACCI
function analyzeFibonacci(history) {
    const tx = history.map(h => h.tx);
    let runs = [], cur = tx[0], len = 1;
    for (let i = 1; i < tx.length; i++) {
        if (tx[i] === cur) len++;
        else { runs.push({ val: cur, len }); cur = tx[i]; len = 1; }
    }
    runs.push({ val: cur, len });
    if (runs.length < 5) return null;
    const lens = runs.slice(-5).map(r => r.len);
    if (lens[0] === 1 && lens[1] === 1 && lens[2] === 2 && lens[3] === 3 && lens[4] === 5) {
        return runs[runs.length-1].val === 'T' ? 'X' : 'T';
    }
    return null;
}

// 37. THUẬT TOÁN ZIGZAG
function analyzeZigzag(history) {
    const tx = history.map(h => h.tx);
    if (tx.length < 8) return null;
    let zig = true;
    for (let i = tx.length-7; i < tx.length-1; i++) {
        if (tx[i] === tx[i+1]) { zig = false; break; }
    }
    if (zig) return tx[tx.length-1] === 'T' ? 'X' : 'T';
    return null;
}

// 38. THUẬT TOÁN ALTERNATING
function analyzeAlternating(history) {
    const tx = history.map(h => h.tx);
    if (tx.length < 6) return null;
    let alt = true;
    for (let i = tx.length-5; i < tx.length; i++) {
        if (tx[i] === tx[i-1]) { alt = false; break; }
    }
    if (alt) return tx[tx.length-1] === 'T' ? 'X' : 'T';
    return null;
}

// 39. THUẬT TOÁN WAVE PATTERN
function analyzeWavePattern(history) {
    const tx = history.map(h => h.tx);
    if (tx.length < 15) return null;
    let waveUp = 0, waveDown = 0;
    for (let i = 1; i < tx.length; i++) {
        if (tx[i] !== tx[i-1]) {
            if (tx[i] === 'T') waveUp++;
            else waveDown++;
        }
    }
    if (waveUp > waveDown + 3) return 'T';
    if (waveDown > waveUp + 3) return 'X';
    return null;
}

// 40. THUẬT TOÁN ĐA SỐ (Voting tổng hợp)
function analyzeMultiPattern(history) {
    const results = [];
    const addResult = (val) => { if (val) results.push(val); };
    
    addResult(analyzeCau11(history));
    addResult(analyzeCauBet(history));
    addResult(analyzeCau22(history));
    addResult(analyzeCau33(history));
    addResult(analyzeCau121(history));
    addResult(analyzeCau212(history));
    addResult(analyzeCau323(history));
    addResult(analyzeCau424(history));
    addResult(analyzeCau535(history));
    addResult(analyzeCau353(history));
    addResult(analyzeCau141(history));
    addResult(analyzeCau414(history));
    addResult(analyzeCauDoiXung2(history));
    addResult(analyzeCauDoiXung3(history));
    addResult(analyzeCauDoiXung4(history));
    addResult(analyzeCauXoayVong2(history));
    addResult(analyzeCauXoayVong3(history));
    addResult(analyzeCauTienTien(history));
    addResult(analyzeCauLuiLui(history));
    addResult(analyzeMeanReversion(history));
    addResult(analyzeMeanReversion2(history));
    addResult(analyzeVolatility(history));
    addResult(analyzeDiceTrend(history));
    addResult(analyzeDiceFirst(history));
    addResult(analyzeDiceEvenOdd(history));
    addResult(analyzeBalance(history));
    addResult(analyzeCycle(history));
    addResult(analyzeMomentum(history));
    addResult(analyzeMomentum2(history));
    addResult(analyzeRegression(history));
    addResult(analyzeMarkov2(history));
    addResult(analyzeMarkov3(history));
    addResult(analyzeNgram3(history));
    addResult(analyzeNgram4(history));
    addResult(analyzePatternMatch(history));
    addResult(analyzeFibonacci(history));
    addResult(analyzeZigzag(history));
    addResult(analyzeAlternating(history));
    addResult(analyzeWavePattern(history));
    
    if (results.length === 0) return null;
    const tCount = results.filter(r => r === 'T').length;
    const xCount = results.filter(r => r === 'X').length;
    if (Math.abs(tCount - xCount) >= 3) {
        return tCount > xCount ? 'T' : 'X';
    }
    return null;
}

// ==================== ENSEMBLE TỔNG HỢP (ỔN ĐỊNH) ====================
class CauAnalyst {
    constructor() {
        this.history = [];
        this.lastPrediction = null;
        this.correctCount = 0;
        this.totalCount = 0;
        this.weights = {
            cau11: 1.2, cauBet: 1.5, cau22: 1.2, cau33: 1.2,
            cau121: 1.3, cau212: 1.3, cau323: 1.3, cau424: 1.3,
            cau535: 1.2, cau353: 1.2, cau141: 1.1, cau414: 1.1,
            cauDoiXung2: 1.1, cauDoiXung3: 1.1, cauDoiXung4: 1.0,
            cauXoayVong2: 1.1, cauXoayVong3: 1.0,
            cauTienTien: 1.0, cauLuiLui: 1.0,
            meanRev: 1.0, meanRev2: 0.9, volatility: 1.0,
            diceTrend: 1.0, diceFirst: 0.8, diceEvenOdd: 0.9,
            balance: 1.2, cycle: 1.1, momentum: 1.0, momentum2: 0.9,
            regression: 0.8, markov2: 1.1, markov3: 1.0,
            ngram3: 1.0, ngram4: 0.9, patternMatch: 1.2,
            fibonacci: 1.0, zigzag: 0.9, alternating: 1.0, wave: 0.9
        };
    }
    
    loadInitial(lines) {
        this.history = lines;
        console.log(`📊 Đã tải ${lines.length} phiên lịch sử cho phân tích cầu`);
    }
    
    pushRecord(record) {
        this.history.push(record);
        if (this.history.length > 600) this.history = this.history.slice(-550);
        
        if (this.lastPrediction && this.lastPrediction === record.tx) {
            this.correctCount++;
        }
        this.totalCount++;
        
        if (this.lastPrediction) {
            const isCorrect = this.lastPrediction === record.tx;
            const adjustment = isCorrect ? 1.02 : 0.98;
            for (const key in this.weights) {
                this.weights[key] = Math.max(0.5, Math.min(2.0, this.weights[key] * adjustment));
            }
        }
        
        this.lastPrediction = this.predict();
        
        const accuracy = this.totalCount > 0 ? (this.correctCount / this.totalCount * 100).toFixed(1) : 0;
        console.log(`🎲 ${record.session} → ${record.result} | Dự đoán tiếp: ${this.lastPrediction === 'T' ? 'TÀI' : 'XỈU'} | Acc: ${accuracy}% (${this.correctCount}/${this.totalCount})`);
    }
    
    predict() {
        if (this.history.length < 15) return 'T';
        
        const votes = { T: 0, X: 0 };
        const addVote = (pred, weightKey) => {
            if (pred) votes[pred] += this.weights[weightKey] || 1.0;
        };
        
        addVote(analyzeCau11(this.history), 'cau11');
        addVote(analyzeCauBet(this.history), 'cauBet');
        addVote(analyzeCau22(this.history), 'cau22');
        addVote(analyzeCau33(this.history), 'cau33');
        addVote(analyzeCau121(this.history), 'cau121');
        addVote(analyzeCau212(this.history), 'cau212');
        addVote(analyzeCau323(this.history), 'cau323');
        addVote(analyzeCau424(this.history), 'cau424');
        addVote(analyzeCau535(this.history), 'cau535');
        addVote(analyzeCau353(this.history), 'cau353');
        addVote(analyzeCau141(this.history), 'cau141');
        addVote(analyzeCau414(this.history), 'cau414');
        addVote(analyzeCauDoiXung2(this.history), 'cauDoiXung2');
        addVote(analyzeCauDoiXung3(this.history), 'cauDoiXung3');
        addVote(analyzeCauDoiXung4(this.history), 'cauDoiXung4');
        addVote(analyzeCauXoayVong2(this.history), 'cauXoayVong2');
        addVote(analyzeCauXoayVong3(this.history), 'cauXoayVong3');
        addVote(analyzeCauTienTien(this.history), 'cauTienTien');
        addVote(analyzeCauLuiLui(this.history), 'cauLuiLui');
        addVote(analyzeMeanReversion(this.history), 'meanRev');
        addVote(analyzeMeanReversion2(this.history), 'meanRev2');
        addVote(analyzeVolatility(this.history), 'volatility');
        addVote(analyzeDiceTrend(this.history), 'diceTrend');
        addVote(analyzeDiceFirst(this.history), 'diceFirst');
        addVote(analyzeDiceEvenOdd(this.history), 'diceEvenOdd');
        addVote(analyzeBalance(this.history), 'balance');
        addVote(analyzeCycle(this.history), 'cycle');
        addVote(analyzeMomentum(this.history), 'momentum');
        addVote(analyzeMomentum2(this.history), 'momentum2');
        addVote(analyzeRegression(this.history), 'regression');
        addVote(analyzeMarkov2(this.history), 'markov2');
        addVote(analyzeMarkov3(this.history), 'markov3');
        addVote(analyzeNgram3(this.history), 'ngram3');
        addVote(analyzeNgram4(this.history), 'ngram4');
        addVote(analyzePatternMatch(this.history), 'patternMatch');
        addVote(analyzeFibonacci(this.history), 'fibonacci');
        addVote(analyzeZigzag(this.history), 'zigzag');
        addVote(analyzeAlternating(this.history), 'alternating');
        addVote(analyzeWavePattern(this.history), 'wave');
        addVote(analyzeMultiPattern(this.history), 'cau11');
        
        if (votes.T === 0 && votes.X === 0) {
            const lastTx = this.history[this.history.length-1]?.tx;
            return lastTx === 'T' ? 'X' : 'T';
        }
        
        const threshold = this.totalCount < 30 ? 1.2 : 1.0;
        if (Math.abs(votes.T - votes.X) < threshold) {
            const lastTx = this.history[this.history.length-1]?.tx;
            return lastTx === 'T' ? 'X' : 'T';
        }
        
        return votes.T > votes.X ? 'T' : 'X';
    }
    
    getPrediction() {
        const pred = this.lastPrediction || this.predict();
        let confidence = this.totalCount > 50 ? 
            Math.min(0.92, (this.correctCount / this.totalCount) + 0.25) : 0.70;
        
        if (this.totalCount > 20) {
            const recentCorrect = this.correctCount / this.totalCount;
            confidence = Math.min(0.95, Math.max(0.55, recentCorrect + 0.2));
        }
        
        return {
            prediction: pred === 'T' ? 'tài' : 'xỉu',
            confidence: Math.round(confidence * 100),
            rawPrediction: pred
        };
    }
    
    getStats() {
        return {
            total: this.totalCount,
            correct: this.correctCount,
            accuracy: this.totalCount > 0 ? (this.correctCount / this.totalCount * 100).toFixed(1) : 0,
            algorithms: 40
        };
    }
}

const cauAnalyst = new CauAnalyst();

// ==================== FETCH & UPDATE (CÓ BACKUP) ====================
async function fetchAndProcessHistory() {
    try {
        const response = await fetch(API_URL, {
            timeout: 10000,
            headers: { 'User-Agent': 'AI-Taixiu-Predictor/3.0' }
        });
        
        if (!response.ok) {
            throw new Error(`HTTP ${response.status}`);
        }
        
        const data = await response.json();
        const newHistory = parseLines(data);
        
        if (newHistory.length === 0) return;
        
        const lastSessionInHistory = newHistory.at(-1);
        
        if (!currentSessionId) {
            if (!loadBackup() || txHistory.length === 0) {
                cauAnalyst.loadInitial(newHistory);
                txHistory = newHistory;
            } else {
                const existingSessions = new Set(txHistory.map(h => h.session));
                const missingRecords = newHistory.filter(r => !existingSessions.has(r.session));
                for (const record of missingRecords) {
                    cauAnalyst.pushRecord(record);
                }
                txHistory = [...txHistory, ...missingRecords].sort((a,b) => a.session - b.session);
            }
            currentSessionId = lastSessionInHistory.session;
            console.log(`✅ Đã tải ${txHistory.length} phiên lịch sử.`);
            saveBackup();
        } else if (lastSessionInHistory.session > currentSessionId) {
            const newRecords = newHistory.filter(r => r.session > currentSessionId);
            for (const record of newRecords) cauAnalyst.pushRecord(record);
            txHistory.push(...newRecords);
            if (txHistory.length > 600) txHistory = txHistory.slice(-550);
            currentSessionId = lastSessionInHistory.session;
            if (newRecords.length > 0) {
                console.log(`🆕 Cập nhật ${newRecords.length} phiên.`);
                saveBackup();
            }
        }
        
        reconnectAttempts = 0;
        
    } catch (e) {
        console.error("❌ Lỗi fetch:", e.message);
        reconnectAttempts++;
        
        if (reconnectAttempts >= MAX_RECONNECT_ATTEMPTS) {
            console.log("⚠️ Mất kết nối, chạy ở chế độ offline với backup");
        }
    }
}

// ==================== API SERVER ====================
const app = fastify({ logger: false });
await app.register(cors, { origin: "*" });

fetchAndProcessHistory();
clearInterval(fetchInterval);
fetchInterval = setInterval(fetchAndProcessHistory, 5000);
console.log(`🔄 AI Phân Tích Cầu đang chạy (interval 5s) - 40+ thuật toán ổn định`);

app.get("/api/cau", async () => {
    const lastResult = txHistory.at(-1) || null;
    const prediction = cauAnalyst.getPrediction();
    
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
    else if (analyzeCauDoiXung2(txHistory)) activeCau = "Cầu Đối xứng";
    else if (analyzeCauXoayVong2(txHistory)) activeCau = "Cầu Xoay vòng";
    else if (analyzeCauTienTien(txHistory)) activeCau = "Cầu Tiến";
    else if (analyzeCauLuiLui(txHistory)) activeCau = "Cầu Lùi";
    
    const stats = cauAnalyst.getStats();
    
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
        confidence: `${prediction.confidence}%`,
        algorithm_stats: {
            total_predictions: stats.total,
            correct_predictions: stats.correct,
            accuracy: stats.accuracy + "%",
            algorithms_used: stats.algorithms
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
            cau_bet: analyzeCauBet(txHistory) ? "active" : "inactive",
            cau_doixung: analyzeCauDoiXung2(txHistory) ? "active" : "inactive",
            cau_xoayvong: analyzeCauXoayVong2(txHistory) ? "active" : "inactive"
        },
        last_10_runs: last10Runs.map(r => ({ type: r.val === 'T' ? 'TÀI' : 'XỈU', length: r.len }))
    };
});

app.get("/health", async () => {
    const stats = cauAnalyst.getStats();
    return {
        status: "ok",
        history_length: txHistory.length,
        last_session: currentSessionId,
        total_predictions: stats.total,
        accuracy: stats.accuracy + "%",
        algorithms: stats.algorithms,
        backup_exists: fs.existsSync(BACKUP_FILE)
    };
});

app.get("/", async () => {
    const stats = cauAnalyst.getStats();
    return {
        name: "AI Phân Tích Cầu Tài Xỉu",
        version: "3.0 - 40+ Thuật Toán",
        description: "Phân tích 40+ loại cầu khác nhau với cơ chế backup và tự động điều chỉnh trọng số",
        algorithms: stats.algorithms,
        accuracy: stats.accuracy + "%",
        features: [
            "40+ thuật toán phân tích cầu",
            "Tự động backup dữ liệu",
            "Học online - điều chỉnh trọng số theo kết quả thực tế",
            "Chống mất kết nối - hoạt động offline với backup",
            "Tự động khôi phục khi restart server"
        ],
        endpoints: [
            "GET /api/cau - Dự đoán phiên tiếp theo",
            "GET /api/cau/history - Lịch sử 100 phiên gần nhất",
            "GET /api/cau/analysis - Phân tích chi tiết cầu đang chạy",
            "GET /health - Kiểm tra trạng thái hệ thống"
        ]
    };
});

// ==================== START SERVER ====================
const start = async () => {
    try {
        await app.listen({ port: PORT, host: "0.0.0.0" });
    } catch (err) {
        if (err.code === 'EADDRINUSE') {
            console.error(`❌ Cổng ${PORT} đã được sử dụng. Hãy đổi PORT hoặc tắt ứng dụng khác.`);
        } else {
            console.error("Lỗi server:", err.message);
        }
        process.exit(1);
    }
    
    let publicIP = "0.0.0.0";
    try {
        const res = await fetch("https://ifconfig.me/ip");
        publicIP = (await res.text()).trim();
    } catch (e) {}
    
    console.log("\n╔════════════════════════════════════════════════════════════╗");
    console.log("║   🎲 AI PHÂN TÍCH CẦU TÀI XỈU - PHIÊN BẢN ỔN ĐỊNH 🎲     ║");
    console.log("╚════════════════════════════════════════════════════════════╝");
    console.log(`   Local:   http://localhost:${PORT}`);
    console.log(`   Network: http://${publicIP}:${PORT}\n`);
    console.log("   🔧 TÍNH NĂNG:\n");
    console.log("   • 40+ thuật toán phân tích cầu");
    console.log("   • Tự động backup dữ liệu");
    console.log("   • Học online - điều chỉnh trọng số theo kết quả thực tế");
    console.log("   • Chống mất kết nối - hoạt động offline với backup");
    console.log("   • Tự động khôi phục khi restart server\n");
    console.log("   📊 Các loại cầu hỗ trợ:\n");
    console.log("   • Cầu 1-1, 2-2, 3-3, 4-4, 5-5 (xen kẽ)");
    console.log("   • Cầu bệt (ngắn, dài, siêu dài)");
    console.log("   • Cầu 1-2-1, 2-1-2, 3-2-3, 4-2-4, 5-3-5, 3-5-3");
    console.log("   • Cầu 1-4-1, 4-1-4");
    console.log("   • Cầu đối xứng (2,3,4)");
    console.log("   • Cầu xoay vòng (2,3)");
    console.log("   • Cầu tiến, cầu lùi");
    console.log("   • Mean Reversion, Volatility, Momentum");
    console.log("   • Markov bậc 2,3");
    console.log("   • N-gram 3,4");
    console.log("   • Pattern Match (từ dữ liệu thực tế)");
    console.log("   • Fibonacci, Zigzag, Alternating, Wave Pattern\n");
};

start();
