import json
import threading
import time
import os
import logging
import collections
import math
from datetime import datetime, timezone
from urllib.request import urlopen, Request
from flask import Flask, jsonify, request as flask_request
 
# ──────────────────────────────────────────────────────────────────────────────
# CẤU HÌNH HỆ THỐNG
# ──────────────────────────────────────────────────────────────────────────────
 
logging.basicConfig(
    level=logging.INFO,
    format='[%(asctime)s] [%(levelname)s] %(message)s'
)
logger = logging.getLogger(__name__)
 
HOST            = '0.0.0.0'
POLL_INTERVAL   = 5          # Giây giữa mỗi lần poll
RETRY_DELAY     = 5          # Giây chờ khi lỗi
MAX_HISTORY     = 50         # Số phiên lịch sử tối đa
MIN_DATA_POINTS = 5          # Số phiên tối thiểu để bắt đầu dự đoán
 
# Cấu hình thuật toán
PATTERN_WINDOW          = 6   # Độ dài chuỗi pattern so khớp
MARKOV_ORDER            = 3   # Bậc của Markov chain
TREND_WINDOW            = 10  # Cửa sổ phát hiện xu hướng
STREAK_WEIGHT           = 1.5 # Trọng số khi có chuỗi liên tiếp
FREQUENCY_WINDOW        = 20  # Cửa sổ phân tích tần suất
 
# ──────────────────────────────────────────────────────────────────────────────
# TRẠNG THÁI TOÀN CỤC
# ──────────────────────────────────────────────────────────────────────────────
 
lock_tx = threading.Lock()
 
# Kết quả mới nhất
latest_result_tx = {
    "Phien": 0,
    "Xuc_xac_1": 0,
    "Xuc_xac_2": 0,
    "Xuc_xac_3": 0,
    "Tong": 0,
    "Ket_qua": "Chưa có",
    "id": "@ledat09878",
    "server_time": "",
    "update_count": 0,
    "Du_doan": {
        "Phien_tiep": 0,
        "Du_doan": "Chưa đủ dữ liệu",
        "Do_tin_cay": 0.0,
        "Chien_luoc": "Chưa đủ dữ liệu",
        "Chi_tiet_chien_luoc": {}
    },
    "Thong_ke": {
        "Tong_phien": 0,
        "Du_doan_dung": 0,
        "Du_doan_sai": 0,
        "Ti_le_dung": 0.0,
        "Chuoi_dung_hien_tai": 0,
        "Chuoi_dung_cao_nhat": 0,
        "Tai_count": 0,
        "Xiu_count": 0
    }
}
 
# Lịch sử phiên
history_tx = []
 
# Tracking dự đoán để tính đúng/sai
pending_prediction = {
    "Phien_du_doan": None,   # Phiên mà dự đoán đang chờ verify
    "Du_doan": None,         # Kết quả dự đoán: "Tài" / "Xỉu"
    "Da_verify": False
}
 
# Thống kê tổng hợp
stats_tx = {
    "Tong_phien": 0,
    "Du_doan_dung": 0,
    "Du_doan_sai": 0,
    "Ti_le_dung": 0.0,
    "Chuoi_dung_hien_tai": 0,
    "Chuoi_dung_cao_nhat": 0,
    "Tai_count": 0,
    "Xiu_count": 0,
    "Chi_tiet_chien_luoc": {}
}
 
last_sid_tx = None
sid_for_tx  = None
 
# ──────────────────────────────────────────────────────────────────────────────
# THUẬT TOÁN DỰ ĐOÁN
# ──────────────────────────────────────────────────────────────────────────────
 
class PredictionEngine:
    """
    Engine dự đoán kết hợp đa chiến lược:
      1. Markov Chain     – mô hình xác suất chuyển trạng thái
      2. Pattern Matching – khớp chuỗi lịch sử gần nhất
      3. Frequency Bias   – xu hướng tần suất cân bằng
      4. Streak Breaker   – phá chuỗi khi quá dài
      5. Hot/Cold Number  – tổng xúc xắc nóng/lạnh
    Tổng hợp bằng weighted voting.
    """
 
    def __init__(self):
        self.strategy_stats = {}
 
    # ── Helpers ───────────────────────────────────────────────────────────────
 
    @staticmethod
    def _ket_qua_list(history):
        """Trả về list 'Tài'/'Xỉu' từ history (mới nhất trước)."""
        return [h["Ket_qua"] for h in history if h.get("Ket_qua") in ("Tài", "Xỉu")]
 
    @staticmethod
    def _tong_list(history):
        """Trả về list tổng từ history."""
        return [h["Tong"] for h in history if "Tong" in h]
 
    # ── Chiến lược 1: Markov Chain ───────────────────────────────────────────
 
    def strategy_markov(self, history, order=MARKOV_ORDER):
        """
        Dùng Markov Chain bậc `order`.
        Xây dựng bảng chuyển trạng thái từ lịch sử,
        rồi dự đoán dựa trên chuỗi hiện tại.
        """
        results = self._ket_qua_list(history)
        if len(results) < order + 2:
            return None, 0.5
 
        # Xây bảng chuyển
        transition = collections.defaultdict(lambda: {"Tài": 0, "Xỉu": 0})
        for i in range(len(results) - order):
            key = tuple(results[i: i + order])
            next_val = results[i + order]
            transition[key][next_val] += 1
 
        # Chuỗi hiện tại (đảo ngược vì mới nhất đứng đầu)
        current_seq = tuple(reversed(results[:order]))
        counts = transition.get(current_seq)
 
        if not counts or (counts["Tài"] + counts["Xỉu"]) == 0:
            # Thử bậc thấp hơn
            if order > 1:
                return self.strategy_markov(history, order - 1)
            return None, 0.5
 
        total = counts["Tài"] + counts["Xỉu"]
        tai_prob = counts["Tài"] / total
        xiu_prob = counts["Xỉu"] / total
 
        if tai_prob > xiu_prob:
            return "Tài", tai_prob
        elif xiu_prob > tai_prob:
            return "Xỉu", xiu_prob
        else:
            return None, 0.5
 
    # ── Chiến lược 2: Pattern Matching ───────────────────────────────────────
 
    def strategy_pattern(self, history, window=PATTERN_WINDOW):
        """
        So khớp chuỗi `window` phiên gần nhất với lịch sử,
        thống kê phiên tiếp theo sau mỗi lần khớp.
        """
        results = self._ket_qua_list(history)
        if len(results) < window + 1:
            return None, 0.5
 
        # Chuỗi cần so khớp (window phiên gần nhất, đảo chiều)
        target = tuple(reversed(results[:window]))
        reversed_results = list(reversed(results))
 
        tai_count = 0
        xiu_count = 0
        for i in range(len(reversed_results) - window):
            candidate = tuple(reversed_results[i: i + window])
            if candidate == target:
                next_val = reversed_results[i + window]
                if next_val == "Tài":
                    tai_count += 1
                else:
                    xiu_count += 1
 
        total = tai_count + xiu_count
        if total == 0:
            # Thử window nhỏ hơn
            if window > 2:
                return self.strategy_pattern(history, window - 1)
            return None, 0.5
 
        tai_prob = tai_count / total
        xiu_prob = xiu_count / total
 
        if tai_prob > xiu_prob:
            return "Tài", tai_prob
        elif xiu_prob > tai_prob:
            return "Xỉu", xiu_prob
        else:
            return None, 0.5
 
    # ── Chiến lược 3: Frequency Bias ─────────────────────────────────────────
 
    def strategy_frequency(self, history, window=FREQUENCY_WINDOW):
        """
        Khi một bên xuất hiện quá nhiều trong `window` phiên,
        dự đoán phần bù để cân bằng (regression to mean).
        """
        results = self._ket_qua_list(history)
        sample = results[:window]
        if len(sample) < 6:
            return None, 0.5
 
        tai_count = sample.count("Tài")
        xiu_count = sample.count("Xỉu")
        total = len(sample)
 
        tai_ratio = tai_count / total
        xiu_ratio = xiu_count / total
 
        # Nếu lệch > 65%, dự đoán ngược lại
        if tai_ratio > 0.65:
            confidence = 0.5 + (tai_ratio - 0.5) * 0.6
            return "Xỉu", min(confidence, 0.75)
        elif xiu_ratio > 0.65:
            confidence = 0.5 + (xiu_ratio - 0.5) * 0.6
            return "Tài", min(confidence, 0.75)
 
        # Tiếp tục theo xu hướng nhẹ
        if tai_ratio > xiu_ratio:
            return "Tài", 0.5 + (tai_ratio - xiu_ratio) * 0.3
        elif xiu_ratio > tai_ratio:
            return "Xỉu", 0.5 + (xiu_ratio - tai_ratio) * 0.3
 
        return None, 0.5
 
    # ── Chiến lược 4: Streak Breaker ─────────────────────────────────────────
 
    def strategy_streak(self, history):
        """
        Đếm chuỗi liên tiếp hiện tại.
        Chuỗi >= 4: xác suất đứt chuỗi tăng mạnh.
        Chuỗi 2-3: xu hướng tiếp tục chuỗi nhẹ.
        """
        results = self._ket_qua_list(history)
        if len(results) < 2:
            return None, 0.5
 
        current = results[0]
        streak = 1
        for r in results[1:]:
            if r == current:
                streak += 1
            else:
                break
 
        if streak >= 5:
            # Xác suất cao đứt chuỗi
            opposite = "Xỉu" if current == "Tài" else "Tài"
            confidence = min(0.5 + streak * 0.06, 0.85)
            return opposite, confidence
        elif streak == 4:
            opposite = "Xỉu" if current == "Tài" else "Tài"
            return opposite, 0.68
        elif streak == 3:
            opposite = "Xỉu" if current == "Tài" else "Tài"
            return opposite, 0.58
        elif streak == 2:
            # Có thể tiếp tục
            return current, 0.55
        else:
            # Streak = 1, khó đoán
            return None, 0.5
 
    # ── Chiến lược 5: Hot/Cold Sum Analysis ──────────────────────────────────
 
    def strategy_sum_analysis(self, history, window=15):
        """
        Phân tích phân phối tổng xúc xắc.
        Tổng từ 3-10 = Xỉu, 11-18 = Tài.
        Xem tổng nào đang 'nóng' và dự đoán dựa trên xác suất thực.
        """
        tong_list = self._tong_list(history)
        sample = tong_list[:window]
        if len(sample) < 5:
            return None, 0.5
 
        # Xác suất lý thuyết Tài: ~49.54%, Xỉu: ~50.46%
        # (với 3 xúc xắc cân đối)
        tai_sums = [s for s in sample if s > 10]
        xiu_sums = [s for s in sample if s <= 10]
 
        tai_avg = sum(tai_sums) / len(tai_sums) if tai_sums else 0
        xiu_avg = sum(xiu_sums) / len(xiu_sums) if xiu_sums else 0
 
        tai_ratio = len(tai_sums) / len(sample)
        xiu_ratio = len(xiu_sums) / len(sample)
 
        # Tính entropy để đánh giá độ ổn định
        if tai_ratio > 0 and xiu_ratio > 0:
            entropy = -(tai_ratio * math.log2(tai_ratio) + xiu_ratio * math.log2(xiu_ratio))
        else:
            entropy = 0
 
        # Entropy cao (gần 1) = cân bằng = khó đoán
        if entropy > 0.95:
            return None, 0.5
 
        if tai_ratio > 0.6:
            # Tài đang hot, xu hướng đổi sang Xỉu
            return "Xỉu", 0.52 + (tai_ratio - 0.6) * 0.5
        elif xiu_ratio > 0.6:
            # Xỉu đang hot, xu hướng đổi sang Tài
            return "Tài", 0.52 + (xiu_ratio - 0.6) * 0.5
 
        # Dựa vào trung bình tổng gần nhất
        recent_3 = tong_list[:3]
        if recent_3:
            avg_recent = sum(recent_3) / len(recent_3)
            if avg_recent > 11.5:
                return "Xỉu", 0.54  # Tổng đang cao, có thể về thấp
            elif avg_recent < 9.5:
                return "Tài", 0.54  # Tổng đang thấp, có thể lên cao
 
        return None, 0.5
 
    # ── Tổng hợp (Ensemble Voting) ────────────────────────────────────────────
 
    def predict(self, history):
        """
        Kết hợp tất cả chiến lược bằng weighted voting.
        Trả về: (du_doan, do_tin_cay, chien_luoc_chinh, chi_tiet)
        """
        if len(history) < MIN_DATA_POINTS:
            return "Chưa đủ dữ liệu", 0.0, "Chưa đủ dữ liệu", {}
 
        strategies = {
            "Markov":    (self.strategy_markov,    1.8),
            "Pattern":   (self.strategy_pattern,   1.6),
            "Frequency": (self.strategy_frequency, 1.2),
            "Streak":    (self.strategy_streak,    1.5),
            "SumAnalysis": (self.strategy_sum_analysis, 1.0),
        }
 
        votes = {"Tài": 0.0, "Xỉu": 0.0}
        detail = {}
        dominant_strategy = None
        dominant_confidence = 0.0
 
        for name, (func, weight) in strategies.items():
            try:
                pred, conf = func(history)
                detail[name] = {
                    "Du_doan": pred if pred else "Không rõ",
                    "Do_tin_cay": round(conf * 100, 1)
                }
                if pred in ("Tài", "Xỉu"):
                    votes[pred] += weight * conf
                    if weight * conf > dominant_confidence:
                        dominant_confidence = weight * conf
                        dominant_strategy = name
            except Exception as e:
                logger.warning(f"Chiến lược {name} lỗi: {e}")
                detail[name] = {"Du_doan": "Lỗi", "Do_tin_cay": 0}
 
        total_weight = votes["Tài"] + votes["Xỉu"]
        if total_weight == 0:
            return "Không xác định", 0.0, "Không rõ", detail
 
        tai_prob = votes["Tài"] / total_weight
        xiu_prob = votes["Xỉu"] / total_weight
 
        if tai_prob > xiu_prob:
            final_pred = "Tài"
            final_conf = tai_prob
        elif xiu_prob > tai_prob:
            final_pred = "Xỉu"
            final_conf = xiu_prob
        else:
            final_pred = "Không xác định"
            final_conf = 0.5
 
        # Giảm confidence nếu các chiến lược mâu thuẫn nhiều
        conflict_ratio = min(votes["Tài"], votes["Xỉu"]) / max(total_weight, 1)
        final_conf = final_conf * (1 - conflict_ratio * 0.3)
 
        return (
            final_pred,
            round(final_conf * 100, 1),
            dominant_strategy or "Tổng hợp",
            detail
        )
 
 
# Khởi tạo engine
engine = PredictionEngine()
 
# ──────────────────────────────────────────────────────────────────────────────
# QUẢN LÝ THỐNG KÊ
# ──────────────────────────────────────────────────────────────────────────────
 
def verify_and_update_stats(actual_result, actual_phien):
    """
    Kiểm tra dự đoán trước với kết quả thực,
    cập nhật thống kê đúng/sai.
    """
    global pending_prediction, stats_tx
 
    with lock_tx:
        pred_info = pending_prediction.copy()
 
    if (
        pred_info["Phien_du_doan"] is not None
        and pred_info["Phien_du_doan"] == actual_phien
        and not pred_info["Da_verify"]
        and pred_info["Du_doan"] in ("Tài", "Xỉu")
    ):
        is_correct = (pred_info["Du_doan"] == actual_result)
 
        with lock_tx:
            stats_tx["Tong_phien"] += 1
            if is_correct:
                stats_tx["Du_doan_dung"] += 1
                stats_tx["Chuoi_dung_hien_tai"] += 1
                stats_tx["Chuoi_dung_cao_nhat"] = max(
                    stats_tx["Chuoi_dung_cao_nhat"],
                    stats_tx["Chuoi_dung_hien_tai"]
                )
            else:
                stats_tx["Du_doan_sai"] += 1
                stats_tx["Chuoi_dung_hien_tai"] = 0
 
            total = stats_tx["Du_doan_dung"] + stats_tx["Du_doan_sai"]
            stats_tx["Ti_le_dung"] = round(
                stats_tx["Du_doan_dung"] / total * 100, 1
            ) if total > 0 else 0.0
 
            pending_prediction["Da_verify"] = True
 
        result_str = "ĐÚNG ✓" if is_correct else "SAI ✗"
        logger.info(
            f"[VERIFY] Phiên {actual_phien}: Dự đoán={pred_info['Du_doan']}, "
            f"Thực tế={actual_result} → {result_str}"
        )
 
 
def update_frequency_stats(ket_qua):
    """Cập nhật số lần Tài/Xỉu."""
    with lock_tx:
        if ket_qua == "Tài":
            stats_tx["Tai_count"] += 1
        elif ket_qua == "Xỉu":
            stats_tx["Xiu_count"] += 1
 
 
# ──────────────────────────────────────────────────────────────────────────────
# CẬP NHẬT KẾT QUẢ
# ──────────────────────────────────────────────────────────────────────────────
 
def update_result(result):
    """
    Cập nhật latest_result_tx với kết quả mới,
    thực hiện dự đoán phiên tiếp theo,
    đồng thời verify dự đoán phiên trước.
    """
    global pending_prediction, latest_result_tx
 
    # 1. Verify dự đoán trước
    verify_and_update_stats(result["Ket_qua"], result["Phien"])
 
    # 2. Cập nhật tần suất
    update_frequency_stats(result["Ket_qua"])
 
    # 3. Chèn vào history (cần lock)
    with lock_tx:
        history_tx.insert(0, result.copy())
        if len(history_tx) > MAX_HISTORY:
            history_tx.pop()
 
    # 4. Chạy dự đoán phiên tiếp theo
    with lock_tx:
        hist_copy = list(history_tx)
        st_copy   = dict(stats_tx)
 
    du_doan, do_tin_cay, chien_luoc, chi_tiet = engine.predict(hist_copy)
 
    next_phien = (result["Phien"] + 1) if isinstance(result["Phien"], int) else result["Phien"]
 
    # 5. Lưu dự đoán để verify sau
    with lock_tx:
        pending_prediction = {
            "Phien_du_doan": next_phien,
            "Du_doan": du_doan,
            "Da_verify": False
        }
 
    # 6. Tổng hợp và cập nhật latest_result
    now = datetime.now(timezone.utc).isoformat(timespec="milliseconds").replace("+00:00", "Z")
 
    full_result = {
        "Phien":     result["Phien"],
        "Xuc_xac_1": result["Xuc_xac_1"],
        "Xuc_xac_2": result["Xuc_xac_2"],
        "Xuc_xac_3": result["Xuc_xac_3"],
        "Tong":      result["Tong"],
        "Ket_qua":   result["Ket_qua"],
        "id":        "@ledat09878",
        "server_time":  now,
        "update_count": st_copy["Tong_phien"] + 1,
        "Du_doan": {
            "Phien_tiep":    next_phien,
            "Du_doan":       du_doan,
            "Do_tin_cay":    do_tin_cay,
            "Chien_luoc":    chien_luoc,
            "Chi_tiet_chien_luoc": chi_tiet
        },
        "Thong_ke": {
            "Tong_phien":          st_copy["Tong_phien"],
            "Du_doan_dung":        st_copy["Du_doan_dung"],
            "Du_doan_sai":         st_copy["Du_doan_sai"],
            "Ti_le_dung":          st_copy["Ti_le_dung"],
            "Chuoi_dung_hien_tai": st_copy["Chuoi_dung_hien_tai"],
            "Chuoi_dung_cao_nhat": st_copy["Chuoi_dung_cao_nhat"],
            "Tai_count":           st_copy["Tai_count"],
            "Xiu_count":           st_copy["Xiu_count"]
        }
    }
 
    with lock_tx:
        latest_result_tx.clear()
        latest_result_tx.update(full_result)
 
    logger.info(
        f"[TX] Phiên {result['Phien']} | {result['Ket_qua']} (Tổng: {result['Tong']}) "
        f"| Dự đoán phiên {next_phien}: {du_doan} ({do_tin_cay}%)"
    )
 
 
# ──────────────────────────────────────────────────────────────────────────────
# HELPER KẾT QUẢ TÀI XỈU
# ──────────────────────────────────────────────────────────────────────────────
 
def get_tai_xiu(d1, d2, d3):
    total = d1 + d2 + d3
    return "Xỉu" if total <= 10 else "Tài"
 
 
# ──────────────────────────────────────────────────────────────────────────────
# POLLING API
# ──────────────────────────────────────────────────────────────────────────────
 
def poll_api():
    """
    Liên tục poll API nguồn để lấy kết quả TX thời gian thực.
    Sử dụng cmd 1008 để lấy SID phiên, cmd 1003 để lấy kết quả xúc xắc.
    """
    global last_sid_tx, sid_for_tx
 
    url = "https://jakpotgwab.geightdors.net/glms/v1/notify/taixiu?platform_id=g8&gid=vgmn_100"
 
    while True:
        try:
            req = Request(url, headers={'User-Agent': 'TaixiuAPI-Predictor/2.0'})
            with urlopen(req, timeout=10) as resp:
                data = json.loads(resp.read().decode('utf-8'))
 
            if data.get('status') == 'OK' and isinstance(data.get('data'), list):
                games = data['data']
 
                # Lấy SID từ cmd 1008
                for game in games:
                    if game.get("cmd") == 1008:
                        sid_for_tx = game.get("sid")
 
                # Xử lý kết quả từ cmd 1003
                for game in games:
                    if game.get("cmd") == 1003:
                        d1 = game.get("d1")
                        d2 = game.get("d2")
                        d3 = game.get("d3")
                        sid = sid_for_tx
 
                        if sid and sid != last_sid_tx and None not in (d1, d2, d3):
                            last_sid_tx = sid
                            total   = d1 + d2 + d3
                            ket_qua = get_tai_xiu(d1, d2, d3)
 
                            result = {
                                "Phien":     sid,
                                "Xuc_xac_1": d1,
                                "Xuc_xac_2": d2,
                                "Xuc_xac_3": d3,
                                "Tong":      total,
                                "Ket_qua":   ket_qua
                            }
 
                            update_result(result)
                            sid_for_tx = None
 
            else:
                logger.warning(f"API trả về dữ liệu không hợp lệ: {data.get('status')}")
 
        except Exception as e:
            logger.error(f"Lỗi polling: {e}")
            time.sleep(RETRY_DELAY)
 
        time.sleep(POLL_INTERVAL)
 
 
# ──────────────────────────────────────────────────────────────────────────────
# FLASK APP & ROUTES
# ──────────────────────────────────────────────────────────────────────────────
 
app = Flask(__name__)
 
 
@app.route("/")
def index():
    """Trang chủ – trả về kết quả TX mới nhất kèm dự đoán."""
    with lock_tx:
        return jsonify(latest_result_tx)
 
 
@app.route("/api/taixiu", methods=["GET"])
def get_taixiu():
    """
    Kết quả TX mới nhất kèm dự đoán phiên tiếp theo và thống kê.
    Response JSON:
        Phien, Xuc_xac_1/2/3, Tong, Ket_qua,
        Du_doan { Phien_tiep, Du_doan, Do_tin_cay, Chien_luoc, Chi_tiet_chien_luoc },
        Thong_ke { Tong_phien, Du_doan_dung, Du_doan_sai, Ti_le_dung, ... }
    """
    with lock_tx:
        return jsonify(latest_result_tx)
 
 
@app.route("/api/history", methods=["GET"])
def get_history():
    """
    Lịch sử 50 phiên gần nhất.
    Query param: ?limit=N để giới hạn số phiên (mặc định 50).
    """
    limit = flask_request.args.get("limit", MAX_HISTORY, type=int)
    limit = max(1, min(limit, MAX_HISTORY))
 
    with lock_tx:
        hist = history_tx[:limit]
 
    return jsonify({
        "total":   len(hist),
        "limit":   limit,
        "history": hist
    })
 
 
@app.route("/api/stats", methods=["GET"])
def get_stats():
    """Thống kê chi tiết tỷ lệ dự đoán đúng/sai theo thời gian."""
    with lock_tx:
        st = dict(stats_tx)
        hist = list(history_tx)
 
    # Tính tỷ lệ Tài/Xỉu từ lịch sử
    tai_list  = [h for h in hist if h.get("Ket_qua") == "Tài"]
    xiu_list  = [h for h in hist if h.get("Ket_qua") == "Xỉu"]
    total_hist = len(hist)
 
    # Phân tích xu hướng gần nhất (10 phiên)
    recent = hist[:10]
    recent_tai = sum(1 for h in recent if h.get("Ket_qua") == "Tài")
    recent_xiu = len(recent) - recent_tai
 
    # Phát hiện chuỗi hiện tại
    current_streak = 0
    current_streak_type = None
    if hist:
        current_streak_type = hist[0].get("Ket_qua")
        for h in hist:
            if h.get("Ket_qua") == current_streak_type:
                current_streak += 1
            else:
                break
 
    return jsonify({
        "Thong_ke_tong": {
            "Tong_phien_da_theo_doi": total_hist,
            "Du_doan_dung":           st["Du_doan_dung"],
            "Du_doan_sai":            st["Du_doan_sai"],
            "Ti_le_dung":             st["Ti_le_dung"],
            "Chuoi_dung_hien_tai":    st["Chuoi_dung_hien_tai"],
            "Chuoi_dung_cao_nhat":    st["Chuoi_dung_cao_nhat"]
        },
        "Phan_bo_ket_qua": {
            "Tai":         len(tai_list),
            "Xiu":         len(xiu_list),
            "Ti_le_Tai":   round(len(tai_list) / total_hist * 100, 1) if total_hist else 0,
            "Ti_le_Xiu":   round(len(xiu_list) / total_hist * 100, 1) if total_hist else 0
        },
        "Xu_huong_10_phien_gan_nhat": {
            "Tai":  recent_tai,
            "Xiu":  recent_xiu
        },
        "Chuoi_hien_tai": {
            "Loai":   current_streak_type,
            "Do_dai": current_streak
        },
        "Du_doan_dang_cho": {
            "Phien":   pending_prediction.get("Phien_du_doan"),
            "Du_doan": pending_prediction.get("Du_doan")
        }
    })
 
 
@app.route("/api/predict", methods=["GET"])
def get_predict():
    """
    Trả về chỉ thông tin dự đoán phiên tiếp theo.
    Tiện lợi cho client chỉ cần kết quả dự đoán.
    """
    with lock_tx:
        result = latest_result_tx.get("Du_doan", {})
        phien_hien_tai = latest_result_tx.get("Phien", 0)
 
    return jsonify({
        "Phien_hien_tai": phien_hien_tai,
        "Du_doan":        result
    })
 
 
@app.route("/api/analysis", methods=["GET"])
def get_analysis():
    """
    Phân tích chi tiết từng chiến lược dự đoán.
    """
    with lock_tx:
        hist = list(history_tx)
 
    if len(hist) < MIN_DATA_POINTS:
        return jsonify({"error": "Chưa đủ dữ liệu để phân tích"}), 400
 
    # Chạy từng chiến lược riêng lẻ
    analysis = {}
 
    try:
        pred, conf = engine.strategy_markov(hist)
        analysis["Markov"] = {"Du_doan": pred, "Do_tin_cay": round(conf * 100, 1)}
    except Exception as e:
        analysis["Markov"] = {"error": str(e)}
 
    try:
        pred, conf = engine.strategy_pattern(hist)
        analysis["Pattern"] = {"Du_doan": pred, "Do_tin_cay": round(conf * 100, 1)}
    except Exception as e:
        analysis["Pattern"] = {"error": str(e)}
 
    try:
        pred, conf = engine.strategy_frequency(hist)
        analysis["Frequency"] = {"Du_doan": pred, "Do_tin_cay": round(conf * 100, 1)}
    except Exception as e:
        analysis["Frequency"] = {"error": str(e)}
 
    try:
        pred, conf = engine.strategy_streak(hist)
        analysis["Streak"] = {"Du_doan": pred, "Do_tin_cay": round(conf * 100, 1)}
    except Exception as e:
        analysis["Streak"] = {"error": str(e)}
 
    try:
        pred, conf = engine.strategy_sum_analysis(hist)
        analysis["SumAnalysis"] = {"Du_doan": pred, "Do_tin_cay": round(conf * 100, 1)}
    except Exception as e:
        analysis["SumAnalysis"] = {"error": str(e)}
 
    # Tổng hợp
    final_pred, final_conf, chien_luoc, _ = engine.predict(hist)
 
    return jsonify({
        "Phan_tich_tung_chien_luoc": analysis,
        "Ket_qua_tong_hop": {
            "Du_doan":    final_pred,
            "Do_tin_cay": final_conf,
            "Chien_luoc_chinh": chien_luoc
        },
        "So_phien_da_co": len(hist)
    })
 
 
@app.route("/api/health", methods=["GET"])
def health_check():
    """Health check endpoint."""
    with lock_tx:
        last_update = latest_result_tx.get("server_time", "")
        phien = latest_result_tx.get("Phien", 0)
 
    return jsonify({
        "status": "OK",
        "last_phien": phien,
        "last_update": last_update,
        "history_count": len(history_tx),
        "timestamp": datetime.now(timezone.utc).isoformat(timespec="milliseconds").replace("+00:00", "Z")
    })
 
 
# ──────────────────────────────────────────────────────────────────────────────
# ERROR HANDLERS
# ──────────────────────────────────────────────────────────────────────────────
 
@app.errorhandler(404)
def not_found(e):
    return jsonify({
        "error": "Endpoint không tồn tại",
        "available_endpoints": [
            "GET /",
            "GET /api/taixiu",
            "GET /api/history?limit=N",
            "GET /api/stats",
            "GET /api/predict",
            "GET /api/analysis",
            "GET /api/health"
        ]
    }), 404
 
 
@app.errorhandler(500)
def server_error(e):
    logger.error(f"Server error: {e}")
    return jsonify({"error": "Lỗi server nội bộ"}), 500
 
 
# ──────────────────────────────────────────────────────────────────────────────
# KHỞI ĐỘNG
# ──────────────────────────────────────────────────────────────────────────────
 
if __name__ == "__main__":
    logger.info("=" * 60)
    logger.info("  HỆ THỐNG API TÀI XỈU v2.0 - @ledat09878")
    logger.info("  Thuật toán: Markov + Pattern + Frequency + Streak + Sum")
    logger.info("=" * 60)
 
    # Khởi động thread polling
    thread_tx = threading.Thread(
        target=poll_api,
        name="PollThread-TX",
        daemon=True
    )
    thread_tx.start()
    logger.info("[OK] Thread polling TX đã khởi động.")
 
    # Lấy port từ env
    port = int(os.environ.get("PORT", 8000))
    logger.info(f"[OK] Server khởi động tại http://{HOST}:{port}")
    logger.info("[OK] Endpoints:")
    logger.info("       GET /api/taixiu    – Kết quả + dự đoán + thống kê")
    logger.info("       GET /api/history   – Lịch sử 50 phiên")
    logger.info("       GET /api/stats     – Thống kê chi tiết")
    logger.info("       GET /api/predict   – Chỉ thông tin dự đoán")
    logger.info("       GET /api/analysis  – Phân tích từng chiến lược")
    logger.info("       GET /api/health    – Kiểm tra sức khoẻ server")
 
    app.run(host=HOST, port=port)
