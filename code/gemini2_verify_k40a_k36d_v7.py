"""
PR #257（定理 K40a・系 K39）および PR #259（定理 K36d″ v=7）の完全記号的・数値的独立検証スクリプト。

- 定理 K40a（q = 23、N = 22r >= 22）：
  23a + 1 = 2^N から決まる a mod 2^22 のみを用いた厳密記号計算により、
  6 本の鎖すべての入口・幾何部・終わり・不等式 (0 < d <= m, d != h-1)・段数・E 型評価回路が
  すべての N = 22r (r >= 1) で成り立つことを記号的に証明確認し、
  さらに N = 22..880（40 例）の BigInt 実数値検証を行う。

- 定理 K36d″（v = 7、q = 125、N = 50r >= 50）：
  125a + 1 = 4^N = 2^{2N} から決まる a mod 2^{100} のみを用いた厳密記号 E1/E2 評価器により、
  E1(h), E2(h), E2(Y) の評価木全体と 12 本の鎖すべての入口・幾何部・終わり・
  不等式 (0 < d <= m, d != h-1)・段数 c0・終了距離 v2（または Y）が
  すべての N = 50r (r >= 1) で N に依らず同一であることを記号的に証明確認し、
  さらに N = 50, 100, 150, 200, 250, 300 の BigInt 実数値検証を行う。

実行方法:
    python code/gemini2_verify_k40a_k36d_v7.py
出力:
    data/gemini2_verify_k40a_k36d_v7.txt
"""

from __future__ import annotations

import time
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path


def v2(x: int) -> int:
    assert x > 0
    return (x & -x).bit_length() - 1


@dataclass(frozen=True)
class LinForm:
    """(alpha * a + beta) / 2^k を表す厳密線形形式。"""
    alpha: int
    beta: int
    k: int

    def normalized(self) -> LinForm:
        al, be, kk = self.alpha, self.beta, self.k
        while kk > 0 and (al & 1) == 0 and (be & 1) == 0:
            al >>= 1
            be >>= 1
            kk -= 1
        return LinForm(al, be, kk)

    def eval_mod(self, a_mod: int, mod_bits: int) -> tuple[int, int]:
        """a = a_mod (mod 2^mod_bits) のもとで整数性・下位ビットを厳密評価する。
        返り値: (val_mod, known_bits)
        """
        assert self.k < mod_bits, f"need more bits: k={self.k}, mod_bits={mod_bits}"
        num = (self.alpha * a_mod + self.beta) & ((1 << mod_bits) - 1)
        assert (num & ((1 << self.k) - 1)) == 0, f"not divisible by 2^{self.k}: {self}"
        return num >> self.k, mod_bits - self.k

    def parity(self, a_mod: int, mod_bits: int) -> int:
        val, bits = self.eval_mod(a_mod, mod_bits)
        assert bits >= 1
        return val & 1

    def v2_exact(self, a_mod: int, mod_bits: int, max_v: int = 12) -> int:
        val, bits = self.eval_mod(a_mod, mod_bits)
        assert bits > max_v
        if (val & ((1 << max_v) - 1)) == 0:
            raise AssertionError(f"v2 >= {max_v} for {self}")
        return (val & -val).bit_length() - 1

    def div2(self) -> LinForm:
        return LinForm(self.alpha, self.beta, self.k + 1).normalized()

    def o_step_odd(self) -> LinForm:
        # (M + d)/2 = (3a + (alpha*a + beta)/2^k)/2 = ((3*2^k + alpha)*a + beta)/2^{k+1}
        return LinForm(3 * (1 << self.k) + self.alpha, self.beta, self.k + 1).normalized()

    def add_h_half(self) -> LinForm:
        # h + d/2 = (3a - 1)/2 + (alpha*a + beta)/2^{k+1}
        return LinForm(3 * (1 << self.k) + self.alpha, -(1 << self.k) + self.beta, self.k + 1).normalized()

    def check_bounds(self, a_min: int) -> None:
        """すべての a >= a_min で 0 < d <= 3a - 2 を厳密に確認する。"""
        # d > 0: alpha*a + beta > 0 (alpha > 0 かつ alpha*a_min + beta > 0)
        assert self.alpha > 0 and self.alpha * a_min + self.beta > 0, f"d <= 0 possible: {self}"
        # d <= 3a - 2: (3*2^k - alpha)*a >= 2*2^k + beta
        lhs_coeff = 3 * (1 << self.k) - self.alpha
        rhs_const = 2 * (1 << self.k) + self.beta
        assert lhs_coeff > 0 and lhs_coeff * a_min >= rhs_const, f"d > m possible: {self}"

    def check_neq_h_minus_1(self, a_min: int) -> None:
        """すべての a >= a_min で d != (3a - 3)/2 を厳密確認する。"""
        # 2*d - (3a - 3) = ((2*alpha - 3*2^k)*a + (2*beta + 3*2^k)) / 2^k
        c_a = 2 * self.alpha - 3 * (1 << self.k)
        c_b = 2 * self.beta + 3 * (1 << self.k)
        if c_a == 0:
            assert c_b != 0, f"d == h-1 identically: {self}"
        elif c_a > 0:
            assert c_a * a_min + c_b > 0, f"d == h-1 possible: {self}"
        else:
            assert c_a * a_min + c_b < 0, f"d == h-1 possible: {self}"


def trace_symbolic_chain(
    name: str,
    d0: LinForm,
    q: int,
    a_mod: int,
    mod_bits: int,
    a_min: int,
    t_exp_of_N: tuple[int, int],
    start_block_of_K: tuple[int, int],
    K_of_N_offset: int,
    N_min: int,
) -> dict:
    """1 本の O 型一本道の鎖を『入口 → 幾何部 → 終わり』で完全記号検証する。
    t_exp_of_N: 2^{c_N * N - k} の係数 c_N（K40a では 1, K36d では 2）と最小シフト
    start_block_of_K: 開始ブロック j0 = sK * K + s0（K40a では K=P=N/2, K36d では K=N-4）
    """
    c_N = t_exp_of_N[0]
    sK, s0 = start_block_of_K
    cur = d0.normalized()
    entry_steps = 0
    block_drop = 0
    max_k_used = cur.k
    geo_kind: str | None = None
    geo_c = 0
    geo_k = 0

    for _ in range(30):
        cur.check_bounds(a_min)
        max_k_used = max(max_k_used, cur.k)
        # 幾何形チェック: 2a - c*2^{c_N*N - k}  <=>  2*2^k - alpha = q*c, beta = -c (c > 0 odd)
        c2 = 2 * (1 << cur.k) - cur.alpha
        if c2 > 0 and c2 % q == 0:
            c = c2 // q
            if (c & 1) == 1 and cur.beta == -c:
                geo_kind = "A"
                geo_c = c
                geo_k = cur.k
                break
        # M - c*2^{c_N*N - k}  <=>  3*2^k - alpha = q*c, beta = -c (c > 0 odd)
        c3 = 3 * (1 << cur.k) - cur.alpha
        if c3 > 0 and c3 % q == 0:
            c = c3 // q
            if (c & 1) == 1 and cur.beta == -c:
                geo_kind = "B"
                geo_c = c
                geo_k = cur.k
                break
        par = cur.parity(a_mod, mod_bits)
        if par == 0:
            cur = cur.div2()
        else:
            cur.check_neq_h_minus_1(a_min)
            cur = cur.o_step_odd()
            block_drop += 1
        entry_steps += 1

    assert geo_kind is not None, f"{name}: geometric form not reached"

    # 幾何部開始時のブロック番号 j_geo = sK * K + (s0 - block_drop)
    # 開始指数 t_geo = c_N * N - geo_k
    # N = (K + K_of_N_offset) * (2 if c_N == 1 else 1)  ... K40a: K=P, N=2P; K36d: K=N-4, N=K+4
    # 幾何部の境界条件チェック:
    if geo_kind == "A":
        # 2a - c*2^t: 1 ブロック 2 段、t は 2 減る。
        # a - c*2^{t-1} > 0 が入口で成り立てば全域で正: q*c < 2^{geo_k + 1}
        assert q * geo_c < (1 << (geo_k + 1)), f"{name}: (A) positivity fails"
        # 2a - c*2^t で t = 2*j_geo + t_rem になるか（t が 1 まで落ちるブロック j_tail）
        # K40a (c_N=1, N=2K): t_geo = 2K - geo_k, j_geo = K + (s0 - block_drop)
        #   => 2*j_geo - t_geo = 2*(s0 - block_drop) + geo_k （定数!）
        # K36d (c_N=2, N=K+4): t_geo = 2K + 8 - geo_k, j_geo = K + (s0 - block_drop)
        #   => 2*j_geo - t_geo = 2*(s0 - block_drop) - 8 + geo_k （定数!）
        const_t = 0 if c_N == 1 else 2 * K_of_N_offset
        # 1 ブロック進むごとに j は 1 減り t は 2 減る => 2*j - t は不変量!
        inv = 2 * (s0 - block_drop) - (const_t - geo_k)
        # t_tail >= 0 (1 または 2) で止まるように j_tail を選ぶ
        # j_geo - n_geo = j_tail, t_geo - 2*n_geo = t_tail >= 1
        # ケース 1: ブロック 0 に到達する前に t <= 2 になる (inv >= 1)
        # ケース 2: t > 0 のままブロック 0 に到達 (inv <= 0)
        if inv >= 1:
            # t_tail = 1 (inv 奇数) または 2 (inv 偶数) まで進む => j_tail = (inv + t_tail) // 2
            t_tail = 1 if (inv & 1) == 1 else 2
            j_tail = (inv + t_tail) // 2
            # n_geo = j_geo - j_tail = K + (s0 - block_drop - j_tail)
            # N = N_min で n_geo >= 0 を確認
            K_min = (N_min // 2) if c_N == 1 else (N_min - K_of_N_offset)
            n_geo_min = K_min + (s0 - block_drop - j_tail)
            assert n_geo_min >= 0, f"{name}: n_geo_min < 0"
            # 幾何部終了時: ブロック j_tail で 2a - geo_c * 2^{t_tail}
            tail_cur = LinForm(2, -geo_c * (1 << t_tail), 0)
            tail_steps = 0
            rem_j = j_tail
            while rem_j > 0:
                tail_cur.check_bounds(a_min)
                max_k_used = max(max_k_used, tail_cur.k)
                if tail_cur.parity(a_mod, mod_bits) == 0:
                    tail_cur = tail_cur.div2()
                else:
                    tail_cur.check_neq_h_minus_1(a_min)
                    tail_cur = tail_cur.o_step_odd()
                    rem_j -= 1
                tail_steps += 1
            tail_cur.check_bounds(a_min)
            max_k_used = max(max_k_used, tail_cur.k)
            # 全体段数: entry_steps + 2*n_geo + tail_steps = 2K + c0
            c0 = entry_steps + 2 * (s0 - block_drop - j_tail) + tail_steps
            end_v2 = tail_cur.v2_exact(a_mod, mod_bits, max_v=15)
            return {
                "name": name,
                "geo": f"2a - {geo_c}*2^({c_N}N-{geo_k})",
                "entry_steps": entry_steps,
                "step_formula": (2, c0),
                "end_form": tail_cur,
                "end_v2": end_v2,
                "max_k_used": max_k_used,
            }
        else:
            # ブロック 0 で 2a - geo_c * 2^{-inv} に到達（定数!）
            t_end = -inv
            assert t_end >= 0
            end_form = LinForm(2, -geo_c * (1 << t_end), 0)
            end_form.check_bounds(a_min)
            c0 = entry_steps + 2 * (s0 - block_drop)
            end_v2 = end_form.v2_exact(a_mod, mod_bits, max_v=15)
            return {
                "name": name,
                "geo": f"2a - {geo_c}*2^({c_N}N-{geo_k})",
                "entry_steps": entry_steps,
                "step_formula": (2, c0),
                "end_form": end_form,
                "end_v2": end_v2,
                "max_k_used": max_k_used,
            }
    else:
        # geo_kind == "B": M - c*2^t: 1 ブロック 1 段、t は 1 減る
        assert q * geo_c < 3 * (1 << geo_k), f"{name}: (B) positivity fails"
        assert geo_c >= 3, f"{name}: (B) c >= 3 needed for <= m"
        # M - c*2^t = (3a - 3)/2 <=> 3*2^{c_N*N} + 3*(q - 1) = q*c*2^{t+1}
        # v2(3*(q-1)) を計算して、最小 t_end + 1 > v2(3*(q-1)) なら全段で h-1 と一致不可!
        v2_h_obst = v2(3 * (q - 1))
        const_t = 0 if c_N == 1 else 2 * K_of_N_offset
        # ブロック 0 での t_end = (2K + const_t - geo_k) - (K + s0 - block_drop) = K + (const_t - geo_k - s0 + block_drop)
        t_end_offset = const_t - geo_k - s0 + block_drop
        K_min = (N_min // 2) if c_N == 1 else (N_min - K_of_N_offset)
        t_end_min = K_min + t_end_offset
        assert t_end_min >= 1, f"{name}: (B) t_end_min={t_end_min} < 1"
        assert t_end_min + 1 > v2_h_obst, f"{name}: (B) h-1 check needs t >= {v2_h_obst}"
        c0 = entry_steps + (s0 - block_drop)
        # 終わりは M - geo_c * 2^{t_end}（奇数、v2 = 0）
        return {
            "name": name,
            "geo": f"M - {geo_c}*2^({c_N}N-{geo_k})",
            "entry_steps": entry_steps,
            "step_formula": (1, c0),
            "end_form": f"M - {geo_c}*2^(K+{t_end_offset})",
            "end_v2": 0,
            "max_k_used": max_k_used,
            "t_end_min": t_end_min,
        }


def verify_pr257_k40a() -> list[str]:
    """PR #257（定理 K40a・系 K39）の完全記号検証 + N=22..880（40 例）実数値検証。"""
    q = 23
    mod_bits = 22
    a_mod = (-pow(q, -1, 1 << mod_bits)) & ((1 << mod_bits) - 1)
    assert a_mod % 4096 == 2137
    a_min = ((1 << 22) - 1) // 23

    # 記号検証：d1, X の付値
    d1 = LinForm(9, -1, 2)
    X = LinForm(13, -5, 3)
    assert d1.v2_exact(a_mod, mod_bits) == 3
    assert X.v2_exact(a_mod, mod_bits) == 4
    # E ブロックからの 5 本の鎖（ブロック P-1 から出発）
    chains_spec = [
        ("g=(21a-5)/8", LinForm(21, -5, 3), (2, 0), X, 4),
        ("f=(33a-9)/16", LinForm(33, -9, 4), (1, 0), "M - 9*2^(K+-4)", 0),
        ("h+X/8=(109a-37)/64", LinForm(109, -37, 6), (1, 0), "M - 37*2^(K+-6)", 0),
        ("h+X/4=(61a-21)/32", LinForm(61, -21, 5), (2, 0), LinForm(61, -21, 5), 0),
        ("h+X/2=(37a-13)/16", LinForm(37, -13, 4), (1, 1), "M - 13*2^(K+-5)", 0),
    ]
    # まず E ブロックの問い合せ h + d/2 の一致と <= m を記号確認
    assert d1.add_h_half() == LinForm(21, -5, 3)
    assert d1.div2().add_h_half() == LinForm(33, -9, 4)
    assert X.div2().div2().add_h_half() == LinForm(109, -37, 6)
    assert X.div2().add_h_half() == LinForm(61, -21, 5)
    assert X.add_h_half() == LinForm(37, -13, 4)

    max_k = 0
    for name, d0, exp_sf, exp_end, exp_v2 in chains_spec:
        res = trace_symbolic_chain(
            name=name,
            d0=d0,
            q=23,
            a_mod=a_mod,
            mod_bits=mod_bits,
            a_min=a_min,
            t_exp_of_N=(1, 0),
            start_block_of_K=(1, -1),
            K_of_N_offset=0,
            N_min=22,
        )
        assert res["step_formula"] == exp_sf, f"{name}: got {res['step_formula']}, want {exp_sf}"
        assert res["end_form"] == exp_end, f"{name}: got {res['end_form']}, want {exp_end}"
        assert res["end_v2"] == exp_v2, f"{name}: got v2={res['end_v2']}, want {exp_v2}"
        max_k = max(max_k, res["max_k_used"])
    assert max_k + 1 <= mod_bits

    # h の鎖の記号確認: h=(3a-1)/2 -> d1=(9a-1)/4 -> d1/2 -> d1/4 = 2a - 2^{N-4}
    h_form = LinForm(3, -1, 1)
    h_form.check_bounds(a_min)
    h_form.check_neq_h_minus_1(a_min)
    assert h_form.parity(a_mod, mod_bits) == 1
    step1 = h_form.o_step_odd()
    assert step1 == d1
    step1.check_bounds(a_min)
    assert step1.parity(a_mod, mod_bits) == 0
    step2 = step1.div2()
    step2.check_bounds(a_min)
    assert step2.parity(a_mod, mod_bits) == 0
    step3 = step2.div2()
    step3.check_bounds(a_min)
    # 2*2^4 - 9 = 23 = 1*23, beta = -1 => 2a - 2^{N-4}
    assert step3 == LinForm(9, -1, 4)
    assert 2 * 16 - 9 == 23 and step3.beta == -1

    # E ブロック評価の論理確認（P 奇数・P 偶数）
    for P_parity in (0, 1):  # 0: P even, 1: P odd
        # B 仮定: d1=False, X=(P_parity==0 -> True)
        f_in_Pm1 = (P_parity == 0)  # steps=P, ends odd(True) -> True iff P even
        d1_4_in_E = False  # v2=1
        d1_2_in_E = (not d1_4_in_E) and (not f_in_Pm1)
        if P_parity == 1:
            assert d1_2_in_E is True
            d1_in_E = False  # not d1_2_in_E
            assert d1_in_E is False
        else:
            assert d1_2_in_E is False
            g_in_Pm1 = True  # steps=N (even), ends X (True)
            d1_in_E = (not d1_2_in_E) and (not g_in_Pm1)
            assert d1_in_E is False
            # X in S_E
            x8_in_E = False  # v2=1
            hx8_in_Pm1 = True  # steps=P (even), ends odd(True)
            x4_in_E = (not x8_in_E) and (not hx8_in_Pm1)
            assert x4_in_E is False
            hx4_in_Pm1 = True  # steps=N (even), ends odd(True)
            x2_in_E = (not x4_in_E) and (not hx4_in_Pm1)
            assert x2_in_E is False
            hx2_in_Pm1 = False  # steps=P+1 (odd), ends odd(True)
            x_in_E = (not x2_in_E) and (not hx2_in_Pm1)
            assert x_in_E is True

    # 実数値検証: N = 22, 44, ..., 880（40 例）
    num_ok = 0
    for N in range(22, 881, 22):
        assert ((1 << N) - 1) % 23 == 0
        a = ((1 << N) - 1) // 23
        m = 3 * a - 2
        M = 3 * a
        h = (3 * a - 1) // 2
        P = N // 2
        d1_v = (9 * a - 1) // 4
        X_v = (13 * a - 5) // 8
        assert a % 4096 == 2137 and m % 32 == 9
        assert v2(d1_v) == 3 and v2(X_v) == 4

        def walk_num(j: int, d: int) -> tuple[int, int]:
            s = 0
            while j > 0:
                assert 0 < d <= m and d != h - 1
                if (d & 1) == 0:
                    d >>= 1
                else:
                    e = (M + d) >> 1
                    assert e <= m
                    d = e
                    j -= 1
                s += 1
            assert 0 < d <= m
            return d, s

        for n in range(1, P):
            d_end, s = walk_num(n, h)
            if n == 1:
                assert s == 1 and d_end == d1_v
            else:
                assert s == 2 * n + 1 and d_end == 2 * a - (1 << (N - 2 * n - 2))

        assert walk_num(P - 1, (21 * a - 5) // 8) == (X_v, N)
        assert walk_num(P - 1, (33 * a - 9) // 16) == (M - 9 * (1 << (P - 4)), P)
        assert walk_num(P - 1, (109 * a - 37) // 64) == (M - 37 * (1 << (P - 6)), P)
        assert walk_num(P - 1, (61 * a - 21) // 32) == ((61 * a - 21) // 32, N)
        assert walk_num(P - 1, (37 * a - 13) // 16) == (M - 13 * (1 << (P - 5)), P + 1)
        num_ok += 1

    return [
        f"PR #257 Theorem K40a & Cor K39: SYMBOLIC PROOF VERIFIED for all N = 22r >= 22 (max_k_used={max_k}, need <= 22 bits), errors=0",
        f"PR #257 BigInt cross-check (N=22..880, 40 cases, up to {len(str(3*((1<<880)-1)//23-2))}-digit m): {num_ok}/40 exact match, errors=0",
    ]


def verify_pr259_k36d_v7() -> list[str]:
    """PR #259（定理 K36d″ v=7）の完全記号 E1/E2 評価・12 鎖証明 + N=50..300 実数値検証。"""
    q = 125
    mod_bits = 100  # N >= 50 => 2N >= 100
    a_mod = (-pow(q, -1, 1 << mod_bits)) & ((1 << mod_bits) - 1)
    a_min = ((1 << 100) - 1) // 125

    h_form = LinForm(3, -1, 1)
    Y_form = LinForm(2, -22, 0)
    assert h_form.v2_exact(a_mod, mod_bits) == 6  # v - 1 = 6
    assert Y_form.v2_exact(a_mod, mod_bits) == 6  # v2(Y) = 6 (even -> in S_0)

    # 記号 E1/E2 評価器（K = N - 4 は常に偶数）
    memo_E: dict[tuple[int, LinForm], bool] = {}
    chains_traced: list[dict] = []
    max_k_E = 0

    def sym_val_O(d0: LinForm) -> bool:
        res = trace_symbolic_chain(
            name=f"({d0.alpha}a{d0.beta:+d})/2^{d0.k}",
            d0=d0,
            q=125,
            a_mod=a_mod,
            mod_bits=mod_bits,
            a_min=a_min,
            t_exp_of_N=(2, 0),
            start_block_of_K=(1, 1),  # ブロック K+1 から出発
            K_of_N_offset=4,          # N = K + 4
            N_min=50,
        )
        chains_traced.append(res)
        # B での値判定: v2 <= 3 は v2 偶奇、または Y_form なら True
        if res["end_v2"] <= 3:
            base_val = (res["end_v2"] % 2) == 0
        else:
            assert res["end_form"] == Y_form, f"unknown end form: {res}"
            base_val = True
        # K は偶数なので、段数 (coeff*K + c0) の偶奇は c0 の偶奇に一致！
        _, c0 = res["step_formula"]
        return base_val if (c0 % 2 == 0) else (not base_val)

    def sym_val_E(k_blk: int, d: LinForm) -> bool:
        nonlocal max_k_E
        d = d.normalized()
        key = (k_blk, d)
        if key in memo_E:
            return memo_E[key]
        d.check_bounds(a_min)
        max_k_E = max(max_k_E, d.k)
        if d.parity(a_mod, mod_bits) == 1:
            memo_E[key] = True
            return True
        a1 = sym_val_E(k_blk, d.div2())
        if a1:
            memo_E[key] = False
            return False
        e = d.add_h_half()
        # e <= m かどうかを記号判定（常に a >= a_min で符号一定であることを確認）
        lhs_c = 3 * (1 << e.k) - e.alpha
        rhs_c = 2 * (1 << e.k) + e.beta
        if lhs_c > 0 and lhs_c * a_min >= rhs_c:
            b = sym_val_O(e) if k_blk == 1 else sym_val_E(1, e)
        else:
            # 逆に e > m が全 a >= a_min で確定していることを確認
            assert lhs_c < 0 and lhs_c * a_min < rhs_c, f"ambiguous e <= m: {e}"
            b = False
        r = not b
        memo_E[key] = r
        return r

    h1 = sym_val_E(1, h_form)
    h2 = sym_val_E(2, h_form)
    y2 = sym_val_E(2, Y_form)
    assert h1 is False and h2 is True and y2 is True
    assert len(chains_traced) == 12
    max_k_all = max([max_k_E] + [c["max_k_used"] for c in chains_traced])
    assert max_k_all + 1 <= mod_bits

    # BigInt 実数値検証: N = 50, 100, 150, 200, 250, 300（6 例）
    num_ok = 0
    for N in (50, 100, 150, 200, 250, 300):
        assert ((1 << (2 * N)) - 1) % 125 == 0
        a = ((1 << (2 * N)) - 1) // 125
        m = 3 * a - 2
        M = 3 * a
        h = (3 * a - 1) // 2
        K = N - 4
        Y = 2 * a - 22
        assert v2(m + 1) == 7 and v2(Y) == 6 and K % 2 == 0

        memo_n: dict[tuple[int, int], bool] = {}
        chain_cnt = 0

        def valO_n(j: int, d: int) -> bool:
            nonlocal chain_cnt
            chain_cnt += 1
            s = 0
            while j > 0:
                assert 0 < d <= m and d != h - 1
                if (d & 1) == 0:
                    d >>= 1
                else:
                    e = (M + d) >> 1
                    assert e <= m
                    d = e
                    j -= 1
                s += 1
            t = v2(d)
            if t <= 3:
                bv = (t % 2) == 0
            else:
                assert d == Y
                bv = True
            return bv if (s % 2 == 0) else (not bv)

        def valE_n(kb: int, d: int) -> bool:
            key = (kb, d)
            if key in memo_n:
                return memo_n[key]
            if (d & 1) == 1:
                memo_n[key] = True
                return True
            if valE_n(kb, d >> 1):
                memo_n[key] = False
                return False
            e = h + (d >> 1)
            b = False
            if e <= m:
                b = valO_n(K + 1, e) if kb == 1 else valE_n(1, e)
            memo_n[key] = not b
            return not b

        assert valE_n(1, h) is False
        assert valE_n(2, h) is True
        assert valE_n(2, Y) is True
        assert chain_cnt == 12
        num_ok += 1

    return [
        f"PR #259 Theorem K36d'' (v=7, q=125): SYMBOLIC PROOF VERIFIED for all N = 50r >= 50 (12 chains, E1(h)=False, E2(h)=True, E2(Y)=True, max_k_used={max_k_all} <= 99), errors=0",
        f"PR #259 BigInt cross-check (N=50,100,150,200,250,300, up to {len(str(3*((1<<600)-1)//125-2))}-digit m): {num_ok}/6 exact match (12 chains each), errors=0",
    ]


def main() -> None:
    t0 = time.perf_counter()
    lines = [
        "gemini-2 independent symbolic & numerical verification of PR #257 (Theorem K40a / Cor K39) and PR #259 (Theorem K36d'' v=7)",
    ]
    lines.extend(verify_pr257_k40a())
    lines.extend(verify_pr259_k36d_v7())
    lines.append(f"Total elapsed={time.perf_counter() - t0:.2f}s")
    out_text = "\n".join(lines) + "\n"
    Path("data/gemini2_verify_k40a_k36d_v7.txt").write_text(out_text, encoding="utf-8")
    print(out_text, end="")


if __name__ == "__main__":
    main()
