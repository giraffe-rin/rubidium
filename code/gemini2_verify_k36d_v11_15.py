"""
PR #261（定理 K36d″ の拡大：v = 11, 13, 15）の完全記号的・数値的独立検証スクリプト。

- ord_q(4)（q = 2^v - 3）を v = 7, 9, 11, 13, 15 で厳密計算して N の条件を確認。
- v = 11 (N = 102r >= 102), v = 13 (N = 387*(2r-1) >= 387), v = 15 (N = 234r >= 234) それぞれについて、
  qa + 1 = 4^N = 2^{2N} から決まる a mod 2^{2*N_min} のみを用いた独立の記号 E1/E2 評価器により、
  E1(h)=False, E2(h)=True, E2(Y)=True の評価木全体および全鎖（28本 / 38本 / 50本）の
  入口・幾何部 (A)/(B)・終わり・全不等式 (0 < d <= m, d != h-1)・段数 c0・終了距離 v2 (または Y) が
  すべての該当 N で完全に同一であることを記号的に証明確認し、厳密な必要桁数 max_k_used を確定する。
- さらに各 v で 3 個ずつの BigInt 実数値照合（計 9 例、最大 N = 1935 の 1,161 桁の m まで）を行う。

実行方法:
    python code/gemini2_verify_k36d_v11_15.py
出力:
    data/gemini2_verify_k36d_v11_15.txt
"""

from __future__ import annotations

import time
from dataclasses import dataclass
from pathlib import Path


def v2(x: int) -> int:
    assert x > 0
    return (x & -x).bit_length() - 1


def mult_order(base: int, mod: int) -> int:
    x = base % mod
    k = 1
    while x != 1:
        x = (x * base) % mod
        k += 1
    return k


@dataclass(frozen=True)
class LinForm:
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
        assert self.k < mod_bits, f"need more bits: k={self.k}, mod_bits={mod_bits}"
        num = (self.alpha * a_mod + self.beta) & ((1 << mod_bits) - 1)
        assert (num & ((1 << self.k) - 1)) == 0, f"not divisible by 2^{self.k}: {self}"
        return num >> self.k, mod_bits - self.k

    def parity(self, a_mod: int, mod_bits: int) -> int:
        val, bits = self.eval_mod(a_mod, mod_bits)
        assert bits >= 1
        return val & 1

    def v2_exact(self, a_mod: int, mod_bits: int, max_v: int = 16) -> int:
        val, bits = self.eval_mod(a_mod, mod_bits)
        assert bits > max_v
        if (val & ((1 << max_v) - 1)) == 0:
            raise AssertionError(f"v2 >= {max_v} for {self}")
        return (val & -val).bit_length() - 1

    def div2(self) -> LinForm:
        return LinForm(self.alpha, self.beta, self.k + 1).normalized()

    def o_step_odd(self) -> LinForm:
        return LinForm(3 * (1 << self.k) + self.alpha, self.beta, self.k + 1).normalized()

    def add_h_half(self) -> LinForm:
        return LinForm(3 * (1 << self.k) + self.alpha, -(1 << self.k) + self.beta, self.k + 1).normalized()

    def check_bounds(self, a_min: int) -> None:
        assert self.alpha > 0 and self.alpha * a_min + self.beta > 0, f"d <= 0 possible: {self}"
        lhs_coeff = 3 * (1 << self.k) - self.alpha
        rhs_const = 2 * (1 << self.k) + self.beta
        assert lhs_coeff > 0 and lhs_coeff * a_min >= rhs_const, f"d > m possible: {self}"

    def check_neq_h_minus_1(self, a_min: int) -> None:
        c_a = 2 * self.alpha - 3 * (1 << self.k)
        c_b = 2 * self.beta + 3 * (1 << self.k)
        if c_a == 0:
            assert c_b != 0, f"d == h-1 identically: {self}"
        elif c_a > 0:
            assert c_a * a_min + c_b > 0, f"d == h-1 possible: {self}"
        else:
            assert c_a * a_min + c_b < 0, f"d == h-1 possible: {self}"


def trace_k36d_chain(
    d0: LinForm,
    v: int,
    q: int,
    a_mod: int,
    mod_bits: int,
    a_min: int,
    N_min: int,
) -> dict:
    """K36d (q = 2^v - 3, qa + 1 = 4^N = 2^{2N}, K = N - (v+1)/2) の O 型一本道鎖の完全記号検証。"""
    K_off = (v + 1) // 2  # N = K + K_off
    K_min = N_min - K_off
    cur = d0.normalized()
    entry_steps = 0
    block_drop = 0
    max_k_used = cur.k
    geo_kind: str | None = None
    geo_c = 0
    geo_k = 0

    for _ in range(40):
        cur.check_bounds(a_min)
        max_k_used = max(max_k_used, cur.k)
        c2 = 2 * (1 << cur.k) - cur.alpha
        if c2 > 0 and c2 % q == 0:
            c = c2 // q
            if (c & 1) == 1 and cur.beta == -c:
                geo_kind = "A"
                geo_c = c
                geo_k = cur.k
                break
        c3 = 3 * (1 << cur.k) - cur.alpha
        if c3 > 0 and c3 % q == 0:
            c = c3 // q
            if (c & 1) == 1 and cur.beta == -c:
                geo_kind = "B"
                geo_c = c
                geo_k = cur.k
                break
        if cur.parity(a_mod, mod_bits) == 0:
            cur = cur.div2()
        else:
            cur.check_neq_h_minus_1(a_min)
            cur = cur.o_step_odd()
            block_drop += 1
        entry_steps += 1

    assert geo_kind is not None, f"v={v}: geometric form not reached for {d0}"
    # 開始ブロック j0 = K + 1, 幾何部開始ブロック j_geo = K + (1 - block_drop)
    # 開始指数 t_geo = 2*N - geo_k = 2*K + (2*K_off - geo_k)
    const_t = 2 * K_off

    if geo_kind == "A":
        assert q * geo_c < (1 << (geo_k + 1)), f"v={v}: (A) positivity fails"
        inv = 2 * (1 - block_drop) - (const_t - geo_k)
        if inv >= 1:
            t_tail = 1 if (inv & 1) == 1 else 2
            j_tail = (inv + t_tail) // 2
            n_geo_min = K_min + (1 - block_drop - j_tail)
            assert n_geo_min >= 0, f"v={v}: n_geo_min={n_geo_min} < 0"
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
            c0 = entry_steps + 2 * (1 - block_drop - j_tail) + tail_steps
            end_v2 = tail_cur.v2_exact(a_mod, mod_bits)
            return {
                "geo": "A",
                "step_formula": (2, c0),
                "end_form": tail_cur,
                "end_v2": end_v2,
                "max_k_used": max_k_used,
            }
        else:
            t_end = -inv
            end_form = LinForm(2, -geo_c * (1 << t_end), 0)
            end_form.check_bounds(a_min)
            c0 = entry_steps + 2 * (1 - block_drop)
            end_v2 = end_form.v2_exact(a_mod, mod_bits)
            return {
                "geo": "A",
                "step_formula": (2, c0),
                "end_form": end_form,
                "end_v2": end_v2,
                "max_k_used": max_k_used,
            }
    else:
        # M - c*2^t: 1 ブロック 1 段、t は 1 減る
        assert q * geo_c < 3 * (1 << geo_k), f"v={v}: (B) positivity fails"
        assert geo_c >= 3, f"v={v}: (B) c >= 3 needed for <= m"
        # M - c*2^t = (3a-3)/2 <=> 3*4^N + 3*(q - 1) = q*c*2^{t+1}
        v2_h_obst = v2(3 * (q - 1))
        t_end_offset = const_t - geo_k - (1 - block_drop)
        t_end_min = K_min + t_end_offset
        assert t_end_min >= 1 and t_end_min + 1 > v2_h_obst, f"v={v}: (B) h-1 check fails"
        c0 = entry_steps + (1 - block_drop)
        return {
            "geo": "B",
            "step_formula": (1, c0),
            "end_form": f"M - {geo_c}*2^(K+{t_end_offset})",
            "end_v2": 0,
            "max_k_used": max_k_used,
        }


def verify_one_v(v: int, exp_ord: int, exp_chains: int, test_Ns: list[int]) -> str:
    q = (1 << v) - 3
    ord4 = mult_order(4, q)
    assert ord4 == exp_ord, f"v={v}: ord_q(4)={ord4}, want {exp_ord}"
    N_min = test_Ns[0]
    K_off = (v + 1) // 2
    assert (N_min - K_off) % 2 == 0
    mod_bits = 2 * N_min
    a_mod = (-pow(q, -1, 1 << mod_bits)) & ((1 << mod_bits) - 1)
    a_min = ((1 << mod_bits) - 1) // q

    h_form = LinForm(3, -1, 1)
    Y_form = LinForm(2, -22, 0)
    assert h_form.v2_exact(a_mod, mod_bits) == v - 1
    assert Y_form.v2_exact(a_mod, mod_bits) == 6

    memo_E: dict[tuple[int, LinForm], bool] = {}
    chains: list[dict] = []
    max_k_E = 0

    def sym_val_O(d0: LinForm) -> bool:
        res = trace_k36d_chain(d0, v, q, a_mod, mod_bits, a_min, N_min)
        chains.append(res)
        if res["end_v2"] <= 3:
            bv = (res["end_v2"] % 2) == 0
        else:
            assert res["end_form"] == Y_form, f"v={v}: unexpected end form {res}"
            bv = True
        _, c0 = res["step_formula"]
        return bv if (c0 % 2 == 0) else (not bv)

    def sym_val_E(kb: int, d: LinForm) -> bool:
        nonlocal max_k_E
        d = d.normalized()
        key = (kb, d)
        if key in memo_E:
            return memo_E[key]
        d.check_bounds(a_min)
        max_k_E = max(max_k_E, d.k)
        if d.parity(a_mod, mod_bits) == 1:
            memo_E[key] = True
            return True
        if sym_val_E(kb, d.div2()):
            memo_E[key] = False
            return False
        e = d.add_h_half()
        lhs_c = 3 * (1 << e.k) - e.alpha
        rhs_c = 2 * (1 << e.k) + e.beta
        if lhs_c > 0 and lhs_c * a_min >= rhs_c:
            b = sym_val_O(e) if kb == 1 else sym_val_E(1, e)
        else:
            assert lhs_c < 0 and lhs_c * a_min < rhs_c, f"v={v}: ambiguous e <= m: {e}"
            b = False
        r = not b
        memo_E[key] = r
        return r

    h1 = sym_val_E(1, h_form)
    h2 = sym_val_E(2, h_form)
    y2 = sym_val_E(2, Y_form)
    assert h1 is False and h2 is True and y2 is True
    assert len(chains) == exp_chains, f"v={v}: chains={len(chains)}, want {exp_chains}"
    max_k_all = max([max_k_E] + [c["max_k_used"] for c in chains])
    assert max_k_all + 1 <= mod_bits

    # BigInt 実数値照合
    max_digits = 0
    for N in test_Ns:
        assert ((1 << (2 * N)) - 1) % q == 0
        a = ((1 << (2 * N)) - 1) // q
        m = 3 * a - 2
        M = 3 * a
        h = (3 * a - 1) // 2
        K = N - K_off
        Y = 2 * a - 22
        assert v2(m + 1) == v and v2(Y) == 6 and K % 2 == 0
        max_digits = max(max_digits, len(str(m)))

        memo_n: dict[tuple[int, int], bool] = {}
        cnt = 0

        def valO_n(j: int, d: int) -> bool:
            nonlocal cnt
            cnt += 1
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

        assert valE_n(1, h) is False and valE_n(2, h) is True and valE_n(2, Y) is True
        assert cnt == exp_chains

    return (
        f"v={v:2d} (q={q:5d}, ord_q(4)={ord4:3d}): SYMBOLIC PROOF VERIFIED "
        f"(chains={len(chains)}, E1(h)=False, E2(h)=True, E2(Y)=True, max_k_used={max_k_all} <= {mod_bits-1}) | "
        f"BigInt {test_Ns} ({len(test_Ns)}/{len(test_Ns)}, up to {max_digits}-digit m), errors=0"
    )


def main() -> None:
    t0 = time.perf_counter()
    # v = 9 の確認: ord_509(4) = 254 (偶数 => K = N - 5 は常に奇数 => K36d' のみ)
    assert mult_order(4, (1 << 9) - 3) == 254

    lines = [
        "gemini-2 independent symbolic & numerical verification of PR #261 (Theorem K36d'' extension: v = 11, 13, 15)",
        "Check v=9 (q=509): ord_509(4)=254 (even => K=N-5 always odd, covered by K36d')",
        verify_one_v(11, 102, 28, [102, 204, 306]),
        verify_one_v(13, 387, 38, [387, 1161, 1935]),
        verify_one_v(15, 234, 50, [234, 468, 702]),
        f"Total elapsed={time.perf_counter() - t0:.2f}s",
    ]
    out_text = "\n".join(lines) + "\n"
    Path("data/gemini2_verify_k36d_v11_15.txt").write_text(out_text, encoding="utf-8")
    print(out_text, end="")


if __name__ == "__main__":
    main()
