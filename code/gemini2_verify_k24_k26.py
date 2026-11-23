"""
PROBLEM.md の定義のみから書いた全探索ソルバー、査読済み定理 K8（PR #111）の独立実装、
および厳密整数演算による 2 値 1 次式証明書独立検証器（AffineCertifier）により、
PR #68（K24 不動点 x* = (m+2)/15 の非到達）および PR #72（補題 K26.0・K26 p = 1 および偶数 2<=p<=30 全 16 類）
を独立検証する。

実行方法:
    python code/gemini2_verify_k24_k26.py
出力:
    data/gemini2_verify_k24_k26.txt
"""

from __future__ import annotations

import time
from collections import deque
from pathlib import Path


def v2(n: int) -> int:
    assert n > 0
    return (n & -n).bit_length() - 1


def ceil_div(num: int, den: int) -> int:
    assert den > 0
    return (num + den - 1) // den


def solve_full_search_gaps(m: int, max_r: int) -> list[int]:
    win = [[False] * (m + 1) for _ in range(max_r + 1)]
    a_rows = [0]
    for r in range(1, max_r + 1):
        limit = min(m, r)
        losing_count = 0
        only_losing_k = -1
        for k in range(1, limit + 1):
            if not win[r - k][k]:
                losing_count += 1
                only_losing_k = k
        if losing_count == 0:
            a_rows.append(r)
        elif losing_count >= 2:
            row = win[r]
            for p in range(m + 1):
                row[p] = True
        else:
            row = win[r]
            for p in range(m + 1):
                if p != only_losing_k:
                    row[p] = True
    return [a_rows[i + 1] - a_rows[i] for i in range(len(a_rows) - 1)]


class LazyK8:
    def __init__(self, m: int) -> None:
        self.m = m
        self.h = (m + 1) // 2
        self.gaps: list[int] = []
        self.memo: list[dict[int, bool]] = []

    def in_S(self, J: int, x: int) -> bool:
        while len(self.memo) <= J:
            self.memo.append({})
        cache = self.memo[J]
        if x in cache:
            return cache[x]
        if J == 0:
            res = (v2(x) & 1) == 0
        else:
            g = self.gap(J - 1)
            res = True
            if (x & 1) == 0 and self.in_S(J, x >> 1):
                res = False
            elif ((g + x) & 1) == 0:
                half = (g + x) >> 1
                if 1 <= half <= self.m and self.in_S(J - 1, half):
                    res = False
            if res and g == self.m + 2 and x == self.h - 1:
                res = False
        cache[x] = res
        return res

    def gap(self, J: int) -> int:
        while len(self.gaps) <= J:
            idx = len(self.gaps)
            self.gaps.append(self.m + 2 if self.in_S(idx, self.h) else self.m + 1)
        return self.gaps[J]


class AffineCertifier:
    def __init__(self, A: int, B: int, pre: str, per: str) -> None:
        self.A = A
        self.B = B
        self.p = len(pre)
        self.L = len(per)
        self.N = self.p + self.L
        self.bits = [int(c) for c in (pre + per)]
        self.m_expr = (A, B)
        self.h_expr = (A // 2, (B + 1) // 2)
        self.hm1_expr = (A // 2, (B - 1) // 2)
        self.g_expr = [(A, B + 1), (A, B + 2)]
        self.t_min = 0
        self.facts: list[dict[tuple[int, int], bool]] = [{} for _ in range(self.N)]

    def _bump_ge(self, lhs: tuple[int, int], rhs: tuple[int, int]) -> None:
        da = lhs[0] - rhs[0]
        db = lhs[1] - rhs[1]
        if da > 0:
            req = max(0, ceil_div(-db, da))
            if req > self.t_min:
                self.t_min = req
        elif da == 0:
            if db < 0:
                raise RuntimeError("ineq false")
        else:
            raise RuntimeError("ineq false large t")

    def _compare_le(self, lhs: tuple[int, int], rhs: tuple[int, int]) -> bool:
        da = rhs[0] - lhs[0]
        db = rhs[1] - lhs[1]
        if da > 0:
            req = max(0, ceil_div(-db, da))
            if req > self.t_min:
                self.t_min = req
            return True
        if da < 0:
            req = max(0, ceil_div(db + 1, -da))
            if req > self.t_min:
                self.t_min = req
            return False
        return db >= 0

    def _is_hm1(self, x: tuple[int, int]) -> bool:
        da = x[0] - self.hm1_expr[0]
        db = x[1] - self.hm1_expr[1]
        if da == 0:
            return db == 0
        if db % da == 0:
            t0 = -db // da
            if t0 >= 0 and t0 + 1 > self.t_min:
                self.t_min = t0 + 1
        return False

    def _parity(self, x: tuple[int, int]) -> int:
        if (x[0] & 1) != 0:
            raise RuntimeError(f"parity depends on t: {x}")
        return x[1] & 1

    def _eval_k3(self, x: tuple[int, int]) -> bool:
        self._bump_ge(x, (0, 1))
        self._bump_ge(self.m_expr, x)
        a, b = x
        if a == 0:
            assert b > 0
            return (v2(b) & 1) == 0
        if b == 0 or v2(a) <= v2(b):
            raise RuntimeError(f"K3 v2 depends on t: {x}")
        return (v2(b) & 1) == 0

    def _eval_from_pred(self, nu: int, pred: int, x: tuple[int, int], pending_p: deque) -> bool:
        self._bump_ge(x, (0, 1))
        self._bump_ge(self.m_expr, x)
        if self._parity(x) == 0:
            if self.get_fact(nu, (x[0] // 2, x[1] // 2), pending_p):
                return False
        pg_bit = self.bits[pred]
        if pg_bit == 1 and self._is_hm1(x):
            return False
        g = self.g_expr[pg_bit]
        s = (g[0] + x[0], g[1] + x[1])
        if self._parity(s) == 0:
            e = (s[0] // 2, s[1] // 2)
            if self._compare_le(e, self.m_expr):
                if self.get_fact(pred, e, pending_p):
                    return False
        return True

    def get_fact(self, nu: int, x: tuple[int, int], pending_p: deque) -> bool:
        cur = self.facts[nu].get(x)
        if cur is not None:
            return cur
        val = self._eval_k3(x) if nu == 0 else self._eval_from_pred(nu, nu - 1, x, pending_p)
        self.facts[nu][x] = val
        if nu == self.p:
            pending_p.append(x)
        return val

    def build_and_verify(self) -> tuple[int, int]:
        pending_p: deque = deque()
        for nu in range(self.N):
            assert self.get_fact(nu, self.h_expr, pending_p) == (self.bits[nu] == 1)
        checked_p: set[tuple[int, int]] = set()
        while pending_p:
            x = pending_p.popleft()
            if x in checked_p:
                continue
            checked_p.add(x)
            val2 = self._eval_from_pred(self.p, self.p + self.L - 1, x, pending_p)
            assert val2 == self.facts[self.p][x]
        # 独立再チェック
        tm = self.t_min
        for nu in range(self.N):
            for (a, b), val in self.facts[nu].items():
                assert a >= 0 and a * tm + b >= 1 and (self.A - a) * tm + (self.B - b) >= 0
                if nu == 0:
                    assert ((v2(b) & 1) == 0) == val and (a == 0 or v2(a) > v2(b))
                preds = [self.p + self.L - 1] if nu == 0 and self.p == 0 else ([nu - 1, self.p + self.L - 1] if nu == self.p else ([nu - 1] if nu > 0 else []))
                for pred in preds:
                    blocked = False
                    if (a & 1) == 0 and (b & 1) == 0 and self.facts[nu].get((a // 2, b // 2), False):
                        blocked = True
                    pg_bit = self.bits[pred]
                    if not blocked and pg_bit == 1:
                        da, db = a - self.hm1_expr[0], b - self.hm1_expr[1]
                        if da == 0 and db == 0:
                            blocked = True
                        elif da != 0 and db % da == 0:
                            assert -db // da < tm
                    if not blocked:
                        g = self.g_expr[pg_bit]
                        sa, sb = g[0] + a, g[1] + b
                        assert (sa & 1) == 0
                        if (sb & 1) == 0:
                            ea, eb = sa // 2, sb // 2
                            if ea < self.A or (ea == self.A and eb <= self.B):
                                assert (self.A - ea) * tm + (self.B - eb) >= 0
                                if self.facts[pred].get((ea, eb), False):
                                    blocked = True
                            else:
                                assert (ea - self.A) * tm + (eb - self.B) >= 1
                    assert (not blocked) == val
        return self.A * tm + self.B, sum(len(d) for d in self.facts)


def k26_congruence_class(p: int) -> tuple[int, int]:
    """v2(m+1) = 3, u ≡ 1 (mod 4), v2((11u+1)/2) = p に対応する m ≡ B (mod 2^{p+5}) を求める。"""
    # 11u + 1 ≡ 2^{p+1} (mod 2^{p+2}) -> u ≡ (2^{p+1} - 1) * inv(11) (mod 2^{p+2})
    mod_u = 1 << (p + 2)
    inv11 = pow(11, -1, mod_u)
    u0 = ((1 << (p + 1)) - 1) * inv11 % mod_u
    assert u0 % 4 == 1 and v2((11 * u0 + 1) // 2) == p
    A = 1 << (p + 5)
    B = 8 * u0 - 1
    assert B < A and v2(B + 1) == 3
    return A, B


def main() -> None:
    t0 = time.perf_counter()
    # 1. PR #68: K23 再帰が不動点 x* = (m+2)/15 に入らないことの数値確認 (5 <= m <= 300000)
    k24_checked = 0
    k24_fixed_candidates = 0
    for m in range(5, 300001, 2):
        v = v2(m + 1)
        if (v & 1) == 0:
            continue
        k24_checked += 1
        x = (m + 1) >> v
        if (m + 2) % 15 == 0 and ((m + 2) // 15) % 2 == 1:
            k24_fixed_candidates += 1
            x_star = (m + 2) // 15
        else:
            x_star = -1
        for _ in range(50):
            assert x != x_star
            E = m + 2 - 3 * x
            ell = v2(abs(E))
            if ell & 1:
                break
            c = (m + 2 - E // (1 << ell)) // 3
            mu = v2(c)
            if mu & 1:
                break
            x = c >> mu
        else:
            raise RuntimeError(f"K23 did not terminate for m={m}")

    # 2. PR #72 補題 K26.0: 全探索（m = 39, 71, 103, 487）+ K8 大規模検証（23 <= m <= 300000）
    fs_positions = 0
    for m, p_exp in [(39, 2), (71, 1), (103, 3), (487, 4)]:
        u = (m + 1) // 8
        assert u % 4 == 1 and v2((11 * u + 1) // 2) == p_exp
        max_r = 12 * (m + 2)
        gaps = solve_full_search_gaps(m, max_r)
        assert gaps[0] == m + 2 and gaps[1] == m + 1
        assert (gaps[2] == m + 2) == (p_exp % 2 == 1)
        fs_positions += (max_r + 1) * (m + 1)

    k260_count = 0
    for u in range(5, 37501, 4):
        m = 8 * u - 1
        if m > 300000:
            break
        p_val = v2((11 * u + 1) // 2)
        lazy = LazyK8(m)
        assert lazy.gap(0) == m + 2 and lazy.gap(1) == m + 1
        assert (lazy.gap(2) == m + 2) == (p_val % 2 == 1)
        k260_count += 1

    # 3. PR #72 部分的証明: p = 1 および偶数 2 <= p <= 30 の全 16 類を AffineCertifier でゼロから独立再計算
    cert_results = []
    for p_val in [1] + list(range(2, 31, 2)):
        A, B = k26_congruence_class(p_val)
        per = "10" if p_val == 1 else "100"
        cert = AffineCertifier(A, B, "", per)
        m_min, nfacts = cert.build_and_verify()
        expected_min = 71 if p_val == 1 else B
        assert m_min == expected_min, f"p={p_val}: m_min={m_min} != {expected_min}"
        cert_results.append(f"p={p_val}(mod 2^{p_val+5},M_min={m_min},facts={nfacts})")

    elapsed = time.perf_counter() - t0
    lines = [
        "gemini-2 independent verification of PR #68 (K24 fixed point) and PR #72 (Lemma K26.0 + K26 p=1,2..30 even)",
        f"PR #68: odd-v m <= 300000 ({k24_checked} values, {k24_fixed_candidates} with odd integer x*=(m+2)/15): 0 cycles, 0 hits on x*",
        f"PR #72 Lemma K26.0 full-search (m=39,71,103,487): total_positions={fs_positions}, errors=0",
        f"PR #72 Lemma K26.0 K8 check (v=3, u≡1 mod 4, u>=5, m<=300000): count={k260_count}, errors=0",
        f"PR #72 K26 partial proof (p=1 and even 2<=p<=30, 16 classes): all 16 rebuilt & double-verified, errors=0",
        "  classes: " + ", ".join(cert_results),
        f"elapsed: {elapsed:.2f}s",
    ]
    out_text = "\n".join(lines) + "\n"
    Path("data/gemini2_verify_k24_k26.txt").write_text(out_text, encoding="utf-8")
    print(out_text, end="")


if __name__ == "__main__":
    main()
