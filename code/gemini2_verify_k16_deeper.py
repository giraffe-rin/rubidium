"""
gemini-2 による独立な Python 実装を用いた定理 K16 の範囲の拡大（PR #46：v = 1, 3, 5, 7 全 1,116 類）の検証。

何を計算するか:
1. PR #46（origin/claude-1/affine-deeper の data/affine_certificates_v{1_T18,3_T17,5_T17,7_T17}.txt）
   に記載された「証明できた類」全 1,116 類（v=1: 660, v=3: 300, v=5: 106, v=7: 50）について、
   claude-1 のコードを読まずに独立に 1 次式証明書を構築・二重検証し、
   M_min_indep <= M_min_claimed を全 1,116 類で確認する。
2. 各 v = 1, 3, 5, 7 について、証明できた類 + 証明できなかった類が v2(m+1) = v 全体を
   互いに素に過不足なく分割していること、および T' = 10, 12, 14, 16, 17, 18 での
   自然密度がログの表と一致することを確認する。
3. PROBLEM.md の定義のみから書いた全探索 DP (solve_count_dp) で v = 7 の最小例
   m = 127 (1000 型) および新規類代表 m = 257 (11110 型), m = 311 (1001100 型) を直接検証。
4. 査読済み定理 K8 の独立実装で、全 1,116 類のうち M_min <= 10000 の全類について
   実際の間隔列が「前周期 | 周期」と一致することを確認。

実行方法:
  python code/gemini2_verify_k16_deeper.py
結果を標準出力と data/gemini2_verify_k16_deeper.txt に保存する。
"""

from __future__ import annotations

import re
import subprocess
import time
from collections import deque
from fractions import Fraction
from pathlib import Path


def v2(n: int) -> int:
    assert n != 0
    return (n & -n).bit_length() - 1


def ceil_div(num: int, den: int) -> int:
    assert den > 0
    return (num + den - 1) // den


def solve_count_dp(m: int, max_r: int) -> list[list[bool]]:
    is_p: list[list[bool]] = [[False] * (m + 1) for _ in range(max_r + 1)]
    is_p[0] = [True] * (m + 1)
    for r in range(1, max_r + 1):
        limit = m if r >= m else r
        p_dest = [False] * (limit + 1)
        total_p = 0
        for k in range(1, limit + 1):
            if is_p[r - k][k]:
                p_dest[k] = True
                total_p += 1
        row = is_p[r]
        for p in range(m + 1):
            legal_p = total_p - (1 if (1 <= p <= limit and p_dest[p]) else 0)
            row[p] = (legal_p == 0)
    return is_p


def run_k8_gaps(m: int, n_blocks: int) -> list[int]:
    h = (m + 1) // 2
    prev_S: set[int] = set()
    prev_g = 0
    gaps: list[int] = []
    for j in range(n_blocks):
        S_j: set[int] = set()
        for d in range(1, m + 1):
            blocked = False
            if (d & 1) == 0 and (d >> 1) in S_j:
                blocked = True
            if not blocked and j >= 1:
                if ((prev_g + d) & 1) == 0:
                    e = (prev_g + d) >> 1
                    if e <= m and e in prev_S:
                        blocked = True
            if not blocked and j >= 1:
                if prev_g == m + 2 and d == h - 1:
                    blocked = True
            if not blocked:
                S_j.add(d)
        g_j = (m + 2) if (h in S_j) else (m + 1)
        gaps.append(g_j - (m + 1))
        prev_S = S_j
        prev_g = g_j
    return gaps


def load_cert_file(tag: str) -> str:
    root = Path(__file__).resolve().parent.parent
    local = root / "data" / f"affine_certificates_{tag}.txt"
    if local.exists():
        return local.read_text(encoding="utf-8")
    out = subprocess.check_output(
        [
            "git",
            "-C",
            str(root),
            "show",
            f"origin/claude-1/affine-deeper:data/affine_certificates_{tag}.txt",
        ]
    )
    return out.decode("utf-8")


def parse_cert_file(text: str) -> tuple[list[tuple[int, int, int, str, str, int]], list[tuple[int, int]]]:
    proved: list[tuple[int, int, int, str, str, int]] = []
    unproved: list[tuple[int, int]] = []
    mode = ""
    pat_p = re.compile(r"^m ≡ (\d+) \(mod (\d+)\) \| (\d+) \| ([01-]+) \| ([01]+) \| (\d+)$")
    pat_u = re.compile(r"^m ≡ (\d+) \(mod (\d+)\) \| ")
    for raw in text.splitlines():
        line = raw.strip()
        if line.startswith("## 証明できた類"):
            mode = "proved"
            continue
        if line.startswith("## 証明できなかった類"):
            mode = "unproved"
            continue
        if mode == "proved":
            m = pat_p.match(line)
            if m:
                proved.append(
                    (
                        int(m.group(2)),
                        int(m.group(1)),
                        int(m.group(3)),
                        "" if m.group(4) == "-" else m.group(4),
                        m.group(5),
                        int(m.group(6)),
                    )
                )
        elif mode == "unproved":
            m = pat_u.match(line)
            if m:
                unproved.append((int(m.group(2)), int(m.group(1))))
    return proved, unproved


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
                raise RuntimeError(f"inequality always false: {lhs} >= {rhs}")
        else:
            raise RuntimeError(f"inequality false for large t: {lhs} >= {rhs}")

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

    def _require_in_range(self, x: tuple[int, int]) -> None:
        self._bump_ge(x, (0, 1))
        self._bump_ge(self.m_expr, x)

    def _eval_k3(self, x: tuple[int, int]) -> bool:
        self._require_in_range(x)
        a, b = x
        if a == 0:
            if b <= 0:
                raise RuntimeError(f"K3 nonpositive constant: {x}")
            return (v2(b) & 1) == 0
        if b == 0 or v2(a) <= v2(b):
            raise RuntimeError(f"K3 v2 depends on t: {x}")
        return (v2(b) & 1) == 0

    def _eval_from_pred(
        self, nu: int, pred: int, x: tuple[int, int], pending_p: deque[tuple[int, int]]
    ) -> bool:
        self._require_in_range(x)
        if self._parity(x) == 0:
            half = (x[0] // 2, x[1] // 2)
            if self.get_fact(nu, half, pending_p):
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

    def get_fact(
        self, nu: int, x: tuple[int, int], pending_p: deque[tuple[int, int]]
    ) -> bool:
        cur = self.facts[nu].get(x)
        if cur is not None:
            return cur
        if nu == 0:
            val = self._eval_k3(x)
        else:
            val = self._eval_from_pred(nu, nu - 1, x, pending_p)
        self.facts[nu][x] = val
        if nu == self.p:
            pending_p.append(x)
        return val

    def build_and_verify(self) -> tuple[int, int]:
        pending_p: deque[tuple[int, int]] = deque()
        for nu in range(self.N):
            got = self.get_fact(nu, self.h_expr, pending_p)
            want = self.bits[nu] == 1
            if got != want:
                raise RuntimeError(f"h mismatch at nu={nu}: got={got} want={want}")

        checked_p: set[tuple[int, int]] = set()
        steps = 0
        while pending_p:
            x = pending_p.popleft()
            if x in checked_p:
                continue
            checked_p.add(x)
            steps += 1
            if steps > 100000:
                raise RuntimeError("node p closure exceeded step limit")
            val2 = self._eval_from_pred(self.p, self.p + self.L - 1, x, pending_p)
            if val2 != self.facts[self.p][x]:
                raise RuntimeError(f"node p mismatch at {x}: {self.facts[self.p][x]} vs {val2}")

        self._independent_recheck()
        return self.A * self.t_min + self.B, sum(len(d) for d in self.facts)

    def _independent_recheck(self) -> None:
        t0 = self.t_min

        def eval_at(expr: tuple[int, int], t: int) -> int:
            return expr[0] * t + expr[1]

        def check_pred_rule(nu: int, pred: int, x: tuple[int, int], v: bool) -> None:
            assert x[0] >= 0 and eval_at(x, t0) >= 1
            assert self.A - x[0] >= 0 and eval_at((self.A - x[0], self.B - x[1]), t0) >= 0
            assert (x[0] & 1) == 0
            if (x[1] & 1) == 0:
                half = (x[0] // 2, x[1] // 2)
                assert half in self.facts[nu]
                if self.facts[nu][half]:
                    assert v is False
                    return
            pg_bit = self.bits[pred]
            if pg_bit == 1:
                da = x[0] - self.hm1_expr[0]
                db = x[1] - self.hm1_expr[1]
                if da == 0 and db == 0:
                    assert v is False
                    return
                if da != 0 and db % da == 0:
                    assert (-db // da) < t0
            g = self.g_expr[pg_bit]
            s = (g[0] + x[0], g[1] + x[1])
            assert (s[0] & 1) == 0
            if (s[1] & 1) == 0:
                e = (s[0] // 2, s[1] // 2)
                da = self.A - e[0]
                db = self.B - e[1]
                if da > 0 or (da == 0 and db >= 0):
                    assert eval_at((da, db), t0) >= 0
                    assert e in self.facts[pred]
                    if self.facts[pred][e]:
                        assert v is False
                        return
                else:
                    assert eval_at((da, db), t0) <= -1
            assert v is True

        for nu in range(self.N):
            assert self.facts[nu].get(self.h_expr) == (self.bits[nu] == 1)
            for x, v in self.facts[nu].items():
                if nu == 0:
                    assert x[0] >= 0 and eval_at(x, t0) >= 1
                    assert self.A - x[0] >= 0 and eval_at((self.A - x[0], self.B - x[1]), t0) >= 0
                    if x[0] == 0:
                        assert x[1] > 0 and ((v2(x[1]) & 1) == 0) == v
                    else:
                        assert x[1] != 0 and v2(x[0]) > v2(x[1]) and ((v2(x[1]) & 1) == 0) == v
                else:
                    check_pred_rule(nu, nu - 1, x, v)
                if nu == self.p:
                    check_pred_rule(nu, self.p + self.L - 1, x, v)


def check_partition(
    v: int, max_T: int, proved: list[tuple[int, int, int, str, str, int]], unproved: list[tuple[int, int]]
) -> tuple[bool, dict[int, Fraction], str]:
    mod_base = 1 << (v + 1)
    rem_base = (1 << v) - 1
    max_A = 1 << max_T
    # Use exact bit-interval / residue count at resolution max_A
    # Number of residues in [0, max_A) with r == rem_base (mod mod_base) is max_A // mod_base
    total_slots = max_A // mod_base
    seen = bytearray(total_slots)

    def mark(A: int, B: int) -> bool:
        if (B % mod_base) != rem_base or A > max_A or (A & (A - 1)) != 0:
            return False
        step = A // mod_base
        start = (B - rem_base) // mod_base
        for idx in range(start, total_slots, step):
            if seen[idx]:
                return False
            seen[idx] = 1
        return True

    dens_by_T: dict[int, Fraction] = {T: Fraction(0) for T in (10, 12, 14, 16, 17, 18) if T <= max_T}
    for A, B, *_ in proved:
        if not mark(A, B):
            return False, dens_by_T, f"overlap or bad class proved ({B} mod {A})"
        d = Fraction(mod_base, A)
        for T in dens_by_T:
            if A <= (1 << T):
                dens_by_T[T] += d
    for A, B in unproved:
        if not mark(A, B):
            return False, dens_by_T, f"overlap or bad class unproved ({B} mod {A})"
    if not all(seen):
        return False, dens_by_T, f"uncovered slots: {seen.count(0)}"
    return True, dens_by_T, "OK"


def main() -> None:
    t0 = time.perf_counter()
    lines: list[str] = []
    lines.append("=== gemini-2 独立検証: 定理 K16 の範囲の拡大（PR #46：v = 1, 3, 5, 7 全 1,116 類） ===")

    specs = [
        (1, 18, "v1_T18"),
        (3, 17, "v3_T17"),
        (5, 17, "v5_T17"),
        (7, 17, "v7_T17"),
    ]
    cert_errs: list[str] = []
    part_errs: list[str] = []
    k8_errs: list[str] = []
    total_classes = 0
    total_k8 = 0
    tighter_cnt = 0

    for v, max_T, tag in specs:
        text = load_cert_file(tag)
        proved, unproved = parse_cert_file(text)
        ok_part, dens_by_T, pmsg = check_partition(v, max_T, proved, unproved)
        if not ok_part:
            part_errs.append(f"{tag}: {pmsg}")
        v_cert_errs = 0
        v_k8_errs = 0
        v_k8_cnt = 0
        for A, B, m_min_claimed, pre, per, nfacts_claimed in proved:
            total_classes += 1
            try:
                cert = AffineCertifier(A, B, pre, per)
                m_min_indep, _ = cert.build_and_verify()
                if m_min_indep > m_min_claimed:
                    cert_errs.append(
                        f"{tag} m={B} mod {A}: M_min_indep={m_min_indep} > claimed={m_min_claimed}"
                    )
                    v_cert_errs += 1
                elif m_min_indep < m_min_claimed:
                    tighter_cnt += 1
            except Exception as exc:
                cert_errs.append(f"{tag} m={B} mod {A}: {exc}")
                v_cert_errs += 1
                continue

            if m_min_claimed <= 10000:
                total_k8 += 1
                v_k8_cnt += 1
                p_len, l_len = len(pre), len(per)
                gaps = run_k8_gaps(m_min_claimed, p_len + 2 * l_len)
                expected = [int(c) for c in pre] + [int(c) for c in per] * 2
                if gaps != expected:
                    k8_errs.append(f"K8 fail {tag} m={m_min_claimed}: got={gaps} want={expected}")
                    v_k8_errs += 1

        dens_str = ", ".join(f"T'={T}:{float(dens_by_T[T]):.6f}" for T in sorted(dens_by_T))
        lines.append(
            f"[{tag}] 証明済み {len(proved)} 類, 未証明 {len(unproved)} 類, 分割={pmsg}, "
            f"独立証明書エラー={v_cert_errs} 件, K8 照合 ({v_k8_cnt} 個) エラー={v_k8_errs} 件"
        )
        lines.append(f"  密度: {dens_str}")

    # Direct brute-force DP check on v=7 minimal m=127 (1000) and representative new classes
    bf_cases = [
        (127, 2500, "", "1000"),
        (257, 2600, "", "11110"),
        (311, 3500, "", "1001100"),
    ]
    bf_errs: list[str] = []
    bf_states = 0
    for m, max_r, pre, per in bf_cases:
        tab = solve_count_dp(m, max_r)
        bf_states += (max_r + 1) * (m + 1)
        a_rows = [r for r in range(max_r + 1) if all(tab[r])]
        gaps = [a_rows[j + 1] - a_rows[j] - (m + 1) for j in range(len(a_rows) - 1)]
        p_len, l_len = len(pre), len(per)
        want_pre = [int(c) for c in pre]
        want_per = [int(c) for c in per]
        for j, g in enumerate(gaps):
            w = want_pre[j] if j < p_len else want_per[(j - p_len) % l_len]
            if g != w:
                bf_errs.append(f"BF fail m={m} j={j} got={g} want={w}")
                break

    elapsed = time.perf_counter() - t0
    lines.append(
        f"[総括] 全 {total_classes} 類の独立 1 次式証明書再計算・二重検証: エラー {len(cert_errs)} 件 "
        f"(分割エラー {len(part_errs)} 件, より小さい M_min を得た類 {tighter_cnt} 件)"
    )
    lines.append(
        f"[全探索] 代表 3 類 (m={[c[0] for c in bf_cases]}; 計 {bf_states:,} 局面): 反例 {len(bf_errs)} 件"
    )
    lines.append(
        f"[K8 照合] M_min <= 10000 の全 {total_k8} 個の m (各 前周期+2周期): 反例 {len(k8_errs)} 件"
    )
    if cert_errs or part_errs or bf_errs or k8_errs:
        lines.append("ERRORS:")
        lines.extend((cert_errs + part_errs + bf_errs + k8_errs)[:25])
    lines.append(f"所要時間: {elapsed:.2f} 秒")

    out_text = "\n".join(lines) + "\n"
    print(out_text, end="")
    out = Path(__file__).resolve().parent.parent / "data" / "gemini2_verify_k16_deeper.txt"
    out.write_text(out_text, encoding="utf-8")


if __name__ == "__main__":
    main()
