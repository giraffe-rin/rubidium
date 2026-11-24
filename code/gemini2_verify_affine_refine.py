"""
gemini-2 による独立 Python 1 次式証明書生成器・二重検証器を用いて、
2 値 1 次式証明書の拡張 PR 群 5 本の全「証明できた類」をゼロから独立再計算・検証する。

対象 PR:
- PR #58 (origin/claude-1/affine-refine): data/affine_refine_v1_T20.txt (v=1, A<=2^20)
- PR #74 (origin/claude-1/affine-refine-v3): data/affine_refine_v3_T19.txt (v=3, A<=2^19)
- PR #76 (origin/claude-1/affine-refine-v5): data/affine_refine_v5_T19.txt (v=5, A<=2^19)
- PR #78 (origin/claude-1/affine-refine-v7): data/affine_refine_v7_T19.txt (v=7, A<=2^19)
- PR #86 (origin/claude-1/affine-v9-v11): data/affine_certificates_v9_T17.txt, v11_T17.txt (v=9,11, A<=2^17)

実行方法:
    python code/gemini2_verify_affine_refine.py
出力:
    data/gemini2_verify_affine_refine.txt
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
    """PR #136（gemini-2/review-k16）で健全性を査読済みの 2 値 1 次式証明書独立検証器。"""

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
        while pending_p:
            x = pending_p.popleft()
            if x in checked_p:
                continue
            checked_p.add(x)
            val2 = self._eval_from_pred(self.p, self.p + self.L - 1, x, pending_p)
            if val2 != self.facts[self.p][x]:
                raise RuntimeError(f"node p mismatch at {x}")
        # 独立再チェック（全事実が t >= t_min で厳密に保存されること）
        self._recheck()
        return self.A * self.t_min + self.B, sum(len(d) for d in self.facts)

    def _recheck(self) -> None:
        tm = self.t_min
        m_min = self.A * tm + self.B
        for nu in range(self.N):
            for x, val in self.facts[nu].items():
                a, b = x
                assert a >= 0 and a * tm + b >= 1
                assert self.A >= a and (self.A - a) * tm + (self.B - b) >= 0
                if nu == 0:
                    if a == 0:
                        assert ((v2(b) & 1) == 0) == val
                    else:
                        assert b != 0 and v2(a) > v2(b) and ((v2(b) & 1) == 0) == val
                preds = [nu - 1] if nu != self.p else ([self.p + self.L - 1] if nu == 0 else [nu - 1, self.p + self.L - 1])
                for pred in preds:
                    if nu == 0 and pred == -1:
                        continue
                    blocked = False
                    if (a & 1) == 0 and (b & 1) == 0:
                        half = (a // 2, b // 2)
                        if half in self.facts[nu] and self.facts[nu][half]:
                            blocked = True
                    pg_bit = self.bits[pred]
                    if not blocked and pg_bit == 1:
                        da = a - self.hm1_expr[0]
                        db = b - self.hm1_expr[1]
                        if da == 0 and db == 0:
                            blocked = True
                        elif da != 0:
                            # check never equals for t >= tm
                            if db % da == 0:
                                assert -db // da < tm
                    if not blocked:
                        g = self.g_expr[pg_bit]
                        sa, sb = g[0] + a, g[1] + b
                        assert (sa & 1) == 0
                        if (sb & 1) == 0:
                            ea, eb = sa // 2, sb // 2
                            if ea < self.A or (ea == self.A and eb <= self.B):
                                assert (self.A - ea) * tm + (self.B - eb) >= 0
                                if (ea, eb) in self.facts[pred] and self.facts[pred][(ea, eb)]:
                                    blocked = True
                            else:
                                assert (ea - self.A) * tm + (eb - self.B) >= 1
                    assert (not blocked) == val


def git_show(repo: Path, ref_path: str) -> str:
    return subprocess.check_output(["git", "-C", str(repo), "show", ref_path]).decode("utf-8")


def parse_file(text: str) -> tuple[list[tuple[int, int, int, str, str, int]], list[tuple[int, int]]]:
    proved: list[tuple[int, int, int, str, str, int]] = []
    unproved: list[tuple[int, int]] = []
    mode = ""
    pat_p = re.compile(r"^m ≡ (\d+) \(mod (\d+)\) \| (\d+) \| ([01-]+) \| ([01]+) \| (\d+)$")
    pat_u = re.compile(r"^m ≡ (\d+) \(mod (\d+)\) \| ")
    for raw in text.splitlines():
        line = raw.strip()
        if line.startswith("## 新しく証明できた類") or line.startswith("## 証明できた類"):
            mode = "proved"
            continue
        if line.startswith("## まだ決まらない類") or line.startswith("## 証明できなかった類"):
            mode = "unproved"
            continue
        if mode == "proved":
            m = pat_p.match(line)
            if m:
                proved.append((int(m.group(2)), int(m.group(1)), int(m.group(3)),
                               "" if m.group(4) == "-" else m.group(4), m.group(5), int(m.group(6))))
        elif mode == "unproved":
            m = pat_u.match(line)
            if m:
                unproved.append((int(m.group(2)), int(m.group(1))))
    return proved, unproved


def check_partition_full(v: int, max_T: int, proved: list, unproved: list) -> tuple[bool, Fraction, str]:
    mod_base = 1 << (v + 1)
    rem_base = (1 << v) - 1
    total_slots = 1 << (max_T - (v + 1))
    seen = bytearray(total_slots)
    dens = Fraction(0)

    def mark(A: int, B: int) -> bool:
        if A < mod_base or (A & (A - 1)) != 0 or A > (1 << max_T):
            return False
        if B % mod_base != rem_base:
            return False
        step = A // mod_base
        start = (B - rem_base) // mod_base
        for idx in range(start, total_slots, step):
            if seen[idx]:
                return False
            seen[idx] = 1
        return True

    for A, B, *_ in proved:
        if not mark(A, B):
            return False, dens, f"bad/overlap proved ({B} mod {A})"
        dens += Fraction(mod_base, A)
    for A, B in unproved:
        if not mark(A, B):
            return False, dens, f"bad/overlap unproved ({B} mod {A})"
    if not all(seen):
        return False, dens, f"uncovered={seen.count(0)}"
    return True, dens, "OK"


def main() -> None:
    t0 = time.perf_counter()
    repo = Path(__file__).resolve().parent.parent
    lines = ["=== gemini-2 独立検証: 2 値 1 次式証明書群（PR #58, #74, #76, #78, #86） ==="]

    # (pr_label, v, max_T, base_ref_or_None, target_ref)
    jobs = [
        ("PR#58 (v=1, T20 refine)", 1, 20, "origin/claude-1/affine-deeper:data/affine_certificates_v1_T18.txt",
         "origin/claude-1/affine-refine:data/affine_refine_v1_T20.txt"),
        ("PR#74 (v=3, T19 refine)", 3, 19, "origin/claude-1/affine-deeper:data/affine_certificates_v3_T17.txt",
         "origin/claude-1/affine-refine-v3:data/affine_refine_v3_T19.txt"),
        ("PR#76 (v=5, T19 refine)", 5, 19, "origin/claude-1/affine-deeper:data/affine_certificates_v5_T17.txt",
         "origin/claude-1/affine-refine-v5:data/affine_refine_v5_T19.txt"),
        ("PR#78 (v=7, T19 refine)", 7, 19, "origin/claude-1/affine-deeper:data/affine_certificates_v7_T17.txt",
         "origin/claude-1/affine-refine-v7:data/affine_refine_v7_T19.txt"),
        ("PR#86 (v=9, T17)", 9, 17, None,
         "origin/claude-1/affine-v9-v11:data/affine_certificates_v9_T17.txt"),
        ("PR#86 (v=11, T17)", 11, 17, None,
         "origin/claude-1/affine-v9-v11:data/affine_certificates_v11_T17.txt"),
    ]

    grand_proved = 0
    grand_cert_errs = 0
    grand_part_errs = 0
    grand_k8 = 0
    grand_k8_errs = 0

    for label, v, max_T, base_ref, target_ref in jobs:
        proved_new, unproved_new = parse_file(git_show(repo, target_ref))
        if base_ref is not None:
            base_proved, _ = parse_file(git_show(repo, base_ref))
            all_proved = base_proved + proved_new
        else:
            all_proved = proved_new

        ok_part, total_dens, pmsg = check_partition_full(v, max_T, all_proved, unproved_new)
        if not ok_part:
            grand_part_errs += 1

        cert_errs = 0
        k8_cnt = 0
        k8_errs = 0
        for idx, (A, B, m_min_claimed, pre, per, _) in enumerate(proved_new):
            grand_proved += 1
            try:
                cert = AffineCertifier(A, B, pre, per)
                m_min_indep, _ = cert.build_and_verify()
                if m_min_indep > m_min_claimed:
                    cert_errs += 1
            except Exception:
                cert_errs += 1
                continue
            # M_min <= 40000 の類および各ファイル先頭 10 類を査読済み K8 で実測照合
            if m_min_claimed <= 40000 or idx < 10:
                k8_cnt += 1
                grand_k8 += 1
                lazy = LazyK8(m_min_claimed)
                p_len, l_len = len(pre), len(per)
                want = [int(c) for c in pre] + [int(c) for c in per] * 2
                got = [1 if lazy.gap(j) == m_min_claimed + 2 else 0 for j in range(p_len + 2 * l_len)]
                if got != want:
                    k8_errs += 1
                    grand_k8_errs += 1
        grand_cert_errs += cert_errs
        lines.append(
            f"[{label}] 新規証明 {len(proved_new)} 類, 未証明 {len(unproved_new)} 類, "
            f"合計密度={float(total_dens):.6f} ({total_dens}), 分割={pmsg}, "
            f"独立再計算エラー={cert_errs}, K8 照合({k8_cnt}個)エラー={k8_errs}"
        )

    elapsed = time.perf_counter() - t0
    lines.append(
        f"[総括] 新規証明全 {grand_proved} 類の独立再計算・二重検証: エラー {grand_cert_errs} 件, "
        f"分割エラー {grand_part_errs} 件, K8 実測照合 ({grand_k8} 個) エラー {grand_k8_errs} 件, 所要時間 {elapsed:.2f} 秒"
    )
    out_text = "\n".join(lines) + "\n"
    Path("data/gemini2_verify_affine_refine.txt").write_text(out_text, encoding="utf-8")
    print(out_text, end="")
    assert grand_cert_errs == 0 and grand_part_errs == 0 and grand_k8_errs == 0


if __name__ == "__main__":
    main()
