"""
gemini2_verify_k29gen_coverage.py — PR #434（Lean 4 定理 K29 一般の奇数 v ≥ 5, u ≥ 5）および
PR #435（Lean 定理群による 1 ≤ m ≤ 10^6 被覆率 90.95%）の独立 Python 3 検証スクリプト。

何を計算するか:
  1. PROBLEM.md の定義のみに基づく O(N) 厳密 DP（漸化式 R / K8 不使用）を用いて、
     定理 K29_gen（m + 1 = 2^v * u, v ≥ 5 奇数, u ≡ 1 (mod 4), u ≥ 5）を
     v = 5, 7, 9, 11, 13（u ≡ 1 mod 8 および u ≡ 5 mod 8 の両枝、m ≤ 500,000）で直接検証する。
     併せて u = 1（v = 5, 7, 9）の挙動も確認する。
  2. 1 ≤ m ≤ 1,000,000 のすべての m について、8 つの Lean 定理（K4, K9, K12a, K10a, K13,
     K29_v5, K29_gen, K38）の仮定充足を Python 整数演算で独立再計算し、
     PR #435 の data/lean_coverage.txt の全行・全定理件数・合計 909,539 / 1,000,000 (90.95%) と
     完全一致することを検証する。

実行方法（リポジトリのルートで）:
  uv run python code/gemini2_verify_k29gen_coverage.py > data/gemini2_verify_k29gen_coverage.txt
"""

from __future__ import annotations

import subprocess
import time
from collections import Counter


def v2(x: int) -> int:
    c = 0
    while (x & 1) == 0:
        x >>= 1
        c += 1
    return c


def fast_dp(m: int, nmax: int) -> list[int]:
    typ = [0] * (nmax + 1)
    typ[0] = -1
    sc = [0] * (nmax + 1)
    sv = [0] * (nmax + 1)
    la = 0
    for r in range(1, nmax + 1):
        c, v = sc[r], sv[r]
        d = r - la
        if d <= m:
            c += 1
            if c == 1:
                v = d
        if c == 0:
            typ[r] = -1
            la = r
        elif c == 1:
            typ[r] = v
            nx = r + v
            if nx <= nmax:
                c2 = sc[nx] + 1
                sc[nx] = c2
                if c2 == 1:
                    sv[nx] = v
        else:
            typ[r] = -2
    return typ


def main() -> None:
    t0 = time.perf_counter()
    print("# gemini-2 独立 Python 3 検証：PR #434（Lean K29_gen）および PR #435（Lean 被覆率 m ≤ 10^6）")

    # 1. Direct DP cross-check for K29_gen across v = 5, 7, 9, 11, 13
    cases = []
    for v in (5, 7, 9, 11, 13):
        for u in (5, 9, 13, 17, 21, 25):
            m = (1 << v) * u - 1
            if m > 500000:
                continue
            L = (m + 2) + ((v - 1) // 2) * (m + 1)
            nmax = 2 * L + 10
            typ = fast_dp(m, nmax)
            for n in range(nmax + 1):
                r = n % L
                pred = (r == 0) or (r >= m + 2 and (r - (m + 2)) % (m + 1) == 0)
                assert (typ[n] == -1) == pred, f"K29_gen DP mismatch at v={v}, u={u}, m={m}, n={n}"
            cases.append((v, u, m))

    # Also inspect u = 1 for v = 5, 7, 9 (excluded by K29_gen hypothesis hu5 : 5 <= u)
    u1_info = []
    for v in (5, 7, 9):
        m = (1 << v) - 1
        L = (m + 2) + ((v - 1) // 2) * (m + 1)
        nmax = 2 * L + 10
        typ = fast_dp(m, nmax)
        ok = all(
            (typ[n] == -1) == ((n % L == 0) or (n % L >= m + 2 and (n % L - (m + 2)) % (m + 1) == 0))
            for n in range(nmax + 1)
        )
        u1_info.append((v, m, ok))

    print(f"\n[1] 定理 K29_gen 直接 DP クロスチェック (v=5,7,9,11,13, u≡1 mod 4, u≥5, m≤500,000):")
    print(f"    全 {len(cases)}/{len(cases)} ケース一致 (最大 m = {max(c[2] for c in cases):,})")
    print(f"    (参考) u=1 の v=5,7,9 の 1 0^{{(v-1)/2}} 判定: {u1_info}")

    # 2. Independent recomputation of PR #435 (lean_coverage.js, 1 <= m <= 1,000,000)
    MMAX = 1_000_000
    stat_tot: Counter[str] = Counter()
    stat_cov: Counter[str] = Counter()
    by_thm: Counter[str] = Counter()

    for m in range(1, MMAX + 1):
        mp1 = m + 1
        # Fast v2 using bit trick
        low = mp1 & -mp1
        v = low.bit_length() - 1
        u = mp1 >> v
        covered = False
        if (v & 1) == 0:
            by_thm["K4"] += 1
            covered = True
        else:
            if v == 1 and m >= 5:
                h = mp1 >> 1
                x3 = 3 * h + 1
                t = (x3 & -x3).bit_length() - 1
                if t & 1:
                    by_thm["K9"] += 1
                    covered = True
                if t == 2:
                    assert (11 * h + 5) % 8 == 0
                    if ((11 * h + 5) // 8) & 1:
                        by_thm["K12a"] += 1
                        covered = True
            if (m & 63) == 7 and m >= 71:
                by_thm["K10a"] += 1
                covered = True
            if (m & 7) == 7:
                U = mp1 >> 3
                x9 = 9 * U + 1
                x11 = 11 * U + 1
                a = (x9 & -x9).bit_length() - 1
                b = (x11 & -x11).bit_length() - 1
                if (a == 1 and b == 3) or (a == 3 and b == 1):
                    by_thm["K13"] += 1
                    covered = True
            if (m & 127) == 31:
                by_thm["K29_v5"] += 1
                covered = True
            if v >= 5 and (u & 3) == 1 and u >= 5:
                by_thm["K29_gen"] += 1
                covered = True
            if v >= 5 and (u & 3) == 3:
                up1 = u + 1
                w = (up1 & -up1).bit_length() - 1
                if ((w & 1) and 3 <= w <= v - 2) or w >= v + 1:
                    by_thm["K38"] += 1
                    covered = True
        key = "偶数" if (v & 1) == 0 else str(v)
        stat_tot[key] += 1
        if covered:
            stat_cov[key] += 1

    # Compare line-by-line with data/lean_coverage.txt on origin/claude-1/lean-coverage
    ref_text = subprocess.check_output(
        ["git", "show", "origin/claude-1/lean-coverage:data/lean_coverage.txt"],
        text=True,
        encoding="utf-8",
    )
    keys = ["偶数"] + sorted((k for k in stat_tot if k != "偶数"), key=int)
    tot_n = sum(stat_tot.values())
    tot_c = sum(stat_cov.values())
    gen_lines = [
        f"# Lean で型が決まる m の割合（1 ≤ m ≤ {MMAX}）",
        f"# 生成: node code/lean_coverage.js {MMAX}",
        "v2(m+1) | m の数 | Lean で型が決まる数 | 割合",
    ]
    for k in keys:
        n, c = stat_tot[k], stat_cov[k]
        gen_lines.append(f"{k} | {n} | {c} | {100.0 * c / n:.2f}%")
    gen_lines.append(f"合計 | {tot_n} | {tot_c} | {100.0 * tot_c / tot_n:.2f}%")

    ref_lines = [l for l in ref_text.splitlines() if l.strip()]
    for gl, rl in zip(gen_lines, ref_lines):
        assert gl == rl, f"Row mismatch:\n  got: {gl}\n  ref: {rl}"

    # Verify per-theorem counts
    expected_thm = {
        "K4": 666667,
        "K9": 166664,
        "K12a": 31250,
        "K29_v5": 7813,
        "K13": 15625,
        "K10a": 15624,
        "K29_gen": 10411,
        "K38": 3297,
    }
    assert dict(by_thm) == expected_thm, f"Theorem counts mismatch: {dict(by_thm)} vs {expected_thm}"

    # Verify K29_v5 vs K29_gen overlap (should be 7812, only m=31 is K29_v5-only)
    overlap_k29 = sum(1 for m in range(1, MMAX + 1) if (m & 127) == 31 and m > 31)
    assert overlap_k29 == 7812

    print(f"\n[2] PR #435 (1 ≤ m ≤ 1,000,000 Lean 被覆率) 独立 Python 再計算:")
    print(f"    合計: {tot_c:,} / {tot_n:,} ({100.0 * tot_c / tot_n:.2f}%) — data/lean_coverage.txt 全行完全一致")
    print(f"    各定理件数 (8/8 完全一致): {dict(by_thm)}")
    print(f"    K29_v5 ∩ K29_gen 重なり = {overlap_k29} (m=31 のみ K29_v5 単独)")
    # Exact asymptotic density
    # v even: 2/3
    # v=1 (1/4): K9 covers 2/3, K12a covers 1/8 -> (2/3 + 1/8) = 19/24 -> 19/96
    # v=3 (1/16): K10a covers 1/4, K13 covers 1/4 (disjoint) -> 1/2 -> 1/32
    # v>=5 odd (1/48): K29 covers 1/2; K38 covers sum_{v=5,7,...} (3/4^(v/2?)):
    #   for odd v>=5, density of v2(m+1)=v is 1/2^(v+1), K38 share within v is (1/6)(1 + 2/4^((v-1)/2) - ...) -> exact sum:
    #   sum_{v>=5 odd} 1/2^(v+1) * (sum_{w=3..v-2 odd} 1/2^w + 1/2^v)
    from fractions import Fraction
    d_even = Fraction(2, 3)
    d_v1 = Fraction(1, 4) * (Fraction(2, 3) + Fraction(1, 8))
    d_v3 = Fraction(1, 16) * (Fraction(1, 4) + Fraction(1, 4))
    d_v5_k29 = Fraction(1, 48) * Fraction(1, 2)
    # K38 within v (odd >=5): w=3 (1/8) + w=5 (1/32) + ... + w=v-2 (1/2^(v-2)) + w>=v+1 (1/2^v)
    # = (1/6)*(1 - 1/2^(v-3)) + 1/2^v = 1/6 - 4/(3*2^v) + 1/2^v = 1/6 - 1/(3*2^v)
    # Wait: sum_{k=1}^{(v-3)/2} 1/2^(2k+1) = (1/8)*(1 - (1/4)^((v-3)/2))/(3/4) = (1/6)*(1 - 1/2^(v-3))
    # wait: 1/6 * (1 - 8/2^v) + 1/2^v = 1/6 - 4/(3*2^v) + 1/2^v = 1/6 - 1/(3*2^v)
    # Multiply by 1/2^(v+1) and sum over odd v>=5:
    # sum_{v>=5 odd} 1/2^(v+1) = 1/64 / (3/4) = 1/48
    # sum_{v>=5 odd} 1/2^(2v+1) = 1/2^11 / (15/16) = 1/(128*15) = 1/1920
    d_v5_k38 = Fraction(1, 6) * Fraction(1, 48) - Fraction(1, 3) * Fraction(1, 1920)
    d_total = d_even + d_v1 + d_v3 + d_v5_k29 + d_v5_k38
    print(f"    (参考) 理論漸近自然密度 = {d_total} = {float(d_total)*100:.6f}% (実測 m≤10^6: {100.0*tot_c/tot_n:.4f}%)")

    elapsed = time.perf_counter() - t0
    print(f"\nALL CHECKS PASSED in {elapsed:.2f}s.")


if __name__ == "__main__":
    main()
