"""
gemini2_verify_lean_k15.py — PR #443（Lean 4 定理 K15 一般の k ≥ 2：`Rubidium.K15_gen`）および
PR #444（Lean 4 まとめ・被覆率 92.00%）の独立 Python 3 検証スクリプト。

何を計算するか:
  1. m ≤ 1,000,000（v2(m+1) = 1, v2(3h+1) = 2k ≥ 4）の全件で、Lean 仮定 w ≡ 3 (mod 4) と
     元の仮定 Q = (m+2+w)/2 奇数の完全同値性を検証。
  2. PROBLEM.md の定義のみに基づく O(N) 厳密 DP（漸化式 R / K8 不使用）で、
     k = 2, 3, 4, 5, 6, 7（最小 w = 7 および w = 19, 31 等）の代表ケースについて
     0 ≤ n ≤ 2L + 10 において K15_gen の主張（1(10)^k 型）と完全一致することを検証。
  3. 1 ≤ m ≤ 1,000,000 の全数について 9 定理（K4, K9, K12a, K15, K10a, K13, K29_v5, K29_gen, K38）の
     被覆率を独立再計算し、PR #443/#444 の data/lean_coverage.txt 全行・合計 919,961 / 1,000,000 (92.00%)
     および全 9 定理件数との完全一致を確認する。

実行方法（リポジトリのルートで）:
  uv run python code/gemini2_verify_lean_k15.py > data/gemini2_verify_lean_k15.txt
"""

from __future__ import annotations

import subprocess
import time
from collections import Counter
from fractions import Fraction


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
    print("# gemini-2 独立 Python 3 検証：PR #443（Lean K15_gen）および PR #444（Lean 被覆率 92.00%）")

    # 1. Direct DP cross-check for K15_gen across k = 2, 3, 4, 5, 6, 7
    dp_checked = []
    for k in (2, 3, 4, 5, 6, 7):
        ws = (7, 19, 31) if k <= 5 else (7,)
        for w in ws:
            assert (4 ** k * w - 1) % 3 == 0
            h = (4 ** k * w - 1) // 3
            m = 2 * h - 1
            Q = (m + 2 + w) // 2
            assert Q % 2 == 1 and w % 4 == 3
            L = (m + 2) + k * (2 * m + 3)
            nmax = 2 * L + 10
            typ = fast_dp(m, nmax)
            for n in range(nmax + 1):
                r = n % L
                pred = (r == 0) or (
                    r >= m + 2
                    and ((r - (m + 2)) % (2 * m + 3) in (0, m + 2))
                )
                assert (typ[n] == -1) == pred, f"K15_gen DP mismatch at k={k}, w={w}, m={m}, n={n}"
            dp_checked.append((k, w, m, L))

    print(f"\n[1] 定理 K15_gen 直接 DP クロスチェック (k = 2..7, 漸化式 R 不使用):")
    print(f"    全 {len(dp_checked)}/{len(dp_checked)} ケース一致 (最大 k=7, m={dp_checked[-1][2]:,}, L={dp_checked[-1][3]:,})")
    for k, w, m, L in dp_checked:
        print(f"    k={k}, w={w:2d}, m={m:6d}, L={L:8d} -> OK (1(10)^{k})")

    # 2. Hypothesis equivalence & full 1 <= m <= 1,000,000 coverage recomputation
    MMAX = 1_000_000
    stat_tot: Counter[str] = Counter()
    stat_cov: Counter[str] = Counter()
    by_thm: Counter[str] = Counter()
    hyp_eq_cnt = 0

    for m in range(1, MMAX + 1):
        mp1 = m + 1
        v = (mp1 & -mp1).bit_length() - 1
        u = mp1 >> v
        cov = False
        if (v & 1) == 0:
            by_thm["K4"] += 1
            cov = True
        else:
            if v == 1 and m >= 5:
                h = mp1 >> 1
                x3 = 3 * h + 1
                t = (x3 & -x3).bit_length() - 1
                if t & 1:
                    by_thm["K9"] += 1
                    cov = True
                elif t == 2:
                    if ((11 * h + 5) // 8) & 1:
                        by_thm["K12a"] += 1
                        cov = True
                elif t >= 4:
                    w = x3 >> t
                    Q_odd = (((m + 2 + w) // 2) & 1) == 1
                    w_mod4_3 = (w & 3) == 3
                    assert Q_odd == w_mod4_3, f"K15 hyp mismatch at m={m}"
                    hyp_eq_cnt += 1
                    if w_mod4_3:
                        by_thm["K15"] += 1
                        cov = True
            if (m & 63) == 7 and m >= 71:
                by_thm["K10a"] += 1
                cov = True
            if (m & 7) == 7:
                U = mp1 >> 3
                x9 = 9 * U + 1
                x11 = 11 * U + 1
                a = (x9 & -x9).bit_length() - 1
                b = (x11 & -x11).bit_length() - 1
                if (a == 1 and b == 3) or (a == 3 and b == 1):
                    by_thm["K13"] += 1
                    cov = True
            if (m & 127) == 31:
                by_thm["K29_v5"] += 1
                cov = True
            if v >= 5 and (u & 3) == 1:
                by_thm["K29_gen"] += 1
                cov = True
            if v >= 5 and (u & 3) == 3:
                up1 = u + 1
                w38 = (up1 & -up1).bit_length() - 1
                if ((w38 & 1) and 3 <= w38 <= v - 2) or w38 >= v + 1:
                    by_thm["K38"] += 1
                    cov = True
        key = "偶数" if (v & 1) == 0 else str(v)
        stat_tot[key] += 1
        if cov:
            stat_cov[key] += 1

    ref_text = subprocess.check_output(
        ["git", "show", "origin/claude-1/lean-k15:data/lean_coverage.txt"],
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

    expected_thm = {
        "K4": 666667,
        "K9": 166664,
        "K12a": 31250,
        "K29_v5": 7813,
        "K29_gen": 10419,
        "K13": 15625,
        "K10a": 15624,
        "K15": 10415,
        "K38": 3297,
    }
    assert dict(by_thm) == expected_thm, f"Counts mismatch: {dict(by_thm)} vs {expected_thm}"

    # Exact asymptotic natural density with K15 included:
    # v=1 (1/4): K9 (2/3) + K12a (1/8) + K15 (sum_{k>=2} 1/2^(2k+1) = (1/32)/(3/4) = 1/24) = 2/3 + 1/6 = 5/6!
    d_even = Fraction(2, 3)
    d_v1 = Fraction(1, 4) * Fraction(5, 6)  # 5/24 = 83.3333...% of v=1!
    d_v3 = Fraction(1, 16) * Fraction(1, 2)
    d_v5_k29 = Fraction(1, 48) * Fraction(1, 2)
    d_v5_k38 = Fraction(1, 6) * Fraction(1, 48) - Fraction(1, 3) * Fraction(1, 1920)
    d_tot = d_even + d_v1 + d_v3 + d_v5_k29 + d_v5_k38

    print(f"\n[2] K15 仮定同値性 (Q 奇数 ⇔ w≡3 mod 4) m ≤ 10^6 全数検証: {hyp_eq_cnt:,}/{hyp_eq_cnt:,} 一致")
    print(f"\n[3] PR #443/#444 (1 ≤ m ≤ 1,000,000 Lean 被覆率) 独立 Python 再計算:")
    print(f"    合計: {tot_c:,} / {tot_n:,} ({100.0 * tot_c / tot_n:.2f}%) — data/lean_coverage.txt 全行完全一致")
    print(f"    v2(m+1)=1: {stat_cov['1']:,}/{stat_tot['1']:,} ({100.0*stat_cov['1']/stat_tot['1']:.2f}%) [理論漸近 5/6 = 83.3333%]")
    print(f"    各定理件数 (9/9 完全一致): {dict(by_thm)}")
    print(f"    理論漸近自然密度 = {d_tot} = {float(d_tot)*100:.6f}% (実測 m≤10^6: {100.0*tot_c/tot_n:.4f}%)")

    elapsed = time.perf_counter() - t0
    print(f"\nALL CHECKS PASSED in {elapsed:.2f}s.")


if __name__ == "__main__":
    main()
