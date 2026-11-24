"""
gemini2_verify_k64.py — PR #446（予想 K64：`m ≤ 40000` 全 416 ケース）および
PR #449（Lean 4 定理 K64：`Rubidium.K64` および更新被覆率 93.04%）の独立 Python 3 検証スクリプト。

何を計算するか:
  1. PROBLEM.md の定義のみに基づく O(N) 厳密 DP（漸化式 R / K8 不使用）を並列実行し、
     PR #446 の data/k64_chain.txt の全 416 ケース（m ≤ 40000、j = 1..5、元は m ≤ 4000 の 41 件のみ直接 DP）
     すべてについて 0 ≤ n ≤ 2L + 10 で型 1^{j+2} 0（前周期なし）と完全一致することを検証する。
     併せて j = 0（K12a と一致）の最小例も確認。
  2. 1 ≤ m ≤ 1,000,000 の全数について 10 定理（K4, K9, K12a, K64, K15, K10a, K13,
     K29_v5, K29_gen, K38）の被覆率を独立再計算し、PR #449 の data/lean_coverage.txt 全行・
     合計 930,377 / 1,000,000 (93.04%)・v2=1 87.50%・全 10 定理件数との完全一致を確認する。

実行方法（リポジトリのルートで）:
  uv run python code/gemini2_verify_k64.py > data/gemini2_verify_k64.txt
"""

from __future__ import annotations

import subprocess
import time
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
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


def check_one_k64(task: tuple[int, int]) -> tuple[int, int, bool]:
    m, j = task
    L = (j + 2) * (m + 2) + (m + 1)
    nmax = 2 * L + 10
    typ = fast_dp(m, nmax)
    lim = (j + 2) * (m + 2)
    for n in range(nmax + 1):
        r = n % L
        pred = (r % (m + 2) == 0) and (r <= lim)
        if (typ[n] == -1) != pred:
            return (m, j, False)
    return (m, j, True)


def main() -> None:
    t0 = time.perf_counter()
    print("# gemini-2 独立 Python 3 検証：PR #446（予想 K64）および PR #449（Lean 定理 K64・被覆率 93.04%）")

    # 1. Verify ALL 416 cases of data/k64_chain.txt (m <= 40000, j = 1..5) by direct PROBLEM.md DP!
    chain_text = subprocess.check_output(
        ["git", "show", "origin/claude-1/k64:data/k64_chain.txt"],
        text=True,
        encoding="utf-8",
    )
    file_rows: list[tuple[int, int]] = []
    for line in chain_text.splitlines():
        if "|" not in line:
            continue
        parts = [p.strip() for p in line.split("|")]
        if not parts[0].isdigit():
            continue
        m = int(parts[0])
        j = int(parts[1])
        assert parts[2] == "1" * (j + 2) + "0"
        assert parts[4] == "はい"
        file_rows.append((m, j))

    # Recompute exact qualifying (m, j) with m <= 40000, j >= 1
    expected_rows: list[tuple[int, int]] = []
    for m in range(5, 40001, 4):
        h = (m + 1) // 2
        x3 = 3 * h + 1
        t = (x3 & -x3).bit_length() - 1
        if t != 2:
            continue
        w = x3 // 4
        X = (m + 2 + w) // 2
        j = 0
        while X % 4 == 2:
            X = (m + 2 + X // 2) // 2
            j += 1
        if j >= 1 and X % 2 == 1:
            expected_rows.append((m, j))
    assert file_rows == expected_rows, f"Coverage mismatch: {len(file_rows)} vs {len(expected_rows)}"

    with ProcessPoolExecutor(max_workers=10) as ex:
        dp_res = list(ex.map(check_one_k64, file_rows))

    assert all(ok for _, _, ok in dp_res), f"Failed: {[x for x in dp_res if not x[2]][:5]}"
    j_counts = Counter(j for _, j, _ in dp_res)
    expected_j = {1: 312, 2: 78, 3: 20, 4: 5, 5: 1}
    assert dict(j_counts) == expected_j, f"j_counts={dict(j_counts)}"
    # Also check j=0 (m=17) matches K64 theorem statement
    assert check_one_k64((17, 0))[2] is True

    print(f"\n[1] PR #446 data/k64_chain.txt 全 416 ケース (m ≤ 40000, j=1..5) 直接 DP 独立検証（漸化式 R 不使用）:")
    print(f"    対象 m 網羅性・全件直接 DP 一致: {len(dp_res)}/{len(expected_rows)} (不一致 0 件)")
    for j in sorted(j_counts):
        print(f"    j={j} (型 {'1'*(j+2)}0): {j_counts[j]}/{j_counts[j]} 直接 DP 一致")

    # 2. Independent recomputation of PR #449 data/lean_coverage.txt (1 <= m <= 1,000,000)
    MMAX = 1_000_000
    stat_tot: Counter[str] = Counter()
    stat_cov: Counter[str] = Counter()
    by_thm: Counter[str] = Counter()

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
                    if m >= 9:
                        w = x3 // 4
                        X = (m + 2 + w) // 2
                        jj = 0
                        while (X & 3) == 2:
                            X = (m + 2 + (X >> 1)) >> 1
                            jj += 1
                        if jj >= 1 and (X & 1) == 1:
                            by_thm["K64"] += 1
                            cov = True
                elif t >= 4:
                    w = x3 >> t
                    if (w & 3) == 3:
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
        ["git", "show", "origin/claude-1/lean-k64:data/lean_coverage.txt"],
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
        "K64": 10416,
        "K10a": 15624,
        "K15": 10415,
        "K38": 3297,
    }
    assert dict(by_thm) == expected_thm, f"Counts mismatch: {dict(by_thm)} vs {expected_thm}"

    # Exact asymptotic natural density with K64 included:
    # v=1 (1/4): K9 (2/3) + K12a (1/8) + K64 (j>=1: (1/4)*(1/6)=1/24) + K15 (1/24) = 2/3 + 1/8 + 1/12 = 7/8 = 87.50%!
    d_even = Fraction(2, 3)
    d_v1 = Fraction(1, 4) * Fraction(7, 8)
    d_v3 = Fraction(1, 16) * Fraction(1, 2)
    d_v5_k29 = Fraction(1, 48) * Fraction(1, 2)
    d_v5_k38 = Fraction(1, 6) * Fraction(1, 48) - Fraction(1, 3) * Fraction(1, 1920)
    d_tot = d_even + d_v1 + d_v3 + d_v5_k29 + d_v5_k38

    print(f"\n[2] PR #449 (1 ≤ m ≤ 1,000,000 Lean 被覆率) 独立 Python 再計算:")
    print(f"    合計: {tot_c:,} / {tot_n:,} ({100.0 * tot_c / tot_n:.2f}%) — data/lean_coverage.txt 全行完全一致")
    print(f"    v2(m+1)=1: {stat_cov['1']:,}/{stat_tot['1']:,} ({100.0*stat_cov['1']/stat_tot['1']:.2f}%) [理論漸近 7/8 = 87.5000%]")
    print(f"    各定理件数 (10/10 完全一致): {dict(by_thm)}")
    print(f"    理論漸近自然密度 = {d_tot} = {float(d_tot)*100:.6f}% (実測 m≤10^6: {100.0*tot_c/tot_n:.4f}%)")

    elapsed = time.perf_counter() - t0
    print(f"\nALL CHECKS PASSED in {elapsed:.2f}s.")


if __name__ == "__main__":
    main()
