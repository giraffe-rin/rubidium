"""
gemini2_verify_k61fix_k62fix_leandp.py — PR #368 修正（命題 K61）・PR #370 修正（命題 K62）・PR #379/#381（Lean DP 勝敗表 3 言語照合）の Python 独立検証

何を計算するか:
  1. PR #379・PR #381（Lean DP 勝敗表との 3 言語独立照合: Lean 4 ↔ JavaScript ↔ Python 3）:
     - PROBLEM.md のゲーム定義（1 <= k <= min(m, r), k != p）を Python 3 で直接 DP 実装し、
       全 m = 1..100, r = 0..3000（計 15,455,150 局面）について、
       各 m の P 局面数・チェックサム Σ (r(m+1) + p + 1)^2 mod (10^9 + 7)・開始 P 局面先頭 20 個を計算する。
     - PR #381 の data/lean_table_summary.txt（100 行）と全 100/100 行を直接照合する（m <= 30, r <= 2000 の 990,495 局面も包含）。
  2. PR #368 修正（命題 K61: b + 3r != 0, inner != 0, u < N ガード付き）:
     - 小さい族の全列挙 enum:5:12:31:511（5 <= N <= 12, 3 <= q <= 31 奇数, 1 <= s <= 511 奇数, r = ±1）を
       Python 独立実装で並列検証し、予測できた全族で実際と完全一致すること・反例 (5,1,83,5)・(5,1,243,5) が
       u >= N ガードで正しく停止することを確認する。
  3. PR #370 修正（命題 K62: 一般奇数 r の有理数規則 + ガード付き）:
     - 小さい族の全列挙 enum:5:12:31:15:255（5 <= N <= 12, 3 <= q <= 31, |r| <= 15 奇数, 1 <= s <= 255 奇数）を
       Python 独立実装（Fraction）で並列検証し、有理数規則で予測できた全族で実際と完全一致することを確認する。

実行方法（リポジトリのルートで）:
  uv run python code/gemini2_verify_k61fix_k62fix_leandp.py > data/gemini2_verify_k61fix_k62fix_leandp.txt
"""
from __future__ import annotations

import concurrent.futures
import subprocess
import sys
import time
from fractions import Fraction

sys.setrecursionlimit(200000)


def v2(x: int) -> int:
    if x == 0:
        return 10**9
    if x < 0:
        x = -x
    return (x & -x).bit_length() - 1


def v2_frac(x: Fraction) -> int:
    assert x.denominator % 2 == 1
    return v2(x.numerator)


# ---------------------------------------------------------------------------
# 1. Exact PROBLEM.md DP for m = 1..100, r = 0..3000 (3-way check with Lean & JS)
# ---------------------------------------------------------------------------
def dp_table_summary_one(args: tuple[int, int]) -> tuple[int, int, int, list[int]]:
    """
    Exact PROBLEM.md DP:
      uniq[r] = -1 if U(r) = ∅ (all p in 0..m are P-positions),
                 d if U(r) = {d} (only p = d is a P-position),
                 0 if |U(r)| >= 2 (no p is a P-position).
    """
    m, rmax = args
    MOD = 1000000007
    uniq = [0] * (rmax + 1)
    uniq[0] = -1
    for r in range(1, rmax + 1):
        lim = m if r >= m else r
        found = -1
        two = False
        for k in range(1, lim + 1):
            u = uniq[r - k]
            if u == -1 or u == k:
                if found == -1:
                    found = k
                else:
                    two = True
                    break
        if two:
            uniq[r] = 0
        elif found == -1:
            uniq[r] = -1
        else:
            uniq[r] = found

    cnt = 0
    s_mod = 0
    starts: list[int] = []
    stride = m + 1
    for r in range(0, rmax + 1):
        u = uniq[r]
        base = r * stride + 1
        if u == -1:
            cnt += stride
            for p in range(0, stride):
                x = base + p
                s_mod = (s_mod + x * x) % MOD
            if r >= 1 and len(starts) < 20:
                starts.append(r)
        elif u > 0:
            cnt += 1
            x = base + u
            s_mod = (s_mod + x * x) % MOD
    return (m, cnt, s_mod, starts)


# ---------------------------------------------------------------------------
# 2. Independent K61 / K62 predictor with guards (b+3r!=0, inner!=0, u<N)
# ---------------------------------------------------------------------------
def gaps_lazy_big(m: int, J: int) -> list[int]:
    h = (m + 1) // 2
    memo: dict[tuple[int, int], bool] = {}
    gm: dict[int, int] = {}

    def gap(j: int) -> int:
        res = gm.get(j)
        if res is not None:
            return res
        r = m + 2 if S(j, h) else m + 1
        gm[j] = r
        return r

    def S(j: int, d: int) -> bool:
        key = (j, d)
        res = memo.get(key)
        if res is not None:
            return res
        if j == 0:
            r = (v2(d) & 1) == 0
        else:
            if (d & 1) == 0 and S(j, d >> 1):
                r = False
            else:
                g = gap(j - 1)
                sm = g + d
                if (sm & 1) == 0 and (sm >> 1) <= m and S(j - 1, sm >> 1):
                    r = False
                elif g == m + 2 and d == h - 1:
                    r = False
                else:
                    r = True
        memo[key] = r
        return r

    return [gap(j) - m - 1 for j in range(J)]


def check_k62_one(q: int, r: int, s: int, N: int) -> tuple[str, bool]:
    """Return (status, matched). status in {'ok', 'mismatch', 'skip', 'guard:b+3r=0', 'guard:inner=0', 'guard:u>=N', 'guard:b_even'}."""
    X = 1 << N
    a = (s * X - r) // q
    beta0 = 3 * r + q
    if beta0 == 0 or v2(beta0) >= N:
        return ("skip", True)
    v = v2(beta0)
    if (v - 1) % 2 != 0:
        return ("skip", True)
    m = 3 * a - 2
    M = 3 * a
    h = (m + 1) // 2
    imax = 4 * N + 20

    def h_in(i: int) -> tuple[bool | None, str]:
        c = Fraction(1, 1)
        K = v
        steps = v - 1
        b = Fraction(beta0 >> v, 1)
        for j in range(1, i + 1):
            e_exp = N - K
            term = c * s * (1 << e_exp) if e_exp >= 0 else c * s / (1 << (-e_exp))
            dd = (b * a - term) / r
            if dd.denominator == 1:
                d = dd.numerator
                if d == h - 1:
                    return (steps % 2 != 0, "")
                if (M + d) // 2 > m:
                    return (steps % 2 == 0, "")
            gam = v2_frac(c)
            co = c / (1 << gam)
            x = b + 3 * r
            if x == 0:
                return (None, "guard:b+3r=0")
            t = v2_frac(x)
            b2 = x / (1 << t)
            E = K + t
            steps += 1
            if E < N + gam:
                if j == i:
                    ib = ((t - 1) % 2 == 0)
                    return (ib if steps % 2 == 0 else (not ib), "")
                steps += t - 1
                K = E
                b = b2
                continue
            nk1 = N + gam - K - 1
            cs = co * s / r
            if E == N + gam:
                inner = b2 + cs * q
                if inner == 0:
                    return (None, "guard:inner=0")
                u = v2_frac(inner)
                if u >= N:
                    return (None, "guard:u>=N")
                if j == i:
                    ib = ((nk1 + u) % 2 == 0)
                    return (ib if steps % 2 == 0 else (not ib), "")
                steps += nk1 + u
                c = cs
                K = u
                b = inner / (1 << u)
                continue
            o = E - N - gam
            if j == i:
                ib = (nk1 % 2 == 0)
                return (ib if steps % 2 == 0 else (not ib), "")
            steps += nk1
            c = cs
            K = 0
            b = b2 * (1 << o) + cs * q
            if v2_frac(b) != 0:
                return (None, "guard:b_even")
        return (None, "guard:limit")

    pred: int | None = None
    for i in range(1, imax + 1):
        val, why = h_in(i)
        if val is None:
            return (why, True)
        if val is False:
            pred = i
            break

    if pred is not None:
        g = gaps_lazy_big(m, pred + 1)
        matched = (0 in g and g.index(0) == pred)
        return ("ok" if matched else "mismatch", matched)
    else:
        g = gaps_lazy_big(m, imax + 1)
        matched = (0 not in g)
        return ("ok" if matched else "mismatch", matched)


def worker_k61_N(N: int) -> tuple[int, int, dict[str, int]]:
    ok_cnt = mis_cnt = 0
    guards: dict[str, int] = {}
    X = 1 << N
    for q in range(3, 32, 2):
        for s in range(1, 512, 2):
            for r in (1, -1):
                if (s * X - r) % q != 0:
                    continue
                a = (s * X - r) // q
                if a <= 0 or a % 2 == 0:
                    continue
                st, _ = check_k62_one(q, r, s, N)
                if st == "ok":
                    ok_cnt += 1
                elif st == "mismatch":
                    mis_cnt += 1
                elif st.startswith("guard:"):
                    guards[st] = guards.get(st, 0) + 1
    return (ok_cnt, mis_cnt, guards)


def worker_k62_N(N: int) -> tuple[int, int, dict[str, int]]:
    ok_cnt = mis_cnt = 0
    guards: dict[str, int] = {}
    X = 1 << N
    rs = [r for r in range(-15, 16, 2)]
    for q in range(3, 32, 2):
        for r in rs:
            for s in range(1, 256, 2):
                if (s * X - r) % q != 0:
                    continue
                a = (s * X - r) // q
                if a <= 0 or a % 2 == 0:
                    continue
                st, _ = check_k62_one(q, r, s, N)
                if st == "ok":
                    ok_cnt += 1
                elif st == "mismatch":
                    mis_cnt += 1
                elif st.startswith("guard:"):
                    guards[st] = guards.get(st, 0) + 1
    return (ok_cnt, mis_cnt, guards)


def main() -> None:
    t0 = time.perf_counter()
    print("# gemini-2 独立検証: PR #368 修正（K61）・PR #370 修正（K62）・PR #379/#381（Lean DP 3 言語照合）")
    print("# 実行コマンド: uv run python code/gemini2_verify_k61fix_k62fix_leandp.py > data/gemini2_verify_k61fix_k62fix_leandp.txt")
    print()

    # 1. PR #379 & #381: 3-way DP cross-check (m = 1..100, r = 0..3000)
    t1 = time.perf_counter()
    with concurrent.futures.ProcessPoolExecutor(max_workers=10) as ex:
        dp_rows = list(ex.map(dp_table_summary_one, [(m, 3000) for m in range(1, 101)]))
    total_positions = sum((m + 1) * 3001 for m in range(1, 101))

    # Compare directly against origin/claude-1/lean-tables-100:data/lean_table_summary.txt
    lean_ref_lines = subprocess.check_output(
        ["git", "show", "origin/claude-1/lean-tables-100:data/lean_table_summary.txt"]
    ).decode("utf-8").splitlines()
    py_lines = [f"{m} {cnt} {s_mod} [{', '.join(str(x) for x in starts)}]" for m, cnt, s_mod, starts in dp_rows]
    dp_mismatches = sum(1 for a_ln, b_ln in zip(py_lines, lean_ref_lines) if a_ln != b_ln)
    if len(py_lines) != len(lean_ref_lines):
        dp_mismatches += abs(len(py_lines) - len(lean_ref_lines))
    print(f"## 1. PR #379・#381（Lean 4 ↔ JavaScript ↔ Python 3 独立 DP 3 言語照合: m = 1..100, r = 0..3000）[{time.perf_counter() - t1:.2f}s]")
    print(f"- 総照合局面数: {total_positions:,} 局面 (m = 1..100)")
    print(f"- data/lean_table_summary.txt (100 行) との行単位完全一致: {100 - dp_mismatches}/100, mismatches = {dp_mismatches}")
    print(f"  代表行 m=1:   {py_lines[0]}")
    print(f"  代表行 m=30:  {py_lines[29]}")
    print(f"  代表行 m=100: {py_lines[99]}")
    print()

    # 2. PR #368 fix: K61 enum:5:12:31:511 + counterexamples
    t2 = time.perf_counter()
    st_ce1, _ = check_k62_one(5, 1, 83, 5)
    st_ce2, _ = check_k62_one(5, 1, 243, 5)
    with concurrent.futures.ProcessPoolExecutor(max_workers=10) as ex:
        res61 = list(ex.map(worker_k61_N, list(range(5, 13))))
    ok61 = sum(x[0] for x in res61)
    mis61 = sum(x[1] for x in res61)
    g61: dict[str, int] = {}
    for _, _, gd in res61:
        for k, v in gd.items():
            g61[k] = g61.get(k, 0) + v
    print(f"## 2. PR #368 修正（命題 K61: enum:5:12:31:511 全列挙 + 反例確認）[{time.perf_counter() - t2:.2f}s]")
    print(f"- 反例ガード確認: (5,1,83,5) -> {st_ce1}, (5,1,243,5) -> {st_ce2}")
    print(f"- enum:5:12:31:511 判定内一致: {ok61}/{ok61 + mis61} (mismatches = {mis61}), ガード停止 = {dict(sorted(g61.items()))}")
    print()

    # 3. PR #370 fix: K62 enum:5:12:31:15:255
    t3 = time.perf_counter()
    with concurrent.futures.ProcessPoolExecutor(max_workers=10) as ex:
        res62 = list(ex.map(worker_k62_N, list(range(5, 13))))
    ok62 = sum(x[0] for x in res62)
    mis62 = sum(x[1] for x in res62)
    g62: dict[str, int] = {}
    for _, _, gd in res62:
        for k, v in gd.items():
            g62[k] = g62.get(k, 0) + v
    print(f"## 3. PR #370 修正（命題 K62: enum:5:12:31:15:255 全列挙、一般奇数 r）[{time.perf_counter() - t3:.2f}s]")
    print(f"- enum:5:12:31:15:255 判定内一致: {ok62}/{ok62 + mis62} (mismatches = {mis62}), ガード停止 = {dict(sorted(g62.items()))}")

    total_errors = dp_mismatches + mis61 + mis62 + (0 if (st_ce1 == "guard:u>=N" and st_ce2 == "guard:u>=N") else 1)
    print()
    print(f"## 総合検証結果: total_errors = {total_errors}, total_elapsed = {time.perf_counter() - t0:.2f}s")
    if total_errors != 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
