"""
gemini2_verify_k7_periods.py — PR #384/#386/#389（予想 K7 の m ≤ 2000 周期性・前周期検証）および
PR #391/#393/#395（Lean 4 定理 K6・K9 の直接 DP クロスチェック）の独立 Python 3 検証スクリプト。

何を計算するか:
  1. PROBLEM.md の直接定義（漸化式 R / K8 を使わない）に基づく O(N) 厳密 DP を実装し、
     素朴な O(N*m^2) 2 次元ミニマックス DP と 2 <= m <= 30, 0 <= n <= 300 で全局面一致を確認する。
  2. PR #384/#386/#389 の全 4 データ組（計 798 個の m：2..200 全数 199 個＋201..2000 の v2(m+1) 奇数 599 個）について、
     - m の網羅性（欠落・失敗なし）と periods / check_dp ファイル間の全行一致
     - 直接 DP による n <= t + 4L + 10（前周期あり 10 個は t + 6L + 10）までの周期性 S(n) = S(n+L)
     - t = 0 時の境界 n = 0（S(0) = S(L)）の明示確認（k7_check_dp.js は n >= t+1 のみ検査）
     - t > 0 時の前周期最小性 S(t) != S(t+L)
     - L の全真約数 d | L に対する最小周期性（反例 n の存在確認；k7_check_dp.js 未検査）
     - t = 0 時の間隔語（第 6 列）の厳密一致
     を独立検証する。
  3. PR #389 ノート記載の前周期あり 10 個（55, 95, 481, 801, 929, 991, 1185, 1463, 1503, 1953）について、
     v, u, 前周期の間隔, 周期の語, t, L, 剰余類・個数（31 個中 5 個等）の全主張を独立検証する。
  4. PR #391/#393/#395 の定理 K6・K9 の同値主張を、5 <= m <= 200（v2(m+1) = 1）の直接 DP 結果と照合する。

実行方法（リポジトリのルートで）:
  uv run python code/gemini2_verify_k7_periods.py > data/gemini2_verify_k7_periods.txt
"""

from __future__ import annotations

import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor


def v2(x: int) -> int:
    c = 0
    while (x & 1) == 0:
        x >>= 1
        c += 1
    return c


def proper_divisors(n: int) -> list[int]:
    divs: list[int] = []
    d = 1
    while d * d <= n:
        if n % d == 0:
            if d < n:
                divs.append(d)
            q = n // d
            if q != d and q < n:
                divs.append(q)
        d += 1
    divs.sort()
    return divs


def naive_problem_dp(m: int, nmax: int) -> list[list[bool]]:
    """PROBLEM.md の定義そのままの素朴な O(N*m^2) 2 次元 DP。
    P[r][p] = True ⇔ 残り r 個・直前の手 p が P 局面（先手負け）。
    """
    P = [[False] * (m + 1) for _ in range(nmax + 1)]
    for p in range(m + 1):
        P[0][p] = True
    for r in range(1, nmax + 1):
        lim = m if r >= m else r
        for p in range(m + 1):
            win = False
            for k in range(1, lim + 1):
                if k == p:
                    continue
                if P[r - k][k]:
                    win = True
                    break
            P[r][p] = not win
    return P


def fast_exact_dp_rows(m: int, nmax: int) -> list[int]:
    """PROBLEM.md の定義のみに基づく O(N) 厳密 DP（漸化式 R / K8 不使用）。

    A_r = {k in [1, min(m, r)] : (r - k, k) is P} とすると (r, p) is P ⇔ A_r ⊆ {p}。
    よって各行 r の型は:
      typ[r] = -1  : A_r = ∅（すべての p で P、特に開始局面 (r, 0) が P）
      typ[r] = k   : A_r = {k}（p = k のみ P）
      typ[r] = -2  : |A_r| >= 2（どの p でも N）
    任意の 2 つの ALL-P 行の間隔は >= m + 1 であるため、区間 [r - m, r - 1] にある
    ALL-P 行は直近の last_all 高々 1 個のみ。SINGLE-P 行 s (typ[s] = k) は
    単一の将来行 r = s + k のみに k を寄与する。
    """
    typ = [0] * (nmax + 1)
    typ[0] = -1
    # single_cnt[r]: SINGLE-P 行からのヒット回数（2 以上で飽和）
    # single_val[r]: 最初のヒット k
    single_cnt = [0] * (nmax + 1)
    single_val = [0] * (nmax + 1)
    last_all = 0
    for r in range(1, nmax + 1):
        cnt = single_cnt[r]
        val = single_val[r]
        d = r - last_all
        if d <= m:
            cnt += 1
            if cnt == 1:
                val = d
        if cnt == 0:
            typ[r] = -1
            last_all = r
        elif cnt == 1:
            typ[r] = val
            nxt = r + val
            if nxt <= nmax:
                c2 = single_cnt[nxt] + 1
                single_cnt[nxt] = c2
                if c2 == 1:
                    single_val[nxt] = val
        else:
            typ[r] = -2
    return typ


def check_one_m(task: tuple[int, int, int, int, str]) -> dict:
    m, t, L, nmax_file, word_col = task
    nmax = t + (6 if t > 0 else 4) * L + 10
    if nmax < nmax_file:
        nmax = nmax_file
    typ = fast_exact_dp_rows(m, nmax)
    S = [x == -1 for x in typ]

    # 1. Periodicity for n >= t + 1
    per_ok = True
    first_per_fail = -1
    for n in range(t + 1, nmax - L + 1):
        if S[n] != S[n + L]:
            per_ok = False
            first_per_fail = n
            break

    # 2. Boundary n = 0 when t == 0
    zero_ok = True
    if t == 0:
        zero_ok = (S[0] == S[L])

    # 3. Minimality of t when t > 0
    t_min_ok = True
    if t > 0:
        t_min_ok = (S[t] != S[t + L])

    # 4. Minimality of L (no proper divisor d | L is a period on [t+1, nmax-d])
    l_min_ok = True
    bad_div = -1
    for d in proper_divisors(L):
        is_per_d = True
        for n in range(t + 1, nmax - d + 1):
            if S[n] != S[n + d]:
                is_per_d = False
                break
        if is_per_d:
            l_min_ok = False
            bad_div = d
            break

    # 5. Gap sequence & gap word
    starts = [n for n in range(nmax + 1) if S[n]]
    gaps = [starts[i] - starts[i - 1] - (m + 1) for i in range(1, len(starts))]
    gaps_binary = all(g in (0, 1) for g in gaps)
    word_ok = True
    pre_gaps = ""
    per_word = ""
    if t == 0 and word_col:
        # Period in gaps: number of starts in (0, L]
        p_cnt = sum(1 for x in starts if 0 < x <= L)
        computed_w = "".join(str(g) for g in gaps[:p_cnt])
        word_ok = (computed_w == word_col)
        per_word = computed_w
    elif t > 0:
        p_cnt = sum(1 for x in starts if t < x <= t + L)
        w = "".join(str(g) for g in gaps)
        j0 = 0
        while j0 < len(w) - 2 * p_cnt:
            if all(w[j0 + i] == w[j0 + i + p_cnt] for i in range(len(w) - j0 - p_cnt)):
                break
            j0 += 1
        pre_gaps = w[:j0]
        per_word = w[j0 : j0 + p_cnt]

    return {
        "m": m,
        "t": t,
        "L": L,
        "nmax": nmax,
        "per_ok": per_ok,
        "first_per_fail": first_per_fail,
        "zero_ok": zero_ok,
        "t_min_ok": t_min_ok,
        "l_min_ok": l_min_ok,
        "bad_div": bad_div,
        "gaps_binary": gaps_binary,
        "word_ok": word_ok,
        "pre_gaps": pre_gaps,
        "per_word": per_word,
    }


def git_show(ref: str, path: str) -> str:
    return subprocess.check_output(
        ["git", "show", f"{ref}:{path}"], text=True, encoding="utf-8"
    )


def parse_periods_file(text: str) -> dict[int, tuple[int, int, int, str]]:
    """m -> (v2, t, L, word_col)"""
    res: dict[int, tuple[int, int, int, str]] = {}
    for line in text.splitlines():
        if not line.startswith("m="):
            continue
        parts = [p.strip() for p in line.split("|")]
        m = int(parts[0][2:])
        v = int(parts[1])
        t_str, L_str = parts[4].split(",")
        t = int(t_str.strip())
        L = int(L_str.strip())
        word_col = parts[5] if len(parts) > 5 else ""
        res[m] = (v, t, L, word_col)
    return res


def parse_check_dp_file(text: str) -> dict[int, tuple[int, int, int, str]]:
    """m -> (t, L, nmax, result)"""
    res: dict[int, tuple[int, int, int, str]] = {}
    for line in text.splitlines():
        if "|" not in line:
            continue
        parts = [p.strip() for p in line.split("|")]
        if not parts[0].isdigit():
            continue
        m = int(parts[0])
        t = int(parts[1])
        L = int(parts[2])
        nmax = int(parts[3])
        status = parts[4]
        res[m] = (t, L, nmax, status)
    return res


def main() -> None:
    t0 = time.perf_counter()
    print("# gemini-2 独立 Python 3 検証：予想 K7（PR #384/#386/#389）および定理 K6/K9（PR #391/#393/#395）")

    # 1. Cross-check fast_exact_dp_rows against naive_problem_dp
    naive_mismatches = 0
    naive_positions = 0
    for m in range(2, 31):
        nmax = 300
        P = naive_problem_dp(m, nmax)
        typ = fast_exact_dp_rows(m, nmax)
        for r in range(nmax + 1):
            for p in range(m + 1):
                fast_p = (typ[r] == -1) or (typ[r] == p)
                naive_positions += 1
                if fast_p != P[r][p]:
                    naive_mismatches += 1
    print(f"\n[1] O(N) 厳密 DP vs PROBLEM.md 素朴 O(N*m^2) DP 照合 (2<=m<=30, 0<=r<=300):")
    print(f"    positions = {naive_positions:,}, mismatches = {naive_mismatches}")
    assert naive_mismatches == 0

    # 2. Load and verify all 4 datasets from PR #384, #386, #389
    datasets = [
        (
            "PR #384 (2..200 all)",
            "origin/claude-1/k7-periods",
            "data/block_periods_m2-200.txt",
            "data/k7_check_dp_2-200.txt",
            list(range(2, 201)),
        ),
        (
            "PR #384 (201..400 odd v2)",
            "origin/claude-1/k7-periods",
            "data/k7_periods_201-400.txt",
            "data/k7_check_dp.txt",
            [m for m in range(201, 401) if v2(m + 1) % 2 == 1],
        ),
        (
            "PR #386 (401..1000 odd v2)",
            "origin/claude-1/k7-periods-1000",
            "data/k7_periods_401-1000.txt",
            "data/k7_check_dp_401-1000.txt",
            [m for m in range(401, 1001) if v2(m + 1) % 2 == 1],
        ),
        (
            "PR #389 (1001..2000 odd v2)",
            "origin/claude-1/k7-periods-2000",
            "data/k7_periods_1001-2000.txt",
            "data/k7_check_dp_1001-2000.txt",
            [m for m in range(1001, 2001) if v2(m + 1) % 2 == 1],
        ),
    ]

    print("\n[2] PR #384 / #386 / #389 全データ組の独立直接 DP 検証:")
    all_preperiod: list[dict] = []
    total_cases = 0
    total_rows_computed = 0

    with ProcessPoolExecutor(max_workers=10) as ex:
        for label, ref, p_path, c_path, expected_ms in datasets:
            p_map = parse_periods_file(git_show(ref, p_path))
            c_map = parse_check_dp_file(git_show(ref, c_path))
            assert sorted(p_map.keys()) == expected_ms, f"{label}: periods m-set mismatch"
            assert sorted(c_map.keys()) == expected_ms, f"{label}: check_dp m-set mismatch"

            tasks = []
            file_sync_ok = 0
            for m in expected_ms:
                v_file, t_p, L_p, word_col = p_map[m]
                t_c, L_c, nmax_c, status_c = c_map[m]
                assert v_file == v2(m + 1), f"v2 mismatch at m={m}"
                assert (t_p, L_p) == (t_c, L_c), f"(t,L) mismatch at m={m}"
                assert nmax_c == t_p + 4 * L_p + 10, f"nmax mismatch at m={m}"
                assert status_c == "一致", f"status != 一致 at m={m}"
                file_sync_ok += 1
                # In block_periods_m2-200.txt, even v2(m+1) also appear; word_col for t==0 may be "" for m<=200? Let's pass it if binary
                w_arg = word_col if (word_col and set(word_col) <= {"0", "1"}) else ""
                tasks.append((m, t_p, L_p, nmax_c, w_arg))

            results = list(ex.map(check_one_m, tasks))
            per_ok = sum(r["per_ok"] for r in results)
            zero_ok = sum(r["zero_ok"] for r in results)
            t_min_ok = sum(r["t_min_ok"] for r in results)
            l_min_ok = sum(r["l_min_ok"] for r in results)
            gaps_bin = sum(r["gaps_binary"] for r in results)
            word_ok = sum(r["word_ok"] for r in results)
            pre = [r for r in results if r["t"] > 0]
            all_preperiod.extend(pre)
            total_cases += len(results)
            total_rows_computed += sum(r["nmax"] + 1 for r in results)

            max_L_row = max(results, key=lambda r: r["L"])
            print(f"  - {label}: {len(results)}/{len(expected_ms)} m 網羅, ファイル照合 {file_sync_ok}/{len(results)}")
            print(
                f"      周期性={per_ok}/{len(results)}, n=0境界(t=0)={zero_ok}/{len(results)}, "
                f"前周期最小性={t_min_ok}/{len(results)}, 最小周期性={l_min_ok}/{len(results)}, "
                f"間隔∈{{0,1}}={gaps_bin}/{len(results)}, 間隔語一致={word_ok}/{len(results)}"
            )
            print(
                f"      最大周期 m={max_L_row['m']} (L={max_L_row['L']}), 前周期あり: {[r['m'] for r in pre]}"
            )
            assert per_ok == len(results)
            assert zero_ok == len(results)
            assert t_min_ok == len(results)
            assert l_min_ok == len(results)
            assert gaps_bin == len(results)
            assert word_ok == len(results)

    print(f"  合計: {total_cases} ケース（延べ {total_rows_computed:,} 行の直接 DP）すべて完全一致・最小性確認済み")

    # 3. Verify PR #389 preperiod table & observations
    expected_table = [
        (55, 3, 7, "11", "010", 58, 169),
        (95, 5, 3, "110", "011", 194, 290),
        (481, 1, 241, "11011", "110", 1932, 1448),
        (801, 1, 401, "1110", "11101", 2409, 4014),
        (929, 1, 465, "1110", "110111", 2793, 5585),
        (991, 5, 31, "11", "0100", 994, 3969),
        (1185, 1, 593, "110", "11011", 2374, 5934),
        (1463, 3, 183, "11", "011110", 1466, 8788),
        (1503, 5, 47, "110110", "011", 7524, 4514),
        (1953, 1, 977, "110", "11011", 3910, 9774),
    ]
    print("\n[3] 前周期のある 10 個（m <= 2000）の表・観察事項（PR #389）の独立検証:")
    assert [r["m"] for r in all_preperiod] == [row[0] for row in expected_table]
    for r, exp in zip(all_preperiod, expected_table):
        m, ev, eu, epre, eper, et, eL = exp
        v = v2(m + 1)
        u = (m + 1) >> v
        assert (v, u, r["pre_gaps"], r["per_word"], r["t"], r["L"]) == (
            ev,
            eu,
            epre,
            eper,
            et,
            eL,
        ), f"Mismatch for m={m}: got {(v, u, r['pre_gaps'], r['per_word'], r['t'], r['L'])}"
        print(
            f"  m={m:4d} | v={v} | u={u:3d} | pre={r['pre_gaps']:6s} | per={r['per_word']:6s} "
            f"| t={r['t']:4d} | L={r['L']:4d} | t_min=OK | L_min=OK"
        )

    # Check PR #389 arithmetic & residue observations
    v1_pre = [row for row in expected_table if row[1] == 1]
    assert all(row[2] % 32 == 17 for row in v1_pre)
    for m, v, u, *_ in v1_pre:
        h = (m + 1) // 2
        assert v2(3 * h + 1) == 2 and ((3 * h + 1) // 4) % 8 == 5
    u_mod128 = [row[2] % 128 for row in v1_pre]
    assert u_mod128 == [113, 17, 81, 81, 81], f"u_mod128={u_mod128}"
    class_v1_u17 = [
        m for m in range(2, 2001) if v2(m + 1) == 1 and ((m + 1) // 2) % 32 == 17
    ]
    assert len(class_v1_u17) == 31, f"len={len(class_v1_u17)}"
    assert all(row[2] % 16 == 7 for row in expected_table if row[1] == 3)
    assert all(row[2] % 4 == 3 for row in expected_table if row[1] == 5)
    assert (expected_table[6][3], expected_table[6][4]) == (
        expected_table[9][3],
        expected_table[9][4],
    )  # 1185 vs 1953
    # Verify t formulas in PR #389 notes
    assert 58 == 55 + 3
    assert 194 == 2 * (95 + 2)
    assert 1932 == 4 * (481 + 2)
    assert 2409 == 3 * (801 + 2)
    assert 2793 == 3 * (929 + 2)
    assert 994 == 991 + 3
    assert 2374 == 2 * (1185 + 2)
    assert 1466 == 1463 + 3
    assert 7524 == 5 * (1503 + 2) - 1
    assert 3910 == 2 * (1953 + 2)
    print(f"  全 10 件の表・式・剰余類観察一致: v=1 u≡17(mod 32) は m<=2000 で {len(class_v1_u17)} 個中 5 個, u mod 128 = {u_mod128}")

    # 4. Cross-check K6 and K9 against direct DP for 5 <= m <= 200 (m % 4 == 1)
    k6_checked = 0
    k9_checked = 0
    for m in range(5, 201, 4):
        h = (m + 1) // 2
        odd_v2 = (v2(3 * h + 1) % 2 == 1)
        nmax = 4 * (2 * m + 3) + 10
        typ = fast_exact_dp_rows(m, nmax)
        is_alt = all(
            (typ[n] == -1) == (n % (2 * m + 3) in (0, m + 2))
            for n in range(nmax + 1)
        )
        assert is_alt == odd_v2, f"K9 mismatch at m={m}"
        if not odd_v2:
            assert typ[2 * m + 3] != -1, f"K9_nec mismatch at m={m}"
        k9_checked += 1
        if m % 8 == 5:
            assert is_alt is True
            k6_checked += 1
    print(f"\n[4] 定理 K6 / K9 の直接 DP クロスチェック (5 <= m <= 200, m ≡ 1 mod 4):")
    print(f"    K6 (m ≡ 5 mod 8): {k6_checked}/{k6_checked} 一致")
    print(f"    K9 (v2(m+1)=1, 同値および K9_nec (2m+3,0)∈N): {k9_checked}/{k9_checked} 一致")

    elapsed = time.perf_counter() - t0
    print(f"\nALL CHECKS PASSED in {elapsed:.2f}s.")


if __name__ == "__main__":
    main()
