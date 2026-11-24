"""
gemini2_verify_k63.py — PR #414（予想 K63：v2(m+1) = 3、v2(9u+1) = 1、v2(11u+1) ≥ 4 偶数、u ≤ 20000）
および PR #415（claims/K6, K9, K10a, K13 追加）の独立 Python 3 検証スクリプト。

何を計算するか:
  1. PROBLEM.md の定義のみに基づく O(N) 厳密 DP（漸化式 R / K8 不使用）を用いて、
     data/k63_check_dp.txt（u ≤ 1200 全 52 ケース）および data/k63_alt3.txt（u ≤ 20000 全 835 ケース、
     m ≤ 159,999）のすべてを直接 DP で独立検証する。
     - 各 u について、まず n ≤ 6(2m+3) まで直接 DP で交互型（n mod (2m+3) ∈ {0, m+2}）か判定。
     - data/k63_alt3.txt が「いいえ」なのに 6(2m+3) までに崩れない場合は、崩れるか 30(2m+3) に達するまで延長。
     - 網羅性（対象 u 集合の完全一致）、11 類すべての件数・交互型件数、data/k63_check_dp.txt の
       最初に外れる n の完全一致を確認する。
  2. ノート追記の 2 つの観察も直接 DP で独立検証する：
     - (1) u = 77 (m = 615, Y = 53) でブロック 1 の (b + 4Y, 4Y) が N（他のブロックでは P）。
     - (2) e ≥ 3, Y ≡ 3 (mod 4) の全 105 ケース（u ≤ 20000）について、最初に交互から外れる n が
       2(2m+3) + (m+1) = 5m + 7 かどうかを全件調査する。

実行方法（リポジトリのルートで）:
  uv run python code/gemini2_verify_k63.py > data/gemini2_verify_k63.txt
"""

from __future__ import annotations

import subprocess
import time
from collections import Counter
from concurrent.futures import ProcessPoolExecutor


def v2(x: int) -> int:
    c = 0
    while (x & 1) == 0:
        x >>= 1
        c += 1
    return c


def fast_exact_dp_rows(m: int, nmax: int) -> list[int]:
    """PROBLEM.md の定義のみに基づく O(N) 厳密 DP（漸化式 R / K8 不使用）。"""
    typ = [0] * (nmax + 1)
    typ[0] = -1
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


def check_one_u(task: tuple[int, int, int, int, bool]) -> dict:
    u, m, e11, ymod8, r_alt = task
    L = 2 * m + 3
    # First check up to 6*L (same bound as k63_check_dp.js)
    nmax = 6 * L
    typ = fast_exact_dp_rows(m, nmax)
    fail = -1
    for n in range(1, nmax + 1):
        rem = n % L
        if (typ[n] == -1) != (rem == 0 or rem == m + 2):
            fail = n
            break
    # If R says non-alternating but it didn't fail within 6*L, extend search up to 30*L
    extended_fail = fail
    if not r_alt and fail < 0:
        nmax2 = 30 * L
        typ2 = fast_exact_dp_rows(m, nmax2)
        for n in range(nmax + 1, nmax2 + 1):
            rem = n % L
            if (typ2[n] == -1) != (rem == 0 or rem == m + 2):
                extended_fail = n
                break
    return {
        "u": u,
        "m": m,
        "e11": e11,
        "ymod4": ymod8 % 4,
        "r_alt": r_alt,
        "dp_fail_6L": fail,
        "dp_fail_ext": extended_fail,
        "dp_alt_ext": extended_fail < 0,
    }


def git_show(ref: str, path: str) -> str:
    return subprocess.check_output(
        ["git", "show", f"{ref}:{path}"], text=True, encoding="utf-8"
    )


def main() -> None:
    t0 = time.perf_counter()
    print("# gemini-2 独立 Python 3 検証：予想 K63（PR #414、u ≤ 20000 全件直接 DP）")

    # Parse data/k63_alt3.txt
    alt3_text = git_show("origin/claude-1/k63-alt3", "data/k63_alt3.txt")
    alt3_rows: list[tuple[int, int, int, int, bool]] = []
    for line in alt3_text.splitlines():
        if "|" not in line:
            continue
        parts = [p.strip() for p in line.split("|")]
        if not parts[0].isdigit():
            continue
        u = int(parts[0])
        m = int(parts[1])
        e11 = int(parts[2])
        ymod8 = int(parts[3])
        r_alt = parts[6] == "はい"
        alt3_rows.append((u, m, e11, ymod8, r_alt))

    # Verify exact coverage of u <= 20000
    expected_us = []
    for u in range(1, 20001, 2):
        e9 = v2(9 * u + 1)
        e11 = v2(11 * u + 1)
        if e9 == 1 and e11 >= 4 and e11 % 2 == 0:
            expected_us.append(u)
    assert [r[0] for r in alt3_rows] == expected_us, "Coverage mismatch in k63_alt3.txt"
    for u, m, e11, ymod8, _ in alt3_rows:
        assert m == 8 * u - 1
        assert e11 == v2(11 * u + 1)
        assert ymod8 == ((11 * u + 1) >> e11) % 8

    # Parse data/k63_check_dp.txt (u <= 1200)
    dp_text = git_show("origin/claude-1/k63-alt3", "data/k63_check_dp.txt")
    dp_file_map: dict[int, tuple[bool, int]] = {}
    for line in dp_text.splitlines():
        if "|" not in line:
            continue
        parts = [p.strip() for p in line.split("|")]
        if not parts[0].isdigit():
            continue
        u = int(parts[0])
        is_alt = parts[4] == "はい"
        fail_n = -1 if parts[5] == "-" else int(parts[5])
        dp_file_map[u] = (is_alt, fail_n)
    expected_dp_us = [u for u in expected_us if u <= 1200]
    assert sorted(dp_file_map.keys()) == expected_dp_us

    # Run independent direct PROBLEM.md DP on ALL 835 cases in parallel!
    with ProcessPoolExecutor(max_workers=10) as ex:
        results = list(ex.map(check_one_u, alt3_rows))

    # Compare u <= 1200 against k63_check_dp.txt
    dp1200_match = 0
    for r in results:
        if r["u"] <= 1200:
            exp_alt, exp_fail = dp_file_map[r["u"]]
            assert (r["dp_fail_6L"] < 0) == exp_alt and r["dp_fail_6L"] == exp_fail, (
                f"k63_check_dp mismatch at u={r['u']}: got {r['dp_fail_6L']}, expected {exp_fail}"
            )
            dp1200_match += 1

    # Compare all 835 cases against data/k63_alt3.txt (R)
    disagreements = [r for r in results if r["r_alt"] != r["dp_alt_ext"]]
    late_fails = [r for r in results if (not r["r_alt"]) and r["dp_fail_6L"] < 0 and r["dp_fail_ext"] > 0]
    print(f"\n[1] 全 835 ケース（u ≤ 20000, m ≤ 159,999）の直接 DP 独立検証（漸化式 R 不使用）:")
    print(f"    対象 u 網羅性 = {len(results)}/{len(expected_us)} 一致")
    print(f"    u ≤ 1200 (data/k63_check_dp.txt) 判定＋初外れ n 一致 = {dp1200_match}/{len(expected_dp_us)}")
    print(f"    u ≤ 20000 (data/k63_alt3.txt, R) vs 直接 DP 不一致 = {len(disagreements)} 件")
    if late_fails:
        print(f"    ※ 6(2m+3) 超〜30(2m+3) で初めて外れた非交互型 = {len(late_fails)} 件: "
              + ", ".join(f"u={r['u']}(n={r['dp_fail_ext']})" for r in late_fails[:10]))
    assert len(disagreements) == 0, f"Disagreements: {disagreements[:5]}"

    # Verify summary table counts
    stat_tot: Counter[tuple[int, int]] = Counter()
    stat_alt: Counter[tuple[int, int]] = Counter()
    for r in results:
        key = (r["e11"], r["ymod4"])
        stat_tot[key] += 1
        if r["dp_alt_ext"]:
            stat_alt[key] += 1

    expected_summary = {
        (4, 1): (313, 313),
        (4, 3): (312, 116),
        (6, 1): (79, 12),
        (6, 3): (78, 0),
        (8, 1): (19, 3),
        (8, 3): (20, 0),
        (10, 1): (5, 1),
        (10, 3): (5, 0),
        (12, 1): (1, 0),
        (12, 3): (2, 0),
        (14, 1): (1, 0),
    }
    print("\n[2] 11 類の集計表照合（直接 DP 結果）:")
    for key in sorted(expected_summary):
        got = (stat_tot[key], stat_alt[key])
        assert got == expected_summary[key], f"Summary mismatch at {key}: {got} vs {expected_summary[key]}"
        print(f"    v2(11u+1)={key[0]:2d}, Y≡{key[1]} (mod 4): {got[1]:3d}/{got[0]:3d} 交互型 (OK)")

    # Verify addendum observations
    # (a) u = 77 (m = 615, Y = 53): check even blocks i = 0..7 (a_i = i*(2m+3)) for (a_i + 4Y, 4Y)
    m77 = 8 * 77 - 1
    Y77 = (11 * 77 + 1) // 16
    assert m77 == 615 and Y77 == 53
    typ77 = fast_exact_dp_rows(m77, 10 * (2 * m77 + 3))
    d4y = 4 * Y77
    even_blk_4y = [(i, typ77[i * (2 * m77 + 3) + d4y] in (-1, d4y)) for i in range(8)]
    assert even_blk_4y[1][1] is False and all(even_blk_4y[i][1] is True for i in (0, 2, 3, 4, 5, 6, 7))
    print(f"\n[3] ノート追記の観察検証:")
    print(f"    u=77 (m=615, 4Y={d4y}): 偶数ブロック i=0..7 (a_i=i(2m+3)) の (a_i+4Y, 4Y)∈P = {[p for _, p in even_blk_4y]} (i=1 のみ N を確認)")

    # (b) Check first failing n for ALL 105 cases of (2): e >= 3, Y ≡ 3 (mod 4)
    part2 = [r for r in results if r["e11"] >= 6 and r["ymod4"] == 3]
    assert len(part2) == 105
    fail_5m7 = sum(1 for r in part2 if r["dp_fail_ext"] == 5 * r["m"] + 7)
    other_part2 = [r for r in part2 if r["dp_fail_ext"] != 5 * r["m"] + 7]
    print(f"    (2) e≥3, Y≡3 (mod 4) 全 {len(part2)} 件の初外れ n:")
    print(f"        n = 2(2m+3)+(m+1) = 5m+7: {fail_5m7}/{len(part2)} 件, それ以外: {len(other_part2)} 件")
    if other_part2:
        for r in other_part2[:10]:
            print(f"        例外: u={r['u']}, m={r['m']}, e11={r['e11']}, fail={r['dp_fail_ext']} (5m+7={5*r['m']+7})")

    elapsed = time.perf_counter() - t0
    print(f"\nALL CHECKS PASSED in {elapsed:.2f}s.")


if __name__ == "__main__":
    main()
