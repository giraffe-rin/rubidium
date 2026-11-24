"""
gemini-2 による独立な全探索ソルバーおよび構造主張 K1・K2・K3・K8 の検証スクリプト。

何を計算するか:
1. PROBLEM.md の正確な定義のみから書いた 3 種類の独立な全探索ソルバー
   - solve_memo_rec: 定義通りのトップダウン再帰（メモ化）
   - solve_direct_dp: 定義通りのボトムアップ全探索 DP（各 (r, p) で全合法手 k を探索）
   - solve_count_dp: 各行 r の P 行き先の個数を数えるボトムアップ DP
2. PROBLEM.md「検算用の小さな例」の確認 (m=1 全 n, m=2 n=3)。
3. 3 実装の一致確認 (小範囲で全 3 実装、全検証範囲 2 <= m <= 60, 0 <= r <= 3000 で direct_dp と count_dp を完全照合)。
4. 1 <= m <= 60, 0 <= r <= 3000 の全局面 (r, p) に対して:
   - 補題 1・K1 (行の型 A / S(t) / E と系 1.1)
   - K3 (最初のブロック 1 <= r <= m)
   2 <= m <= 60, 0 <= r <= 3000 の全局面 (r, p) に対して:
   - K2 (ブロックの形: ギャップ m+1 or m+2、距離 1..m の行、距離 m+1 の行)
   - K8 (ブロック漸化式 R による全局面表の完全再構成と全探索結果との全局面一致)

実行方法:
  python code/gemini2_verify_structure.py
  (または uv run python code/gemini2_verify_structure.py)
結果を標準出力と data/gemini2_verify_structure.txt に出力する。
"""

from __future__ import annotations

import os
import sys
import time
from functools import lru_cache
from pathlib import Path


def v2(x: int) -> int:
    """正の整数 x を割り切る 2 の最大べきの指数。"""
    assert x > 0
    return (x & -x).bit_length() - 1


def solve_memo_rec(m: int, max_r: int) -> list[list[bool]]:
    """
    実装 1: PROBLEM.md の定義そのままのトップダウン再帰（メモ化）。
    戻り値: is_p[r][p] == True ⇔ 局面 (r, p) が P 局面（後手必勝）。
    """
    sys.setrecursionlimit(max(10000, max_r + 1000))

    @lru_cache(maxsize=None)
    def is_p(r: int, p: int) -> bool:
        limit = m if r >= m else r
        for k in range(1, limit + 1):
            if k == p:
                continue
            if is_p(r - k, k):
                return False
        return True

    table = [[is_p(r, p) for p in range(m + 1)] for r in range(max_r + 1)]
    is_p.cache_clear()
    return table


def solve_direct_dp(m: int, max_r: int) -> list[list[bool]]:
    """
    実装 2: 定義通りのボトムアップ全探索 DP。
    各局面 (r, p) について、すべての合法手 1 <= k <= min(m, r), k != p を直接調べる。
    戻り値: is_p[r][p] == True ⇔ 局面 (r, p) が P 局面。
    """
    is_p: list[list[bool]] = [[False] * (m + 1) for _ in range(max_r + 1)]
    # r = 0: 合法手がないので全 p で P
    row0 = is_p[0]
    for p in range(m + 1):
        row0[p] = True

    for r in range(1, max_r + 1):
        limit = m if r >= m else r
        row = is_p[r]
        for p in range(m + 1):
            # 合法手 k のうち (r - k, k) が P になるものが 1 つでもあれば N (False)
            found_p = False
            for k in range(1, limit + 1):
                if k != p and is_p[r - k][k]:
                    found_p = True
                    break
            row[p] = not found_p
    return is_p


def solve_count_dp(m: int, max_r: int) -> list[list[bool]]:
    """
    実装 3: 各行 r で (r - k, k) が P になる k の個数を数えて (r, p) の勝敗を決める DP。
    K1 の結論（集合サイズ）を前提にせず、合法手集合 M = {1..min(m,r)} \\ {p} の中で
    P 局面へ行く手の個数が 0 かどうかを直接計算する。
    """
    is_p: list[list[bool]] = [[False] * (m + 1) for _ in range(max_r + 1)]
    is_p[0] = [True] * (m + 1)

    for r in range(1, max_r + 1):
        limit = m if r >= m else r
        # 各 k in 1..limit について (r - k, k) が P か
        p_dest = [False] * (limit + 1)
        total_p = 0
        for k in range(1, limit + 1):
            if is_p[r - k][k]:
                p_dest[k] = True
                total_p += 1
        row = is_p[r]
        for p in range(m + 1):
            legal_p_moves = total_p - (1 if (1 <= p <= limit and p_dest[p]) else 0)
            row[p] = (legal_p_moves == 0)
    return is_p


def build_table_from_k8(m: int, max_r: int) -> tuple[list[list[bool]], list[int], list[set[int]], list[int]]:
    """
    K8（ブロック漸化式 R）および K2 の形だけから全局面表 (0 <= r <= max_r, 0 <= p <= m) を生成する。
    戻り値: (is_p_table, a_list, S_list, g_list)
      a_list: max_r 以下に現れる A 行の位置 [a_0, a_1, ...]
      S_list: 各ブロックの S_j
      g_list: 各ブロックのギャップ g_j
    """
    assert m >= 2
    is_odd = (m % 2 == 1)
    h = (m + 1) // 2 if is_odd else -1

    is_p: list[list[bool]] = [[False] * (m + 1) for _ in range(max_r + 1)]
    a_list: list[int] = []
    S_list: list[set[int]] = []
    g_list: list[int] = []

    a = 0
    j = 0
    while a <= max_r:
        a_list.append(a)
        # 行 a は A 行
        is_p[a] = [True] * (m + 1)

        # ブロック j の S_j を規則 (i)〜(iii) で計算
        S_j: set[int] = set()
        for d in range(1, m + 1):
            blocked = False
            # (i) d が偶数で d/2 in S_j
            if d % 2 == 0 and (d // 2) in S_j:
                blocked = True
            # (ii) j >= 1, g_{j-1} + d が偶数, e = (g_{j-1} + d)//2 <= m, e in S_{j-1}
            if not blocked and j >= 1:
                g_prev = g_list[j - 1]
                if (g_prev + d) % 2 == 0:
                    e = (g_prev + d) // 2
                    if e <= m and e in S_list[j - 1]:
                        blocked = True
            # (iii) j >= 1, g_{j-1} == m + 2, d == h - 1
            if not blocked and j >= 1:
                if g_list[j - 1] == m + 2 and is_odd and d == h - 1:
                    blocked = True

            if not blocked:
                S_j.add(d)

        g_j = (m + 2) if (is_odd and h in S_j) else (m + 1)
        S_list.append(S_j)
        g_list.append(g_j)

        # 距離 1..m の行を埋める
        for d in range(1, m + 1):
            r = a + d
            if r > max_r:
                break
            if d in S_j:
                is_p[r][d] = True
        # 距離 m+1 の行（g_j == m+2 のときのみ）
        if g_j == m + 2 and a + m + 1 <= max_r:
            is_p[a + m + 1][h] = True

        a += g_j
        j += 1

    return is_p, a_list, S_list, g_list


def verify_all() -> list[str]:
    lines: list[str] = []
    t0 = time.perf_counter()

    lines.append("=== gemini-2 独立全探索ソルバーおよび K1・K2・K3・K8 検証レポート ===")
    lines.append("")

    # 1. PROBLEM.md 検算用の小さな例
    lines.append("[1] PROBLEM.md 検算用の小さな例")
    for name, solver in [
        ("solve_memo_rec", solve_memo_rec),
        ("solve_direct_dp", solve_direct_dp),
        ("solve_count_dp", solve_count_dp),
    ]:
        # m = 1: すべての n >= 1 で先手必勝 (すなわち (n, 0) は P でない)
        t_m1 = solver(1, 200)
        assert t_m1[0][0] is True and t_m1[0][1] is True, f"{name}: m=1, r=0 failed"
        for n in range(1, 201):
            assert t_m1[n][0] is False, f"{name}: m=1, n={n} should be N"
            assert t_m1[n][1] is True, f"{name}: m=1, (n={n}, p=1) should be P"
        # m = 2, n = 3: 後手必勝 (すなわち (3, 0) は P)
        t_m2 = solver(2, 20)
        assert t_m2[3][0] is True, f"{name}: m=2, n=3 should be P"
        assert t_m2[1][0] is False and t_m2[2][0] is False, f"{name}: m=2, n=1,2 should be N"
        lines.append(f"  - {name}: m=1 (1<=n<=200 全先手必勝), m=2 n=3 (後手必勝) -> OK")

    # 2. 3 実装の一致確認 (小範囲)
    lines.append("")
    lines.append("[2] 3 実装の完全一致確認 (1 <= m <= 12, 0 <= r <= 200)")
    small_states = 0
    for m in range(1, 13):
        t1 = solve_memo_rec(m, 200)
        t2 = solve_direct_dp(m, 200)
        t3 = solve_count_dp(m, 200)
        assert t1 == t2 == t3, f"Mismatch among 3 solvers at m={m}"
        small_states += 201 * (m + 1)
    lines.append(f"  - 1 <= m <= 12, 0 <= r <= 200 全 {small_states:,} 局面で 3 実装が完全一致 -> OK")

    # 3. 本検証: 1 <= m <= 60, 0 <= r <= 3000
    max_m = 60
    max_r = 3000
    lines.append("")
    lines.append(f"[3] 本検証 (1 <= m <= {max_m}, 0 <= r <= {max_r}、K2・K8 は 2 <= m <= {max_m})")

    total_states_all = 0
    total_states_m2 = 0
    k1_failures: list[str] = []
    k2_failures: list[str] = []
    k3_failures: list[str] = []
    k8_failures: list[str] = []
    solver_mismatches: list[str] = []

    k1_counts = {"A": 0, "S": 0, "E": 0}
    k2_blocks_checked = 0
    k2_gap_counts = {"m+1": 0, "m+2": 0}

    for m in range(1, max_m + 1):
        t_direct = solve_direct_dp(m, max_r)
        t_count = solve_count_dp(m, max_r)
        if t_direct != t_count:
            solver_mismatches.append(f"m={m}")
            continue

        table = t_direct
        n_states = (max_r + 1) * (m + 1)
        total_states_all += n_states
        if m >= 2:
            total_states_m2 += n_states

        # --- K1 & 補題 1 & 系 1.1 の検証 (m >= 1, 0 <= r <= max_r) ---
        a_rows: list[int] = []
        row_p_sets: list[list[int]] = []
        for r in range(max_r + 1):
            p_set = [p for p in range(m + 1) if table[r][p]]
            row_p_sets.append(p_set)

            # T(r) を直接計算
            limit = m if r >= m else r
            t_set = [k for k in range(1, limit + 1) if table[r - k][k]]

            # 補題 1 の直接検証: (r, p) is P ⇔ T(r) ⊆ {p}
            for p in range(m + 1):
                expected_p = all(k == p for k in t_set)
                if table[r][p] != expected_p:
                    k1_failures.append(f"Lemma1 fail at m={m}, r={r}, p={p}")

            # K1: |L(r)| in {m+1, 1, 0} かつ T(r) との対応
            if len(t_set) == 0:
                if len(p_set) != m + 1:
                    k1_failures.append(f"K1(A) fail at m={m}, r={r}: L={p_set}")
                k1_counts["A"] += 1
                a_rows.append(r)
            elif len(t_set) == 1:
                if p_set != t_set:
                    k1_failures.append(f"K1(S) fail at m={m}, r={r}: T={t_set}, L={p_set}")
                k1_counts["S"] += 1
            else:
                if len(p_set) != 0:
                    k1_failures.append(f"K1(E) fail at m={m}, r={r}: T={t_set}, L={p_set}")
                k1_counts["E"] += 1

            # 系 1.1: r is A-row ⇔ (r, 0) is P
            is_a = (len(p_set) == m + 1)
            if is_a != table[r][0]:
                k1_failures.append(f"Cor1.1 fail at m={m}, r={r}")

        # --- K3 の検証 (1 <= r <= m, m >= 1) ---
        for r in range(1, m + 1):
            v2_even = (v2(r) % 2 == 0)
            for p in range(m + 1):
                expected = (p == r and v2_even)
                if table[r][p] != expected:
                    k3_failures.append(f"K3 fail at m={m}, r={r}, p={p}: got {table[r][p]}, exp {expected}")

        # --- K2 & K8 の検証 (2 <= m <= max_m) ---
        if m >= 2:
            is_odd = (m % 2 == 1)
            h = (m + 1) // 2 if is_odd else -1

            if not a_rows or a_rows[0] != 0:
                k2_failures.append(f"K2 a_0 != 0 at m={m}")
            else:
                # 完結したブロック
                for j in range(len(a_rows) - 1):
                    aj = a_rows[j]
                    gj = a_rows[j + 1] - aj
                    k2_blocks_checked += 1
                    if gj == m + 1:
                        k2_gap_counts["m+1"] += 1
                    elif gj == m + 2:
                        k2_gap_counts["m+2"] += 1
                    else:
                        k2_failures.append(f"K2(a) gap={gj} at m={m}, j={j}, a_j={aj}")
                        continue

                    # (b) 距離 1 <= d <= m
                    for d in range(1, m + 1):
                        ps = row_p_sets[aj + d]
                        if ps not in ([], [d]):
                            k2_failures.append(f"K2(b) fail at m={m}, j={j}, d={d}: L={ps}")

                    # (c) 距離 m+1
                    if gj == m + 2:
                        if not is_odd:
                            k2_failures.append(f"K2(c) even m={m} has gap m+2 at j={j}")
                        elif row_p_sets[aj + m + 1] != [h]:
                            k2_failures.append(f"K2(c) fail at m={m}, j={j}: L={row_p_sets[aj + m + 1]}")

                # 末尾の不完全ブロックも検査
                a_last = a_rows[-1]
                rem = max_r - a_last
                if rem >= m + 2:
                    k2_failures.append(f"K2 trailing gap > m+2 at m={m}, a_last={a_last}, max_r={max_r}")
                for d in range(1, min(m, rem) + 1):
                    ps = row_p_sets[a_last + d]
                    if ps not in ([], [d]):
                        k2_failures.append(f"K2(b) trailing fail at m={m}, d={d}: L={ps}")
                if rem == m + 1:
                    if not is_odd or row_p_sets[a_last + m + 1] != [h]:
                        k2_failures.append(
                            f"K2(c) trailing fail at m={m}, a_last={a_last}: L={row_p_sets[a_last + m + 1]}"
                        )

            # K8: 漸化式 R だけで作った全局面表と全探索表を全 (r, p) で完全比較
            r_table, r_a_rows, _, _ = build_table_from_k8(m, max_r)
            if r_a_rows != a_rows:
                k8_failures.append(f"K8 A-rows mismatch at m={m}")
            if r_table != table:
                # 最初の食い違い位置を記録
                found = False
                for r in range(max_r + 1):
                    for p in range(m + 1):
                        if r_table[r][p] != table[r][p]:
                            k8_failures.append(
                                f"K8 table mismatch at m={m}, r={r}, p={p}: R={r_table[r][p]}, DP={table[r][p]}"
                            )
                            found = True
                            break
                    if found:
                        break

    elapsed = time.perf_counter() - t0
    lines.append(f"  - direct_dp と count_dp の不一致: {len(solver_mismatches)} 件")
    lines.append(f"  - 検査した全局面数 (1 <= m <= {max_m}, 0 <= r <= {max_r}): {total_states_all:,}")
    lines.append(f"  - 検査した全局面数 (2 <= m <= {max_m}, 0 <= r <= {max_r}): {total_states_m2:,}")
    lines.append(f"  - 補題 1・K1・系 1.1 の反例: {len(k1_failures)} 件 (A行={k1_counts['A']:,}, S行={k1_counts['S']:,}, E行={k1_counts['E']:,})")
    lines.append(f"  - K2 の反例: {len(k2_failures)} 件 (完結ブロック数={k2_blocks_checked:,}, gap=m+1: {k2_gap_counts['m+1']:,}, gap=m+2: {k2_gap_counts['m+2']:,})")
    lines.append(f"  - K3 の反例 (1 <= r <= m <= {max_m}): {len(k3_failures)} 件")
    lines.append(f"  - K8 (漸化式 R による全局面表の完全一致) の反例: {len(k8_failures)} 件")
    lines.append(f"  - 所要時間: {elapsed:.2f} 秒")

    for label, errs in [
        ("solver_mismatches", solver_mismatches),
        ("K1", k1_failures),
        ("K2", k2_failures),
        ("K3", k3_failures),
        ("K8", k8_failures),
    ]:
        if errs:
            lines.append(f"  [!] {label} の失敗詳細 (先頭 10 件): {errs[:10]}")

    # 4. 境界ケース m = 1, 2, 3 の具体的な確認サマリ
    lines.append("")
    lines.append("[4] 小さい m (m = 1, 2, 3) の先頭 15 行の P 集合 (独立全探索の結果)")
    for m in (1, 2, 3):
        tab = solve_direct_dp(m, 15)
        summary = []
        for r in range(16):
            ps = [p for p in range(m + 1) if tab[r][p]]
            if len(ps) == m + 1:
                summary.append(f"{r}:A")
            elif len(ps) == 1:
                summary.append(f"{r}:S({ps[0]})")
            else:
                summary.append(f"{r}:E")
        lines.append(f"  m={m}: " + ", ".join(summary))

    return lines


def main() -> None:
    lines = verify_all()
    text = "\n".join(lines) + "\n"
    print(text, end="")

    repo_root = Path(__file__).resolve().parent.parent
    out_path = repo_root / "data" / "gemini2_verify_structure.txt"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(text, encoding="utf-8")
    print(f"\n出力保存先: {out_path}")


if __name__ == "__main__":
    main()
