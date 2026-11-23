"""
gemini-2 による独立な Python 全探索ソルバーを用いた命題 K10a（g₁ の式）・系 K10b の数値検証。

何を計算するか:
1. PROBLEM.md の正確な定義のみから書いた全探索 DP (solve_count_dp) で、
   v2(m+1) = 3（m + 1 = 8u、u は奇数）、u = 1, 3, 5, ..., 25（m = 7, 23, ..., 199、計 13 個の m）について
   0 <= r <= 3*(m+2) の全局面を計算。
2. すべての対象 m で次を検証:
   - 命題 K10a: g_0 = m + 2、かつ g_1 = m + 2 ⇔ v2(9u + 1) が偶数。
   - 証明中間主張: u in S_1 ⇔ 2u not in S_1 ⇔ 4u in S_1 ⇔ v2(9u + 1) が偶数。
   - 系 K10b: v2(9u + 1) が偶数（特に u ≡ 3 (mod 8)）のとき g_0 = g_1 = m + 2 かつ (2m + 3, 0) が N。

実行方法:
  python code/gemini2_verify_k10_g1.py
結果を標準出力と data/gemini2_verify_k10_g1.txt に保存する。
"""

from __future__ import annotations

import time
from pathlib import Path


def v2(x: int) -> int:
    assert x > 0
    return (x & -x).bit_length() - 1


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


def main() -> None:
    t0 = time.perf_counter()
    lines: list[str] = []
    lines.append("=== gemini-2 独立検証: 命題 K10a（g₁ の式）・系 K10b ===")

    us = list(range(1, 26, 2))
    k10a_errs: list[str] = []
    k10b_errs: list[str] = []
    total_states = 0

    for u in us:
        m = 8 * u - 1
        max_r = 3 * (m + 2)
        tab = solve_count_dp(m, max_r)
        total_states += (max_r + 1) * (m + 1)

        a_rows = [r for r in range(max_r + 1) if all(tab[r])]
        g0 = a_rows[1] - a_rows[0]
        g1 = a_rows[2] - a_rows[1]
        v = v2(9 * u + 1)
        v_even = (v % 2 == 0)

        a1 = a_rows[1]
        u_in_s1 = tab[a1 + u][u]
        u2_in_s1 = tab[a1 + 2 * u][2 * u]
        u4_in_s1 = tab[a1 + 4 * u][4 * u]

        if g0 != m + 2 or (g1 == m + 2) != v_even:
            k10a_errs.append(f"u={u}, m={m}: g0={g0}, g1={g1}, v2(9u+1)={v}")
        if not (u_in_s1 == v_even and u2_in_s1 == (not v_even) and u4_in_s1 == v_even):
            k10a_errs.append(f"chain fail at u={u}: {u_in_s1}, {u2_in_s1}, {u4_in_s1}")

        if v_even:
            if g1 != m + 2 or tab[2 * m + 3][0] is not False:
                k10b_errs.append(f"K10b fail at u={u}, m={m}")
        if u % 8 == 3:
            if v != 2 or tab[2 * m + 3][0] is not False:
                k10b_errs.append(f"K10b (u≡3 mod 8) fail at u={u}, m={m}")

    elapsed = time.perf_counter() - t0
    lines.append(f"検証範囲: m + 1 = 8u, u = 1, 3, ..., 25 (m = 7..199, 13 個), 0 <= r <= 3(m+2) (計 {total_states:,} 局面)")
    lines.append(f"  - 命題 K10a（および鎖 u, 2u, 4u）の反例: {len(k10a_errs)} 件")
    lines.append(f"  - 系 K10b の反例: {len(k10b_errs)} 件")
    lines.append(f"所要時間: {elapsed:.2f} 秒")

    text = "\n".join(lines) + "\n"
    print(text, end="")
    out = Path(__file__).resolve().parent.parent / "data" / "gemini2_verify_k10_g1.txt"
    out.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
