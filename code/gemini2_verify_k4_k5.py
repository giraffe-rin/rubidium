"""
gemini-2 による独立な Python 全探索ソルバーを用いた定理 K4・K5 および主張 Q(j) の数値検証。

何を計算するか:
1. PROBLEM.md の正確な定義のみから書いたボトムアップ全探索 DP (solve_direct_dp) で
   2 <= m <= 60, 0 <= r <= 3000 の全局面 (r, p) を計算（あわせて小範囲で検算例を確認）。
2. 定理 K4（開始局面 (n, 0) が P ⇔ (m+1)|n が成り立つ ⇔ v2(m+1) が偶数）を全範囲で検証。
3. 定理 K5（v2(m+1) が奇数なら (n, 0) が P となる最小の n >= 1 は m+2）を全範囲で検証。
4. K4 証明内の帰納的主張 Q(j)（m が奇数かつ v2(m+1) が偶数のとき、全ブロックで
   g_j = m+1 かつ 1 <= d <= m, v2(d) <= s* で d in S_j ⇔ v2(d) が偶数）も直接検証。

実行方法:
  python code/gemini2_verify_k4_k5.py
結果を標準出力と data/gemini2_verify_k4_k5.txt に保存する。
"""

from __future__ import annotations

import time
from pathlib import Path


def v2(x: int) -> int:
    assert x > 0
    return (x & -x).bit_length() - 1


def solve_count_dp(m: int, max_r: int) -> list[list[bool]]:
    """PROBLEM.md の定義通りの全探索 DP。is_p[r][p] == True ⇔ (r, p) が P 局面。"""
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
    lines.append("=== gemini-2 独立検証: 定理 K4・K5・主張 Q(j) ===")

    # PROBLEM.md 検算例
    t1 = solve_count_dp(1, 50)
    assert all(not t1[n][0] for n in range(1, 51))
    t2 = solve_count_dp(2, 10)
    assert t2[3][0] is True
    lines.append("PROBLEM.md 検算例 (m=1 全先手必勝, m=2 n=3 後手必勝): OK")

    max_m = 60
    max_r = 3000
    k4_errs: list[str] = []
    k5_errs: list[str] = []
    q_errs: list[str] = []
    even_v2_ms = 0
    odd_v2_ms = 0
    odd_m_even_v2_ms = 0
    total_states = 0

    for m in range(2, max_m + 1):
        tab = solve_count_dp(m, max_r)
        total_states += (max_r + 1) * (m + 1)
        v = v2(m + 1)
        v_even = (v % 2 == 0)

        # (1) すべての 1 <= n <= max_r で (n, 0) が P ⇔ (m+1) | n か
        is_multiple_type = all(tab[n][0] == (n % (m + 1) == 0) for n in range(1, max_r + 1))

        if v_even:
            even_v2_ms += 1
            if not is_multiple_type:
                k4_errs.append(f"K4(⇐) fail at m={m}")
        else:
            odd_v2_ms += 1
            if is_multiple_type:
                k4_errs.append(f"K4(⇒) fail at m={m}")
            # K5: 最小の n >= 1 で (n, 0) が P となるのは m + 2
            first_p = next((n for n in range(1, max_r + 1) if tab[n][0]), None)
            if first_p != m + 2:
                k5_errs.append(f"K5 fail at m={m}: first_p={first_p}, exp={m+2}")

        # Q(j) の直接検証（m が奇数かつ v2(m+1) が偶数の場合）
        if m % 2 == 1 and v_even:
            odd_m_even_v2_ms += 1
            s_star = v - 1
            a_rows = [r for r in range(max_r + 1) if all(tab[r])]
            for j in range(len(a_rows)):
                aj = a_rows[j]
                if aj != j * (m + 1):
                    q_errs.append(f"Q1 fail at m={m}, j={j}: a_j={aj}")
                for d in range(1, m + 1):
                    if aj + d > max_r:
                        break
                    if v2(d) <= s_star:
                        in_sj = tab[aj + d][d] and all(
                            (tab[aj + d][p] == (p == d)) for p in range(m + 1)
                        )
                        exp = (v2(d) % 2 == 0)
                        if in_sj != exp:
                            q_errs.append(f"Q2 fail at m={m}, j={j}, d={d}")

    elapsed = time.perf_counter() - t0
    lines.append(f"検証範囲: 2 <= m <= {max_m}, 0 <= r <= {max_r} (計 {total_states:,} 局面)")
    lines.append(f"  - v2(m+1) 偶数の m: {even_v2_ms} 個 (うち奇数 m: {odd_m_even_v2_ms} 個)")
    lines.append(f"  - v2(m+1) 奇数の m: {odd_v2_ms} 個")
    lines.append(f"  - 定理 K4 の反例: {len(k4_errs)} 件")
    lines.append(f"  - 定理 K5 の反例: {len(k5_errs)} 件")
    lines.append(f"  - 主張 Q(j) の反例: {len(q_errs)} 件")
    lines.append(f"所要時間: {elapsed:.2f} 秒")
    if k4_errs or k5_errs or q_errs:
        lines.append(f"[!] errors: K4={k4_errs[:5]}, K5={k5_errs[:5]}, Q={q_errs[:5]}")

    text = "\n".join(lines) + "\n"
    print(text, end="")
    out = Path(__file__).resolve().parent.parent / "data" / "gemini2_verify_k4_k5.txt"
    out.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
