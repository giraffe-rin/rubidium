"""
gemini-2 による独立な Python 全探索ソルバーを用いた定理 K6 および補足（先手の必勝手）の数値検証。

何を計算するか:
1. PROBLEM.md の正確な定義のみから書いた全探索 DP (solve_count_dp) で、
   m ≡ 5 (mod 8), 5 <= m <= 101 (計 13 個の m), 0 <= r <= 3000 の全局面 (r, p) を計算。
2. 定理 K6: すべての 1 <= n <= 3000 で (n, 0) が P ⇔ n ≡ 0 または m+2 (mod 2m+3) を検証。
3. 証明内の帰納的主張 P(j)（j 偶数なら全奇数 d in S_j かつ g_j = m+2、j 奇数なら g_j = m+1）を検証。
4. PR #10 補足「先手の必勝手」の検証:
   - 0 < c < m+2 に対し k = c を提案しているが、c = m+1 のとき k = m+1 > m となり合法手でないことを確認。
   - 正しい手（c = m+1 のとき k = h = (m+1)/2、0 < c <= m のとき k = c、m+2 < c < 2m+3 のとき k = c - (m+2)）が
     すべての N 開始局面で合法かつ P 局面へ遷移することを検証。

実行方法:
  python code/gemini2_verify_k6.py
結果を標準出力と data/gemini2_verify_k6.txt に保存する。
"""

from __future__ import annotations

import time
from pathlib import Path


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
    lines.append("=== gemini-2 独立検証: 定理 K6・主張 P(j)・補足（先手の必勝手） ===")

    # PROBLEM.md 検算例
    t1 = solve_count_dp(1, 50)
    assert all(not t1[n][0] for n in range(1, 51))
    t2 = solve_count_dp(2, 10)
    assert t2[3][0] is True
    lines.append("PROBLEM.md 検算例: OK")

    ms = [m for m in range(5, 102) if m % 8 == 5]
    max_r = 3000

    k6_errs: list[str] = []
    p_errs: list[str] = []
    supp_illegal_count = 0
    supp_first_counterexample: str | None = None
    fixed_strategy_errs: list[str] = []
    total_states = 0

    for m in ms:
        tab = solve_count_dp(m, max_r)
        total_states += (max_r + 1) * (m + 1)
        h = (m + 1) // 2
        mod = 2 * m + 3

        # 定理 K6 の検証
        for n in range(1, max_r + 1):
            c = n % mod
            exp_p = (c == 0 or c == m + 2)
            if tab[n][0] != exp_p:
                k6_errs.append(f"m={m}, n={n}")

            if not exp_p:
                # PR #10 補足そのままの戦略を検証
                if 0 < c < m + 2:
                    k_supp = c
                else:
                    k_supp = c - (m + 2)
                legal = (1 <= k_supp <= min(m, n))
                if not legal or not tab[n - k_supp][k_supp]:
                    supp_illegal_count += 1
                    if supp_first_counterexample is None:
                        supp_first_counterexample = (
                            f"m={m}, n={n}, c={c}: 補足の指示 k={k_supp} は k > m={m} のため非合法手"
                        )

                # 修正版戦略の検証
                if 0 < c <= m:
                    k_fix = c
                elif c == m + 1:
                    k_fix = h
                else:
                    k_fix = c - (m + 2)
                if not (1 <= k_fix <= min(m, n)) or not tab[n - k_fix][k_fix]:
                    fixed_strategy_errs.append(f"m={m}, n={n}, k_fix={k_fix}")

        # 主張 P(j) の検証
        a_rows = [r for r in range(max_r + 1) if all(tab[r])]
        for j in range(len(a_rows) - 1):
            aj = a_rows[j]
            gj = a_rows[j + 1] - aj
            if j % 2 == 0:
                if gj != m + 2:
                    p_errs.append(f"P(j) gap fail at m={m}, j={j}: g={gj}")
                for d in range(1, m + 1, 2):
                    if not (tab[aj + d][d] and all(tab[aj + d][p] == (p == d) for p in range(m + 1))):
                        p_errs.append(f"P(j) odd d fail at m={m}, j={j}, d={d}")
            else:
                if gj != m + 1:
                    p_errs.append(f"P(j) gap fail at m={m}, j={j}: g={gj}")

    elapsed = time.perf_counter() - t0
    lines.append(f"検証範囲: m ≡ 5 (mod 8), 5 <= m <= 101 ({len(ms)} 個の m), 0 <= r <= {max_r} (計 {total_states:,} 局面)")
    lines.append(f"  - 定理 K6 の反例: {len(k6_errs)} 件")
    lines.append(f"  - 主張 P(j) の反例: {len(p_errs)} 件")
    lines.append(f"  - 補足（先手の必勝手）の反例（非合法手 k = m+1）: {supp_illegal_count:,} 件")
    if supp_first_counterexample:
        lines.append(f"    最小反例: {supp_first_counterexample}")
    lines.append(f"  - 修正版戦略（c = m+1 で k = h）の反例: {len(fixed_strategy_errs)} 件")
    lines.append(f"所要時間: {elapsed:.2f} 秒")

    text = "\n".join(lines) + "\n"
    print(text, end="")
    out = Path(__file__).resolve().parent.parent / "data" / "gemini2_verify_k6.txt"
    out.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
