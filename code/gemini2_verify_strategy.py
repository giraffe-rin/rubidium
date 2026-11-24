"""
gemini-2 による独立な Python 全探索ソルバーを用いた系 W（一般の局面 (r, p) の必勝戦略）の数値検証。

何を計算するか:
1. PROBLEM.md の正確な定義のみから書いた全探索 DP (solve_count_dp) で
   1 <= m <= 60, 0 <= r <= 3000 の全局面 (r, p) (計 5,671,890 局面) の勝敗を計算。
2. 系 W の規則のみ（m = 1 は T(r) = {1}、m >= 2 はブロック漸化式 R から得た (a_j, S_j, g_j)）から
   各局面 (r, p) の必勝手集合 W_cor(r, p) を構成。
3. 全 5,671,890 局面について次を検証:
   - W_cor(r, p) == ∅ ⇔ 全探索表で (r, p) が P 局面。
   - W_cor(r, p) のすべての手 k が合法 (1 <= k <= min(m, r) かつ k != p) かつ
     行き先 (r - k, k) が全探索表で P 局面。
   - さらに W_cor(r, p) が、全探索で求めた全勝ち手集合 {k 合法 : (r-k, k) が P} と集合として完全一致。

実行方法:
  python code/gemini2_verify_strategy.py
結果を標準出力と data/gemini2_verify_strategy.txt に保存する。
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


def build_blocks_k8(m: int, max_r: int) -> tuple[list[int], list[set[int]], list[int]]:
    is_odd = (m % 2 == 1)
    h = (m + 1) // 2 if is_odd else -1
    a_list: list[int] = []
    S_list: list[set[int]] = []
    g_list: list[int] = []
    a = 0
    j = 0
    while a <= max_r:
        a_list.append(a)
        S_j: set[int] = set()
        for d in range(1, m + 1):
            blocked = False
            if d % 2 == 0 and (d // 2) in S_j:
                blocked = True
            if not blocked and j >= 1:
                gp = g_list[j - 1]
                if (gp + d) % 2 == 0:
                    e = (gp + d) // 2
                    if e <= m and e in S_list[j - 1]:
                        blocked = True
            if not blocked and j >= 1:
                if g_list[j - 1] == m + 2 and is_odd and d == h - 1:
                    blocked = True
            if not blocked:
                S_j.add(d)
        g_j = (m + 2) if (is_odd and h in S_j) else (m + 1)
        S_list.append(S_j)
        g_list.append(g_j)
        a += g_j
        j += 1
    return a_list, S_list, g_list


def main() -> None:
    t0 = time.perf_counter()
    lines: list[str] = []
    lines.append("=== gemini-2 独立検証: 系 W（一般の局面 (r, p) の必勝戦略） ===")

    max_m = 60
    max_r = 3000
    total_states = 0
    errs: list[str] = []

    # m = 1
    tab1 = solve_count_dp(1, max_r)
    for r in range(max_r + 1):
        limit = 1 if r >= 1 else 0
        for p in range(2):
            total_states += 1
            w_cor = set() if (r == 0 or p == 1) else {1}
            w_bf = {k for k in range(1, limit + 1) if k != p and tab1[r - k][k]}
            if w_cor != w_bf or (len(w_cor) == 0) != tab1[r][p]:
                errs.append(f"m=1, r={r}, p={p}: cor={w_cor}, bf={w_bf}")

    # 2 <= m <= 60
    for m in range(2, max_m + 1):
        tab = solve_count_dp(m, max_r)
        a_list, S_list, g_list = build_blocks_k8(m, max_r)
        is_odd = (m % 2 == 1)
        h = (m + 1) // 2 if is_odd else -1

        j = 0
        for r in range(max_r + 1):
            while j + 1 < len(a_list) and a_list[j + 1] <= r:
                j += 1
            d = r - a_list[j]
            limit = m if r >= m else r

            # 系 W が定める T(r) を構成
            if d == 0:
                t_cor: set[int] = set()
            elif 1 <= d <= m:
                t_cor = {d}
                if d % 2 == 0 and (d // 2) in S_list[j]:
                    t_cor.add(d // 2)
                if j >= 1:
                    gp = g_list[j - 1]
                    if (gp + d) % 2 == 0:
                        e = (gp + d) // 2
                        if e <= m and e in S_list[j - 1]:
                            t_cor.add(e)
                    if gp == m + 2 and is_odd and d == h - 1:
                        t_cor.add(h)
            else:
                # d == m + 1
                assert d == m + 1 and g_list[j] == m + 2
                t_cor = {h}

            # 全探索による T_bf(r)
            t_bf = {k for k in range(1, limit + 1) if tab[r - k][k]}
            if t_cor != t_bf:
                errs.append(f"T mismatch at m={m}, r={r}: cor={t_cor}, bf={t_bf}")
                break

            # 全 p について W_cor(r, p) = t_cor \ {p} の合法性・勝敗一致を検証
            row = tab[r]
            for p in range(m + 1):
                total_states += 1
                w_cor = t_cor - {p}
                if (len(w_cor) == 0) != row[p]:
                    errs.append(f"P/N mismatch at m={m}, r={r}, p={p}")
                    break
                for k in w_cor:
                    if not (1 <= k <= limit and k != p and tab[r - k][k]):
                        errs.append(f"Invalid move k={k} at m={m}, r={r}, p={p}")
                        break

    elapsed = time.perf_counter() - t0
    lines.append(f"検証範囲: 1 <= m <= {max_m}, 0 <= r <= {max_r} (計 {total_states:,} 局面)")
    lines.append(f"  - 系 W の勝ち手集合・合法性・P/N 判定の反例: {len(errs)} 件")
    lines.append(f"所要時間: {elapsed:.2f} 秒")
    if errs:
        lines.append(f"[!] errors: {errs[:10]}")

    text = "\n".join(lines) + "\n"
    print(text, end="")
    out = Path(__file__).resolve().parent.parent / "data" / "gemini2_verify_strategy.txt"
    out.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
