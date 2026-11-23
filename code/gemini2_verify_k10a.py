"""
gemini-2 による独立な Python ソルバーを用いた定理 K10 (a)（v2(m+1)=3, u≡1(mod 8), u>=9）の数値検証。

何を計算するか:
1. PROBLEM.md の正確な定義のみから書いた全探索 DP (solve_count_dp) で、
   u = 9, 17, 25（m = 71, 135, 199）、0 <= r <= 2500 の全局面 (r, p) を計算し、
   - 交互型（(n, 0) が P ⇔ n ≡ 0 または m+2 (mod 2m+3)）
   - 証明内の不変量 I(j)（(E1)〜(E4)、(O1)〜(O5)、および奇数 j での 2u in S_j）
   を全探索表上で直接検証する。
2. 査読済み定理 K8（ブロック漸化式 R）の独立実装で、u = 9, 17, ..., 249（31 個の u, m = 71..1991）
   について各 40 ブロックまで I(j) および交互型を検証する。

実行方法:
  python code/gemini2_verify_k10a.py
結果を標準出力と data/gemini2_verify_k10a.txt に保存する。
"""

from __future__ import annotations

import time
from pathlib import Path


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


def run_k8_blocks(m: int, n_blocks: int) -> tuple[list[set[int]], list[int]]:
    h = (m + 1) // 2
    S_list: list[set[int]] = []
    g_list: list[int] = []
    for j in range(n_blocks):
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
                if g_list[j - 1] == m + 2 and d == h - 1:
                    blocked = True
            if not blocked:
                S_j.add(d)
        g_j = (m + 2) if (h in S_j) else (m + 1)
        S_list.append(S_j)
        g_list.append(g_j)
    return S_list, g_list


def check_invariant(u: int, S_list: list[set[int]], g_list: list[int]) -> list[str]:
    m = 8 * u - 1
    h = 4 * u
    w = (11 * u + 1) // 2
    errs: list[str] = []
    for j, (S_j, g_j) in enumerate(zip(S_list, g_list)):
        if j % 2 == 0:
            if not all(d in S_j for d in range(1, m + 1, 2)):
                errs.append(f"E1 fail u={u} j={j}")
            if w in S_j:
                errs.append(f"E2 fail u={u} j={j}")
            if h not in S_j:
                errs.append(f"E3 fail u={u} j={j}")
            if g_j != m + 2:
                errs.append(f"E4 fail u={u} j={j}")
        else:
            if u in S_j:
                errs.append(f"O1 fail u={u} j={j}")
            if 2 * u not in S_j:
                errs.append(f"2u fail u={u} j={j}")
            if 3 * u not in S_j:
                errs.append(f"O2 fail u={u} j={j}")
            if 6 * u in S_j:
                errs.append(f"O3 fail u={u} j={j}")
            if h in S_j:
                errs.append(f"O4 fail u={u} j={j}")
            if g_j != m + 1:
                errs.append(f"O5 fail u={u} j={j}")
    return errs


def main() -> None:
    t0 = time.perf_counter()
    lines: list[str] = []
    lines.append("=== gemini-2 独立検証: 定理 K10 (a)（v2(m+1)=3, u≡1(mod 8), u>=9） ===")

    # 1. 全探索検証 (u = 9, 17, 25 -> m = 71, 135, 199)
    bf_errs: list[str] = []
    bf_states = 0
    for u in (9, 17, 25):
        m = 8 * u - 1
        max_r = 2500
        tab = solve_count_dp(m, max_r)
        bf_states += (max_r + 1) * (m + 1)
        mod = 2 * m + 3
        for n in range(1, max_r + 1):
            if tab[n][0] != (n % mod in (0, m + 2)):
                bf_errs.append(f"alt fail at m={m}, n={n}")
                break
        a_rows = [r for r in range(max_r + 1) if all(tab[r])]
        S_list = [{d for d in range(1, m + 1) if tab[a_rows[j] + d][d]} for j in range(len(a_rows) - 1)]
        g_list = [a_rows[j + 1] - a_rows[j] for j in range(len(a_rows) - 1)]
        bf_errs.extend(check_invariant(u, S_list, g_list))

    # 2. 査読済み K8 経由の広範囲検証 (u = 9, 17, ..., 249, 各 40 ブロック)
    k8_errs: list[str] = []
    us = list(range(9, 250, 8))
    for u in us:
        m = 8 * u - 1
        S_list, g_list = run_k8_blocks(m, 40)
        k8_errs.extend(check_invariant(u, S_list, g_list))

    elapsed = time.perf_counter() - t0
    lines.append(f"[1] 全探索検証 (u=9,17,25; m=71,135,199; 0<=r<=2500; 計 {bf_states:,} 局面): 反例 {len(bf_errs)} 件")
    lines.append(f"[2] 査読済み K8 経由検証 (u=9..249 の {len(us)} 個, 各 40 ブロック): 反例 {len(k8_errs)} 件")
    lines.append(f"所要時間: {elapsed:.2f} 秒")
    if bf_errs or k8_errs:
        lines.append(f"[!] errors: bf={bf_errs[:5]}, k8={k8_errs[:5]}")

    text = "\n".join(lines) + "\n"
    print(text, end="")
    out = Path(__file__).resolve().parent.parent / "data" / "gemini2_verify_k10a.txt"
    out.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
