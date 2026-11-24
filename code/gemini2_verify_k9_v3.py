"""
gemini-2 による独立な Python ソルバーを用いた定理 K9-v3（m = 8t+1, v2(3t+1) = 3）の数値検証。

何を計算するか:
1. PROBLEM.md の正確な定義のみから書いた全探索 DP (solve_count_dp) で、
   q = 5, 11（m = 105, 233）、0 <= r <= 3000 の全局面を計算し、
   定理 K9-v3（交互型）および証明内の不変量 L(j) を全探索表上で直接検証。
2. 査読済み定理 K8 の独立実装で、q = 5, 11, ..., 119（20 個の q, m = 105..2537）、
   各 30 ブロックまで L(j) および交互型を検証。

実行方法:
  python code/gemini2_verify_k9_v3.py
結果を標準出力と data/gemini2_verify_k9_v3.txt に保存する。
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


def check_L(q: int, S_list: list[set[int]], g_list: list[int]) -> list[str]:
    m = (64 * q - 5) // 3
    h = (32 * q - 1) // 3
    errs: list[str] = []
    for j, (S_j, g_j) in enumerate(zip(S_list, g_list)):
        if j % 2 == 0:
            if not all(d in S_j for d in range(1, m + 1, 2)):
                errs.append(f"E odd fail q={q} j={j}")
            for x, want in [(2*q, False), (4*q, True), (8*q, False), (16*q, True), (10*q, False), (20*q, True)]:
                if (x in S_j) != want:
                    errs.append(f"E({x}) fail q={q} j={j}")
            if g_j != m + 2:
                errs.append(f"E gap fail q={q} j={j}")
        else:
            for x in (h, h + 2*q, h + 8*q, h + 10*q):
                if x in S_j:
                    errs.append(f"O({x}) fail q={q} j={j}")
            if g_j != m + 1:
                errs.append(f"O gap fail q={q} j={j}")
    return errs


def main() -> None:
    t0 = time.perf_counter()
    lines: list[str] = []
    lines.append("=== gemini-2 独立検証: 定理 K9-v3（m = 8t+1, v2(3t+1) = 3） ===")

    bf_errs: list[str] = []
    bf_states = 0
    for q in (5, 11):
        m = (64 * q - 5) // 3
        max_r = 3000
        tab = solve_count_dp(m, max_r)
        bf_states += (max_r + 1) * (m + 1)
        mod = 2 * m + 3
        for n in range(1, max_r + 1):
            if tab[n][0] != (n % mod in (0, m + 2)):
                bf_errs.append(f"alt fail m={m} n={n}")
                break
        a_rows = [r for r in range(max_r + 1) if all(tab[r])]
        S_list = [{d for d in range(1, m + 1) if tab[a_rows[j] + d][d]} for j in range(len(a_rows) - 1)]
        g_list = [a_rows[j + 1] - a_rows[j] for j in range(len(a_rows) - 1)]
        bf_errs.extend(check_L(q, S_list, g_list))

    k8_errs: list[str] = []
    qs = list(range(5, 120, 6))
    for q in qs:
        m = (64 * q - 5) // 3
        S_list, g_list = run_k8_blocks(m, 30)
        k8_errs.extend(check_L(q, S_list, g_list))

    elapsed = time.perf_counter() - t0
    lines.append(f"[1] 全探索検証 (q=5,11; m=105,233; 0<=r<=3000; 計 {bf_states:,} 局面): 反例 {len(bf_errs)} 件")
    lines.append(f"[2] 査読済み K8 経由検証 (q=5..119 の {len(qs)} 個, 各 30 ブロック): 反例 {len(k8_errs)} 件")
    lines.append(f"所要時間: {elapsed:.2f} 秒")

    text = "\n".join(lines) + "\n"
    print(text, end="")
    out = Path(__file__).resolve().parent.parent / "data" / "gemini2_verify_k9_v3.txt"
    out.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
