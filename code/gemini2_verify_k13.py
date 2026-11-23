"""
gemini-2 による独立な Python ソルバーを用いた定理 K13（v2(m+1) = 3 の「100」型）の数値検証。

何を計算するか:
1. PROBLEM.md の正確な定義のみから書いた全探索 DP (solve_count_dp) で、
   {v2(9u+1), v2(11u+1)} = {1, 3} の 6 例
   (u = 5, 21, 37 [m = 39, 167, 295] および u = 15, 31, 47 [m = 119, 247, 375])
   について全局面を計算し、100 型の開始局面特徴づけ（n mod (3m+4) in {0, m+2, 2m+3}）と
   不変量 Λ(j) を直接検証。
2. 査読済み定理 K8 の独立実装で、m <= 10000 で v2(m+1) = 3 かつ
   {v2(9u+1), v2(11u+1)} = {1, 3} を満たす全 m について不変量 Λ(j) と 100 型を検証。

実行方法:
  python code/gemini2_verify_k13.py
結果を標準出力と data/gemini2_verify_k13.txt に保存する。
"""

from __future__ import annotations

import time
from pathlib import Path


def v2(n: int) -> int:
    return (n & -n).bit_length() - 1


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


def check_lambda(u: int, S_list: list[set[int]], g_list: list[int]) -> list[str]:
    m = 8 * u - 1
    h = 4 * u
    X1 = (9 * u + 1) // 2
    X3 = (11 * u + 1) // 2
    Y = X1 if v2(X1) == 2 else X3
    errs: list[str] = []
    for j, (S_j, g_j) in enumerate(zip(S_list, g_list)):
        rem = j % 3
        if rem == 0:
            if not all(d in S_j for d in range(1, m + 1, 2)):
                errs.append(f"A1 fail u={u} j={j}")
            if Y not in S_j:
                errs.append(f"A2 fail u={u} j={j}")
            if g_j != m + 2:
                errs.append(f"g0mod3 fail u={u} j={j}")
        elif rem == 1:
            if u in S_j:
                errs.append(f"B1 fail u={u} j={j}")
            if 3 * u in S_j:
                errs.append(f"B2 fail u={u} j={j}")
            if 6 * u not in S_j:
                errs.append(f"B3 fail u={u} j={j}")
            if g_j != m + 1:
                errs.append(f"g1mod3 fail u={u} j={j}")
        else:
            if 6 * u in S_j:
                errs.append(f"C1 fail u={u} j={j}")
            if (h + Y // 2) in S_j:
                errs.append(f"C2 fail u={u} j={j}")
            if g_j != m + 1:
                errs.append(f"g2mod3 fail u={u} j={j}")
    return errs


def main() -> None:
    t0 = time.perf_counter()
    lines: list[str] = []
    lines.append("=== gemini-2 独立検証: 定理 K13（v2(m+1) = 3 の「100」型） ===")

    bf_cases = [
        (5, 2000),   # m=39, v2(11u+1)=3
        (15, 2000),  # m=119, v2(9u+1)=3
        (21, 2000),  # m=167, v2(11u+1)=3
        (31, 2000),  # m=247, v2(9u+1)=3
        (37, 2500),  # m=295, v2(11u+1)=3
        (47, 2500),  # m=375, v2(9u+1)=3
    ]
    bf_errs: list[str] = []
    bf_states = 0
    for u, max_r in bf_cases:
        m = 8 * u - 1
        assert {v2(9 * u + 1), v2(11 * u + 1)} == {1, 3}
        tab = solve_count_dp(m, max_r)
        bf_states += (max_r + 1) * (m + 1)
        mod = 3 * m + 4
        for n in range(1, max_r + 1):
            if tab[n][0] != (n % mod in (0, m + 2, 2 * m + 3)):
                bf_errs.append(f"100-type start fail m={m} n={n}")
                break
        a_rows = [r for r in range(max_r + 1) if all(tab[r])]
        S_list = [
            {d for d in range(1, m + 1) if tab[a_rows[j] + d][d]}
            for j in range(len(a_rows) - 1)
        ]
        g_list = [a_rows[j + 1] - a_rows[j] for j in range(len(a_rows) - 1)]
        bf_errs.extend(check_lambda(u, S_list, g_list))

    # K8 verification for all m <= 10000 with v2(m+1)=3 and {v2(9u+1), v2(11u+1)} == {1, 3}
    k8_errs: list[str] = []
    cnt = 0
    for u in range(1, 10002 // 8 + 1, 2):
        m = 8 * u - 1
        if m > 10000:
            break
        if {v2(9 * u + 1), v2(11 * u + 1)} != {1, 3}:
            continue
        cnt += 1
        n_blocks = 15 if m > 3000 else 30
        S_list, g_list = run_k8_blocks(m, n_blocks)
        k8_errs.extend(check_lambda(u, S_list, g_list))

    elapsed = time.perf_counter() - t0
    lines.append(
        f"[1] 全探索検証 (6 例: m={[8*u-1 for u, _ in bf_cases]}; 計 {bf_states:,} 局面): "
        f"反例 {len(bf_errs)} 件"
    )
    lines.append(
        f"[2] 査読済み K8 経由検証 (m <= 10000 の該当全 {cnt} 個): 反例 {len(k8_errs)} 件"
    )
    if bf_errs or k8_errs:
        lines.append("ERRORS:")
        lines.extend((bf_errs + k8_errs)[:20])
    lines.append(f"所要時間: {elapsed:.2f} 秒")

    text = "\n".join(lines) + "\n"
    print(text, end="")
    out = Path(__file__).resolve().parent.parent / "data" / "gemini2_verify_k13.txt"
    out.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
