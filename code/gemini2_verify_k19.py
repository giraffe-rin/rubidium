"""
gemini-2 による独立な Python ソルバーを用いた定理 K19・系 K19.1（v2(m+1) = 1, v2(h-1) = 2j+1 の 1^{j+1}0 型）の数値検証。

何を計算するか:
1. PROBLEM.md の正確な定義のみから書いた全探索 DP (solve_count_dp) で、
   r = 1 (m=5), r = 3 (m=17), r = 5 (m=65, 193), r = 7 (m=257), r = 9 (m=1025)
   の 6 例について全局面を計算し、1^{j+1}0 型、距離 a_i, b_i の性質と恒等式 (E1)-(E3)、
   および主張 P(n) を全探索表上で直接検証。
2. 査読済み定理 K8 の独立実装で、5 <= m <= 10000 の v2(m+1) = 1 かつ r = v2(h-1) 奇数の
   全 m（r = 1, 3, 5, 7, 9, 11）について、各 3 周期（ただし大きい m は 2 周期）の間隔と
   主張 P(n) を全件検証。

実行方法:
  python code/gemini2_verify_k19.py
結果を標準出力と data/gemini2_verify_k19.txt に保存する。
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
            if (d & 1) == 0 and (d >> 1) in S_j:
                blocked = True
            if not blocked and j >= 1:
                gp = g_list[j - 1]
                if ((gp + d) & 1) == 0:
                    e = (gp + d) >> 1
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


def check_k19(m: int, S_list: list[set[int]], g_list: list[int]) -> list[str]:
    errs: list[str] = []
    h = (m + 1) // 2
    D = h - 1
    r = v2(D)
    assert r % 2 == 1
    j_param = (r - 1) // 2
    L = j_param + 2

    # Compute a_i (1 <= i <= j) and b_i (0 <= i <= j) and check integer/parity/bounds/identities
    a: dict[int, int] = {}
    b: dict[int, int] = {}
    for i in range(1, j_param + 1):
        num = D * ((1 << (2 * i)) - 1)
        den = 3 * (1 << (2 * i))
        if num % den != 0:
            errs.append(f"a_{i} not int m={m}")
            return errs
        ai = h - num // den
        if (ai & 1) != 1 or not (0 < ai < h - 1):
            errs.append(f"a_{i} parity/bound fail m={m} ai={ai}")
        a[i] = ai

    for i in range(0, j_param + 1):
        num = D * (2 * (1 << (2 * i)) + 1)
        den = 3 * (1 << (2 * i + 1))
        if num % den != 0:
            errs.append(f"b_{i} not int m={m}")
            return errs
        bi = h + 1 + num // den
        want_odd = 1 if i == j_param else 0
        if (bi & 1) != want_odd or not (h + 1 < bi <= m):
            errs.append(f"b_{i} parity/bound fail m={m} bi={bi}")
        b[i] = bi

    # Identities (E1)-(E3)
    if (m + 2 + h) // 2 != b[0]:
        errs.append(f"E1 fail m={m}")
    for i in range(1, j_param + 1):
        if (m + 2 + a[i]) // 2 != b[i]:
            errs.append(f"E2 fail m={m} i={i}")
    for i in range(0, j_param):
        if b[i] // 2 != a[i + 1]:
            errs.append(f"E3 fail m={m} i={i}")

    # Check P(n) and gaps across all computed blocks
    for J, (S_J, g_J) in enumerate(zip(S_list, g_list)):
        n = J % L
        want_g = (m + 2) if (n <= j_param) else (m + 1)
        if g_J != want_g:
            errs.append(f"gap fail m={m} J={J} n={n} got={g_J} want={want_g}")
            break
        if n <= j_param:
            if h not in S_J:
                errs.append(f"h not in S_J m={m} J={J}")
            upper_a = min(j_param, j_param - n + 1)
            for i in range(1, upper_a + 1):
                if (a[i] in S_J) != (i + n <= j_param):
                    errs.append(f"P(n) a_{i} fail m={m} J={J} n={n}")
            for i in range(0, j_param - n + 1):
                if (b[i] in S_J) != (i == j_param - n):
                    errs.append(f"P(n) b_{i} fail m={m} J={J} n={n}")
    return errs


def main() -> None:
    t0 = time.perf_counter()
    lines: list[str] = []
    lines.append("=== gemini-2 独立検証: 定理 K19・系 K19.1（v2(m+1) = 1, v2(h-1) = 2j+1） ===")

    bf_cases = [
        (5, 800),      # r=1 (j=0)
        (17, 1000),    # r=3 (j=1)
        (65, 1600),    # r=5 (j=2, u=1)
        (193, 2500),   # r=5 (j=2, u=3)
        (257, 3200),   # r=7 (j=3, u=1)
        (1025, 6500),  # r=9 (j=4, u=1)
    ]
    bf_errs: list[str] = []
    bf_states = 0
    for m, max_r in bf_cases:
        tab = solve_count_dp(m, max_r)
        bf_states += (max_r + 1) * (m + 1)
        a_rows = [r for r in range(max_r + 1) if all(tab[r])]
        S_list = [
            {d for d in range(1, m + 1) if tab[a_rows[J] + d][d]}
            for J in range(len(a_rows) - 1)
        ]
        g_list = [a_rows[J + 1] - a_rows[J] for J in range(len(a_rows) - 1)]
        bf_errs.extend(check_k19(m, S_list, g_list))

    # K8 verification for all m <= 10000 with v2(m+1)=1 and odd r = v2(h-1)
    k8_errs: list[str] = []
    cnt = 0
    max_r_seen = 0
    for m in range(5, 10001, 4):
        h = (m + 1) // 2
        r = v2(h - 1)
        if r % 2 != 1:
            continue
        cnt += 1
        if r > max_r_seen:
            max_r_seen = r
        j_param = (r - 1) // 2
        L = j_param + 2
        n_blocks = (2 * L) if m > 3000 else (3 * L)
        S_list, g_list = run_k8_blocks(m, n_blocks)
        k8_errs.extend(check_k19(m, S_list, g_list))

    elapsed = time.perf_counter() - t0
    lines.append(
        f"[1] 全探索検証 (6 例: m={[c[0] for c in bf_cases]}; 計 {bf_states:,} 局面): "
        f"反例 {len(bf_errs)} 件"
    )
    lines.append(
        f"[2] 査読済み K8 経由検証 (5 <= m <= 10000 の該当全 {cnt} 個 [最大 r={max_r_seen}]): "
        f"反例 {len(k8_errs)} 件"
    )
    if bf_errs or k8_errs:
        lines.append("ERRORS:")
        lines.extend((bf_errs + k8_errs)[:20])
    lines.append(f"所要時間: {elapsed:.2f} 秒")

    text = "\n".join(lines) + "\n"
    print(text, end="")
    out = Path(__file__).resolve().parent.parent / "data" / "gemini2_verify_k19.txt"
    out.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
