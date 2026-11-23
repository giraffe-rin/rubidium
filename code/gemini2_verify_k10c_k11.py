"""
gemini-2 による独立な Python ソルバーを用いた定理 K10c・系（K10(b)）・定理 K11 の数値検証。

何を計算するか:
1. PROBLEM.md の正確な定義のみから書いた全探索 DP (solve_count_dp) で、
   - v = 3: u = 1, 3, 5, 7, 9, 11, 13, 15 (m = 7, 23, 39, 55, 71, 87, 103, 119)
   - v = 5: u = 1, 3, 5, 7 (m = 31, 95, 159, 223)
   - v = 7: u = 1 (m = 127)
   について全局面を計算し、定理 K10c (a)(b)(c)・系・定理 K11 と補題 O / 1' / E2 を直接検証。
2. 査読済み定理 K8 の独立実装で、v2(m+1) >= 3 が奇数の全 m <= 20000（1,667 個）について、
   ブロック 0..2 を計算し、補題 1'・定理 K10c (a)(b)(c)・系・定理 K11（v = 5, 7, 9, 11, 13）
   を全件検証。

実行方法:
  python code/gemini2_verify_k10c_k11.py
結果を標準出力と data/gemini2_verify_k10c_k11.txt に保存する。
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


def check_m(m: int, S_list: list[set[int]], g_list: list[int]) -> list[str]:
    errs: list[str] = []
    v = v2(m + 1)
    u = (m + 1) >> v
    h = (m + 1) // 2
    X1 = (((1 << v) + 1) * u + 1) // 2

    if g_list[0] != m + 2:
        errs.append(f"g0 fail m={m}")

    # Lemma 1'
    want_g1 = (m + 2) if (v2(X1) % 2 == 1) else (m + 1)
    if g_list[1] != want_g1:
        errs.append(f"Lemma 1' fail m={m} g1={g_list[1]} want={want_g1}")

    if v == 3:
        # K10c (a)
        if (g_list[1] == m + 2) != (v2(9 * u + 1) % 2 == 0):
            errs.append(f"K10c(a) fail m={m}")
        if u == 1:
            # K10c (c)
            if (3 in S_list[1]) or (6 not in S_list[1]) or (g_list[1] != m + 1) or (g_list[2] != m + 1):
                errs.append(f"K10c(c) fail m={m}")
        else:
            if g_list[1] == m + 1:
                # K10c (b)
                if (g_list[2] == m + 2) != (v2(11 * u + 1) % 2 == 0):
                    errs.append(f"K10c(b) fail m={m}")
        # Corollary: u == 7 (mod 8) -> not alternating (g1=m+2 or g2=m+1)
        if u % 8 == 7 and (g_list[1] == m + 1 and g_list[2] == m + 2):
            errs.append(f"Cor u=7 mod 8 fail m={m}")
    elif v >= 5 and v % 2 == 1:
        # K11: either g1 = m+2 or g2 = m+1
        if v2(X1) % 2 == 1:
            if g_list[1] != m + 2:
                errs.append(f"K11 odd v2(X1) fail m={m}")
        else:
            if g_list[1] != m + 1:
                errs.append(f"K11 even v2(X1) g1 fail m={m}")
            if u % 4 == 3:
                if (3 * u in S_list[1]) or ((3 * (1 << (v - 2)) * u) not in S_list[1]):
                    errs.append(f"K11 u=3 mod 4 mid fail m={m}")
            else:
                if (
                    (5 * u in S_list[1])
                    or (9 * u in S_list[1])
                    or ((5 * (1 << (v - 3)) * u) in S_list[1])
                    or ((9 * (1 << (v - 4)) * u) not in S_list[1])
                    or (((1 << (v - 3)) * u) in S_list[2])
                    or ((h // 2) not in S_list[2])
                ):
                    errs.append(f"K11 u=1 mod 4 mid fail m={m}")
            if (h in S_list[2]) or (g_list[2] != m + 1):
                errs.append(f"K11 g2 fail m={m}")
    return errs


def main() -> None:
    t0 = time.perf_counter()
    lines: list[str] = []
    lines.append("=== gemini-2 独立検証: 定理 K10c・系（K10(b)）・定理 K11 ===")

    bf_cases = [
        # v = 3: u = 1..15
        (7, 1500), (23, 1500), (39, 1500), (55, 1500),
        (71, 1500), (87, 1500), (103, 1500), (119, 1500),
        # v = 5: u = 1, 3, 5, 7
        (31, 1500), (95, 1500), (159, 1500), (223, 2000),
        # v = 7: u = 1
        (127, 2000),
    ]
    bf_errs: list[str] = []
    bf_states = 0
    for m, max_r in bf_cases:
        tab = solve_count_dp(m, max_r)
        bf_states += (max_r + 1) * (m + 1)
        a_rows = [r for r in range(max_r + 1) if all(tab[r])]
        S_list = [
            {d for d in range(1, m + 1) if tab[a_rows[j] + d][d]}
            for j in range(min(4, len(a_rows) - 1))
        ]
        g_list = [a_rows[j + 1] - a_rows[j] for j in range(min(4, len(a_rows) - 1))]
        bf_errs.extend(check_m(m, S_list, g_list))

    # K8 verification for all m <= 20000 with odd v2(m+1) >= 3
    k8_errs: list[str] = []
    cnt_v3 = 0
    cnt_v5p = 0
    max_v = 0
    for m in range(7, 20001, 2):
        v = v2(m + 1)
        if v >= 3 and v % 2 == 1:
            if v == 3:
                cnt_v3 += 1
            else:
                cnt_v5p += 1
            if v > max_v:
                max_v = v
            S_list, g_list = run_k8_blocks(m, 3)
            k8_errs.extend(check_m(m, S_list, g_list))

    elapsed = time.perf_counter() - t0
    lines.append(
        f"[1] 全探索検証 ({len(bf_cases)} 例: v=3 で 8 例, v=5 で 4 例, v=7 で 1 例; "
        f"計 {bf_states:,} 局面): 反例 {len(bf_errs)} 件"
    )
    lines.append(
        f"[2] 査読済み K8 経由検証 (m <= 20000 の奇数 v>=3 全 {cnt_v3 + cnt_v5p} 個; "
        f"v=3 が {cnt_v3} 個, v>=5 が {cnt_v5p} 個 [最大 v={max_v}]): 反例 {len(k8_errs)} 件"
    )
    if bf_errs or k8_errs:
        lines.append("ERRORS:")
        lines.extend((bf_errs + k8_errs)[:20])
    lines.append(f"所要時間: {elapsed:.2f} 秒")

    text = "\n".join(lines) + "\n"
    print(text, end="")
    out = Path(__file__).resolve().parent.parent / "data" / "gemini2_verify_k10c_k11.txt"
    out.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
