"""
gemini-2 による独立な Python ソルバーを用いた定理 K12（v2(m+1) = 1, v2(3h+1) = 2 の「110」型）の数値検証。

何を計算するか:
1. PROBLEM.md の正確な定義のみから書いた全探索 DP (solve_count_dp) で、
   h = 9, 17, 25, 33, 41, 49, 57, 65 (m = 17, 33, 49, 65, 81, 97, 113, 129), 0 <= r <= 2000
   の全局面を計算し、定理 K12 (a)（Q 奇数なら 110 型、開始局面 P <=> n mod (3m+5) in {0, m+2, 2m+4}、
   不変量 Θ(j)）および定理 K12 (b)（g_0 = g_1 = m+2、g_2 = m+2 <=> v2(Q) 奇数）を直接検証。
2. 査読済み定理 K8 の独立実装で、v2(m+1) = 1 かつ v2(3h+1) = 2 の全 m <= 10000（624 個）について、
   定理 K12 (b)（全 624 個）および定理 K12 (a)（Q 奇数の全 312 個、各 30 ブロックの Θ(j)）を検証。

実行方法:
  python code/gemini2_verify_k12.py
結果を標準出力と data/gemini2_verify_k12.txt に保存する。
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


def check_theta(m: int, S_list: list[set[int]], g_list: list[int]) -> list[str]:
    h = (m + 1) // 2
    w = (3 * h + 1) // 4
    e_star = 2 * w
    errs: list[str] = []
    for j, (S_j, g_j) in enumerate(zip(S_list, g_list)):
        rem = j % 3
        if rem == 0:
            if not all(d in S_j for d in range(1, m + 1, 2)):
                errs.append(f"E1 fail m={m} j={j}")
            if e_star in S_j:
                errs.append(f"E2 fail m={m} j={j}")
            if g_j != m + 2:
                errs.append(f"g0mod3 fail m={m} j={j}")
        elif rem == 1:
            if w in S_j:
                errs.append(f"P1 fail m={m} j={j}")
            if e_star not in S_j:
                errs.append(f"P2 fail m={m} j={j}")
            if h not in S_j:
                errs.append(f"P3 fail m={m} j={j}")
            if g_j != m + 2:
                errs.append(f"g1mod3 fail m={m} j={j}")
        else:
            if h in S_j:
                errs.append(f"R1 fail m={m} j={j}")
            if g_j != m + 1:
                errs.append(f"g2mod3 fail m={m} j={j}")
    return errs


def main() -> None:
    t0 = time.perf_counter()
    lines: list[str] = []
    lines.append("=== gemini-2 独立検証: 定理 K12（v2(m+1) = 1, v2(3h+1) = 2 の「110」型） ===")

    bf_hs = [9, 17, 25, 33, 41, 49, 57, 65]
    bf_errs: list[str] = []
    bf_states = 0
    for h in bf_hs:
        m = 2 * h - 1
        assert (11 * h + 5) % 8 == 0
        Q = (11 * h + 5) // 8
        max_r = 2000
        tab = solve_count_dp(m, max_r)
        bf_states += (max_r + 1) * (m + 1)
        a_rows = [r for r in range(max_r + 1) if all(tab[r])]
        S_list = [
            {d for d in range(1, m + 1) if tab[a_rows[j] + d][d]}
            for j in range(len(a_rows) - 1)
        ]
        g_list = [a_rows[j + 1] - a_rows[j] for j in range(len(a_rows) - 1)]

        # K12 (b)
        if g_list[0] != m + 2 or g_list[1] != m + 2:
            bf_errs.append(f"K12(b) g0/g1 fail m={m}")
        if (g_list[2] == m + 2) != (v2(Q) % 2 == 1):
            bf_errs.append(f"K12(b) g2 fail m={m} Q={Q}")

        # K12 (a)
        if Q % 2 == 1:
            mod = 3 * m + 5
            for n in range(1, max_r + 1):
                if tab[n][0] != (n % mod in (0, m + 2, 2 * m + 4)):
                    bf_errs.append(f"K12(a) start fail m={m} n={n}")
                    break
            bf_errs.extend(check_theta(m, S_list, g_list))

    # K8 verification for all m <= 10000 with v2(m+1)=1, v2(3h+1)=2
    k8_b_errs: list[str] = []
    k8_a_errs: list[str] = []
    total_m = 0
    odd_q_m = 0
    for m in range(5, 10001, 4):
        h = (m + 1) // 2
        if v2(3 * h + 1) != 2:
            continue
        total_m += 1
        if (11 * h + 5) % 8 != 0:
            k8_b_errs.append(f"Q not int m={m}")
            continue
        Q = (11 * h + 5) // 8
        if Q % 2 == 1:
            odd_q_m += 1
            n_blocks = 12 if m > 3000 else 30
            S_list, g_list = run_k8_blocks(m, n_blocks)
            if g_list[0] != m + 2 or g_list[1] != m + 2 or g_list[2] != m + 1:
                k8_b_errs.append(f"K12(b) oddQ fail m={m}")
            k8_a_errs.extend(check_theta(m, S_list, g_list))
        else:
            _, g_list = run_k8_blocks(m, 3)
            if g_list[0] != m + 2 or g_list[1] != m + 2:
                k8_b_errs.append(f"K12(b) g0/g1 fail m={m}")
            if (g_list[2] == m + 2) != (v2(Q) % 2 == 1):
                k8_b_errs.append(f"K12(b) g2 fail m={m}")

    elapsed = time.perf_counter() - t0
    lines.append(
        f"[1] 全探索検証 (8 例: m={[2*h-1 for h in bf_hs]}, 0<=r<=2000; 計 {bf_states:,} 局面): "
        f"反例 {len(bf_errs)} 件"
    )
    lines.append(
        f"[2] 査読済み K8 経由検証 (m <= 10000 の該当全 {total_m} 個, うち Q 奇数 {odd_q_m} 個): "
        f"(b) 反例 {len(k8_b_errs)} 件, (a) 反例 {len(k8_a_errs)} 件"
    )
    if bf_errs or k8_b_errs or k8_a_errs:
        lines.append("ERRORS:")
        lines.extend((bf_errs + k8_b_errs + k8_a_errs)[:20])
    lines.append(f"所要時間: {elapsed:.2f} 秒")

    text = "\n".join(lines) + "\n"
    print(text, end="")
    out = Path(__file__).resolve().parent.parent / "data" / "gemini2_verify_k12.txt"
    out.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
