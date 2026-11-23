"""
gemini-2 による独立な Python ソルバーを用いた定理 K12″（11010 型および一般の k での g_2 の式）の数値検証。

何を計算するか:
1. PROBLEM.md の正確な定義のみから書いた全探索 DP (solve_count_dp) で、
   - (a) k = 2, Q_2 奇数の 3 例: w = 7, 19, 31 (m = 73, 201, 329) で 11010 型の開始局面と Ψ(j) を検証
   - (b) 例外 m = 9、および k = 2 (m = 137), k = 3 (m = 41, 297) で (b) を検証
2. 査読済み定理 K8 の独立実装で、m <= 10000 の v2(m+1) = 1 かつ v2(3h+1) = 2k >= 2 の全 m について、
   - m != 9 の全例で (b): g_0 = g_1 = m+2, g_2 = m+2 <=> v2(Q_k) 奇数 を検証
   - k = 2 かつ Q_2 奇数の全例で (a): Ψ(j) と 11010 型を検証。

実行方法:
  python code/gemini2_verify_k12_k2.py
結果を標準出力と data/gemini2_verify_k12_k2.txt に保存する。
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


def check_psi_k2(m: int, S_list: list[set[int]], g_list: list[int]) -> list[str]:
    h = (m + 1) // 2
    w = (3 * h + 1) // 16
    f1 = h + 2 * w
    f2 = h + 4 * w
    errs: list[str] = []
    for j, (S_j, g_j) in enumerate(zip(S_list, g_list)):
        r = j % 5
        if r == 0:
            if not all(d in S_j for d in range(1, m + 1, 2)):
                errs.append(f"Z1 fail m={m} j={j}")
            if (2 * w in S_j) or (4 * w not in S_j) or (8 * w in S_j):
                errs.append(f"Z2 fail m={m} j={j}")
            if g_j != m + 2:
                errs.append(f"g0mod5 fail m={m} j={j}")
        elif r == 1:
            if (8 * w not in S_j) or (10 * w not in S_j) or (9 * w in S_j):
                errs.append(f"U fail m={m} j={j}")
            if g_j != m + 2:
                errs.append(f"g1mod5 fail m={m} j={j}")
        elif r == 2:
            if (f1 not in S_j) or (f2 in S_j):
                errs.append(f"V fail m={m} j={j}")
            if g_j != m + 1:
                errs.append(f"g2mod5 fail m={m} j={j}")
        elif r == 3:
            if not all(d in S_j for d in range(1, m + 1, 2)):
                errs.append(f"W1 fail m={m} j={j}")
            if 8 * w not in S_j:
                errs.append(f"W2 fail m={m} j={j}")
            if g_j != m + 2:
                errs.append(f"g3mod5 fail m={m} j={j}")
        else:
            if f1 in S_j:
                errs.append(f"T1 fail m={m} j={j}")
            if g_j != m + 1:
                errs.append(f"g4mod5 fail m={m} j={j}")
    return errs


def main() -> None:
    t0 = time.perf_counter()
    lines: list[str] = []
    lines.append("=== gemini-2 独立検証: 定理 K12″（11010 型および一般の k での g_2 の式） ===")

    bf_cases = [
        (9, 1000),    # k=2, w=1, Q2=6 (exception to (b))
        (41, 1500),   # k=3, w=1, Q3=22 (v2=1)
        (73, 2500),   # k=2, w=7, Q2=41 (odd -> 11010)
        (137, 2000),  # k=2, w=13, Q2=76 (v2=2)
        (201, 2500),  # k=2, w=19, Q2=111 (odd -> 11010)
        (297, 2000),  # k=3, w=7, Q3=153 (odd)
        (329, 2500),  # k=2, w=31, Q2=181 (odd -> 11010)
    ]
    bf_errs: list[str] = []
    bf_states = 0
    for m, max_r in bf_cases:
        h = (m + 1) // 2
        val_v2 = v2(3 * h + 1)
        assert val_v2 % 2 == 0 and val_v2 >= 2
        k = val_v2 // 2
        w = (3 * h + 1) >> val_v2
        Qk = (m + 2 + w) // 2

        tab = solve_count_dp(m, max_r)
        bf_states += (max_r + 1) * (m + 1)
        a_rows = [r for r in range(max_r + 1) if all(tab[r])]
        S_list = [
            {d for d in range(1, m + 1) if tab[a_rows[j] + d][d]}
            for j in range(len(a_rows) - 1)
        ]
        g_list = [a_rows[j + 1] - a_rows[j] for j in range(len(a_rows) - 1)]

        if m == 9:
            if g_list[0] != 11 or g_list[1] != 11 or g_list[2] != 10:
                bf_errs.append(f"m=9 exception check fail g={g_list[:3]}")
        else:
            if g_list[0] != m + 2 or g_list[1] != m + 2:
                bf_errs.append(f"(b) g0/g1 fail m={m}")
            if (g_list[2] == m + 2) != (v2(Qk) % 2 == 1):
                bf_errs.append(f"(b) g2 fail m={m} Qk={Qk}")
            if k == 2 and Qk % 2 == 1:
                mod = 5 * m + 8
                good = {0, m + 2, 2 * m + 4, 3 * m + 5, 4 * m + 7}
                for n in range(1, max_r + 1):
                    if tab[n][0] != (n % mod in good):
                        bf_errs.append(f"(a) start fail m={m} n={n}")
                        break
                bf_errs.extend(check_psi_k2(m, S_list, g_list))

    # K8 verification for all m <= 10000 with v2(m+1) = 1 and even v2(3h+1) >= 2
    k8_b_errs: list[str] = []
    k8_a_errs: list[str] = []
    cnt_b = 0
    cnt_a = 0
    max_k = 0
    for m in range(5, 10001, 4):
        h = (m + 1) // 2
        val_v2 = v2(3 * h + 1)
        if val_v2 % 2 != 0:
            continue
        k = val_v2 // 2
        if k > max_k:
            max_k = k
        w = (3 * h + 1) >> val_v2
        Qk = (m + 2 + w) // 2
        if m == 9:
            continue
        cnt_b += 1
        if k == 2 and Qk % 2 == 1:
            cnt_a += 1
            n_blocks = 15 if m > 3000 else 25
            S_list, g_list = run_k8_blocks(m, n_blocks)
            if g_list[0] != m + 2 or g_list[1] != m + 2 or g_list[2] != m + 1:
                k8_b_errs.append(f"(b) fail m={m}")
            k8_a_errs.extend(check_psi_k2(m, S_list, g_list))
        else:
            _, g_list = run_k8_blocks(m, 3)
            if g_list[0] != m + 2 or g_list[1] != m + 2:
                k8_b_errs.append(f"(b) g0/g1 fail m={m}")
            if (g_list[2] == m + 2) != (v2(Qk) % 2 == 1):
                k8_b_errs.append(f"(b) g2 fail m={m}")

    elapsed = time.perf_counter() - t0
    lines.append(
        f"[1] 全探索検証 (7 例: m={[c[0] for c in bf_cases]}; 計 {bf_states:,} 局面): "
        f"反例 {len(bf_errs)} 件"
    )
    lines.append(
        f"[2] 査読済み K8 経由検証 (m <= 10000, m != 9 全 {cnt_b} 個 [最大 k={max_k}], "
        f"うち k=2, Q2 奇数 {cnt_a} 個): (b) 反例 {len(k8_b_errs)} 件, (a) 反例 {len(k8_a_errs)} 件"
    )
    if bf_errs or k8_b_errs or k8_a_errs:
        lines.append("ERRORS:")
        lines.extend((bf_errs + k8_b_errs + k8_a_errs)[:20])
    lines.append(f"所要時間: {elapsed:.2f} 秒")

    text = "\n".join(lines) + "\n"
    print(text, end="")
    out = Path(__file__).resolve().parent.parent / "data" / "gemini2_verify_k12_k2.txt"
    out.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
