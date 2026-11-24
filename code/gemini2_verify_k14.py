"""
gemini-2 による独立な Python ソルバーを用いた定理 K14・系 K14.1 の数値検証。

何を計算するか:
1. PROBLEM.md の正確な定義のみから書いた全探索 DP (solve_count_dp) で、
   - 例外 m = 9 (k = 2, q = 1) のブロック 0..4（g = [11, 11, 10, 11, 11]）を直接検証
   - k = 2 (q = 0, 2, 4 の各最小例) および k = 3 (q = 0, 2 の各最小例) について
     定理 K14 の結論および中間事実（f_t in S_2 <=> v2(Y_t)+t 奇数、e_i in S_3）を全探索表上で直接検証
2. 査読済み定理 K8 の独立実装で、m <= 30000 の v2(m+1) = 1, v2(3h+1) = 2k >= 4, q = v2(Q_k) 偶数
   の全 m について、ブロック 0..4 で定理 K14 と全中間事実を検証。

実行方法:
  python code/gemini2_verify_k14.py
結果を標準出力と data/gemini2_verify_k14.txt に保存する。
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


def check_k14(m: int, S_list: list[set[int]], g_list: list[int]) -> list[str]:
    errs: list[str] = []
    h = (m + 1) // 2
    val_v2 = v2(3 * h + 1)
    k = val_v2 // 2
    w = (3 * h + 1) >> val_v2
    Qk = (m + 2 + w) // 2
    q = v2(Qk)

    if g_list[:4] != [m + 2, m + 2, m + 1, m + 2]:
        errs.append(f"g0..3 fail m={m} got={g_list[:4]}")
    want_g4 = (m + 2) if (q >= 2) else (m + 1)
    if g_list[4] != want_g4:
        errs.append(f"g4 fail m={m} q={q} got={g_list[4]} want={want_g4}")

    # Check intermediate claims: f_t in S_2 <=> v2(Y_t) + t is odd
    for t in range(1, 2 * k - 1):
        f_t = h + (w << t)
        Y_t = Qk + (w << (2 * k - t - 1))
        if (f_t in S_list[2]) != ((v2(Y_t) + t) % 2 == 1):
            errs.append(f"f_t in S_2 fail m={m} t={t}")

    # Check S_3 for e_i
    if q == 0:
        for i in range(2, 2 * k):
            e_i = w << i
            if (e_i in S_list[3]) != (i % 2 == 1):
                errs.append(f"e_i in S_3 fail m={m} i={i}")
    else:
        e_star = w << (2 * k - 1)
        if e_star in S_list[3]:
            errs.append(f"e* in S_3 fail m={m} q={q}")
    return errs


def main() -> None:
    t0 = time.perf_counter()
    lines: list[str] = []
    lines.append("=== gemini-2 独立検証: 定理 K14・系 K14.1 ===")

    # 1. Pick smallest examples for (k=2, q=0,2,4) and (k=3, q=0,2)
    targets = [(2, 0), (2, 2), (2, 4), (3, 0), (3, 2)]
    picked: list[tuple[int, int, int]] = []
    for tk, tq in targets:
        for m in range(5, 20000, 4):
            h = (m + 1) // 2
            val = v2(3 * h + 1)
            if val != 2 * tk:
                continue
            w = (3 * h + 1) >> val
            Qk = (m + 2 + w) // 2
            if v2(Qk) == tq:
                picked.append((m, tk, tq))
                break

    bf_errs: list[str] = []
    bf_states = 0

    # Exception m = 9
    tab9 = solve_count_dp(9, 200)
    bf_states += 201 * 10
    a9 = [r for r in range(201) if all(tab9[r])]
    g9 = [a9[j + 1] - a9[j] for j in range(5)]
    if g9 != [11, 11, 10, 11, 11]:
        bf_errs.append(f"m=9 g0..4 fail got={g9}")

    for m, tk, tq in picked:
        max_r = 6 * (m + 2) + 5
        tab = solve_count_dp(m, max_r)
        bf_states += (max_r + 1) * (m + 1)
        a_rows = [r for r in range(max_r + 1) if all(tab[r])]
        S_list = [
            {d for d in range(1, m + 1) if tab[a_rows[j] + d][d]}
            for j in range(5)
        ]
        g_list = [a_rows[j + 1] - a_rows[j] for j in range(5)]
        bf_errs.extend(check_k14(m, S_list, g_list))

    # 2. K8 verification for all m <= 30000 with v2(m+1)=1, v2(3h+1)=2k>=4, q even
    k8_errs: list[str] = []
    cnt = 0
    max_k = 0
    for m in range(5, 30001, 4):
        h = (m + 1) // 2
        val = v2(3 * h + 1)
        if val < 4 or val % 2 != 0:
            continue
        k = val // 2
        w = (3 * h + 1) >> val
        Qk = (m + 2 + w) // 2
        q = v2(Qk)
        if q % 2 != 0:
            continue
        cnt += 1
        if k > max_k:
            max_k = k
        S_list, g_list = run_k8_blocks(m, 5)
        k8_errs.extend(check_k14(m, S_list, g_list))

    elapsed = time.perf_counter() - t0
    lines.append(
        f"[1] 全探索検証 (m=9 例外 + 5 例 {[(m, f'k={k},q={q}') for m, k, q in picked]}; "
        f"計 {bf_states:,} 局面): 反例 {len(bf_errs)} 件"
    )
    lines.append(
        f"[2] 査読済み K8 経由検証 (m <= 30000 の該当全 {cnt} 個 [最大 k={max_k}]): 反例 {len(k8_errs)} 件"
    )
    if bf_errs or k8_errs:
        lines.append("ERRORS:")
        lines.extend((bf_errs + k8_errs)[:20])
    lines.append(f"所要時間: {elapsed:.2f} 秒")

    text = "\n".join(lines) + "\n"
    print(text, end="")
    out = Path(__file__).resolve().parent.parent / "data" / "gemini2_verify_k14.txt"
    out.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
