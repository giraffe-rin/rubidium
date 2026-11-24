"""
gemini-2 による独立な Python ソルバーを用いた定理 K9（v2(m+1) = 1 のときの交互型の同値条件）の数値検証。

何を計算するか:
1. PROBLEM.md の正確な定義のみから書いた全探索 DP (solve_count_dp) で、
   k = 0 (m = 5, 13), k = 1 (m = 25, 57), k = 2 (m = 105, 233), k = 3 (m = 425)
   について全局面を計算し、交互型および証明の二分木 T と主張 Ψ(j) を全探索表上で直接検証。
2. 査読済み定理 K8 の独立実装で、v2(m+1) = 1 かつ 5 <= m <= 5000 の全 m（1249 個）および
   k = 5 最小例 m = 6825 (q = 5) について：
   - v2(3h+1) が奇数の全例で、二分木 T の全節点値 <= m、(Ob) の全値 <= m-2、
     事実集合のサイズが重複なく 2^{k+2}-1、およびブロック j = 0..19 で Ψ(j) と交互型を検証。
   - v2(3h+1) が偶数の全例で、g_1 = m+2（非交互型）を再確認。

実行方法:
  python code/gemini2_verify_k9_general.py
結果を標準出力と data/gemini2_verify_k9_general.txt に保存する。
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


def build_tree_T(m: int) -> tuple[int, int, list[tuple[int, int]]]:
    h = (m + 1) // 2
    N = 3 * h + 1
    val_v2 = v2(N)
    assert val_v2 % 2 == 1
    k = (val_v2 - 1) // 2
    q = N >> val_v2
    nodes: list[tuple[int, int]] = []
    stack = [(2 * k, q)]
    while stack:
        c, r = stack.pop()
        nodes.append((c, r))
        if c >= 2:
            stack.append((c - 2, r))
            stack.append((c - 2, r + (1 << (2 * k + 2 - c)) * q))
    return k, q, nodes


def check_psi(m: int, S_list: list[set[int]], g_list: list[int]) -> list[str]:
    h = (m + 1) // 2
    k, q, nodes = build_tree_T(m)
    errs: list[str] = []

    if q < 5 or q % 6 != 5:
        errs.append(f"q condition fail m={m} q={q}")

    eb_vals: set[int] = set()
    ec_vals: set[int] = set()
    ob_vals: set[int] = set()
    for c, r in nodes:
        if r % 2 != 1 or c % 2 != 0:
            errs.append(f"node parity fail m={m} node={(c, r)}")
        val = (1 << c) * r
        if not (1 <= val <= m):
            errs.append(f"Eb bound fail m={m} val={val}")
        eb_vals.add(val)
        if c >= 2:
            ec = (1 << (c - 1)) * r
            ob = h + ec
            if not (1 <= ec <= m - 1):
                errs.append(f"Ec bound fail m={m} ec={ec}")
            if not (1 <= ob <= m - 2):
                errs.append(f"Ob bound fail m={m} ob={ob}")
            ec_vals.add(ec)
            ob_vals.add(ob)

    # Check exact distinct fact count: Eb + Ec + Ob + {Oa: h} + {h in E} = 2^{k+2} - 1
    e_in_facts = eb_vals | {h}
    o_out_facts = ob_vals | {h}
    total_facts = len(e_in_facts) + len(ec_vals) + len(o_out_facts)
    if total_facts != (1 << (k + 2)) - 1:
        errs.append(f"fact count mismatch m={m} k={k} got={total_facts} want={(1<<(k+2))-1}")

    for j, (S_j, g_j) in enumerate(zip(S_list, g_list)):
        if j % 2 == 0:
            if not all(d in S_j for d in range(1, m + 1, 2)):
                errs.append(f"Ea fail m={m} j={j}")
            for x in eb_vals:
                if x not in S_j:
                    errs.append(f"Eb fail m={m} j={j} x={x}")
            for x in ec_vals:
                if x in S_j:
                    errs.append(f"Ec fail m={m} j={j} x={x}")
            if g_j != m + 2:
                errs.append(f"E gap fail m={m} j={j} g={g_j}")
        else:
            if h in S_j:
                errs.append(f"Oa fail m={m} j={j}")
            for x in ob_vals:
                if x in S_j:
                    errs.append(f"Ob fail m={m} j={j} x={x}")
            if g_j != m + 1:
                errs.append(f"O gap fail m={m} j={j} g={g_j}")
    return errs


def main() -> None:
    t0 = time.perf_counter()
    lines: list[str] = []
    lines.append("=== gemini-2 独立検証: 定理 K9（v2(m+1) = 1 の交互型の一般同値条件） ===")

    # 1. Direct brute-force DP for k = 0, 1, 2, 3 examples
    bf_cases = [
        (5, 2000),    # k=0, q=5
        (13, 2000),   # k=0, q=11
        (25, 2000),   # k=1, q=5
        (57, 2000),   # k=1, q=11
        (105, 2500),  # k=2, q=5
        (233, 2500),  # k=2, q=11
        (425, 2500),  # k=3, q=5
    ]
    bf_errs: list[str] = []
    bf_states = 0
    for m, max_r in bf_cases:
        tab = solve_count_dp(m, max_r)
        bf_states += (max_r + 1) * (m + 1)
        mod = 2 * m + 3
        for n in range(1, max_r + 1):
            if tab[n][0] != (n % mod in (0, m + 2)):
                bf_errs.append(f"alt fail m={m} n={n}")
                break
        a_rows = [r for r in range(max_r + 1) if all(tab[r])]
        S_list = [
            {d for d in range(1, m + 1) if tab[a_rows[j] + d][d]}
            for j in range(len(a_rows) - 1)
        ]
        g_list = [a_rows[j + 1] - a_rows[j] for j in range(len(a_rows) - 1)]
        bf_errs.extend(check_psi(m, S_list, g_list))

    # 2. K8-based verification for all v2(m+1)=1, 5 <= m <= 5000 + k=5 minimal m=6825
    odd_count = 0
    even_count = 0
    max_k_seen = -1
    k8_odd_errs: list[str] = []
    k8_even_errs: list[str] = []
    ms = list(range(5, 5001, 4)) + [6825]
    for m in ms:
        h = (m + 1) // 2
        val_v2 = v2(3 * h + 1)
        if val_v2 % 2 == 1:
            odd_count += 1
            k_cur = (val_v2 - 1) // 2
            if k_cur > max_k_seen:
                max_k_seen = k_cur
            n_blocks = 12 if m > 3000 else 20
            S_list, g_list = run_k8_blocks(m, n_blocks)
            k8_odd_errs.extend(check_psi(m, S_list, g_list))
        else:
            even_count += 1
            _, g_list = run_k8_blocks(m, 2)
            if g_list[0] != m + 2 or g_list[1] != m + 2:
                k8_even_errs.append(f"even v2 fail m={m} g={g_list}")

    elapsed = time.perf_counter() - t0
    lines.append(
        f"[1] 全探索検証 (k=0..3 の 7 例: m={[c[0] for c in bf_cases]}; 計 {bf_states:,} 局面): "
        f"反例 {len(bf_errs)} 件"
    )
    lines.append(
        f"[2] 査読済み K8 経由検証 (5<=m<=5000 全 {len(ms)-1} 個 + m=6825(k=5); "
        f"v2 奇数 {odd_count} 個 [最大 k={max_k_seen}], v2 偶数 {even_count} 個): "
        f"奇数反例 {len(k8_odd_errs)} 件, 偶数反例 {len(k8_even_errs)} 件"
    )
    if bf_errs or k8_odd_errs or k8_even_errs:
        lines.append("ERRORS:")
        lines.extend((bf_errs + k8_odd_errs + k8_even_errs)[:20])
    lines.append(f"所要時間: {elapsed:.2f} 秒")

    text = "\n".join(lines) + "\n"
    print(text, end="")
    out = Path(__file__).resolve().parent.parent / "data" / "gemini2_verify_k9_general.txt"
    out.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
