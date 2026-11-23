"""
gemini-2 による独立な Python 全探索ソルバーを用いた定理 K9（⇒）（必要性）の数値検証。

何を計算するか:
1. PROBLEM.md の正確な定義のみから書いた全探索 DP (solve_count_dp) で、
   v2(m+1) = 1（m ≡ 1 (mod 4)）、5 <= m <= 101（25 個の m）、0 <= r <= 3000 の全局面を計算。
2. すべての対象 m で次を検証:
   - g_0 = m + 2
   - g_1 = m + 1 ⇔ v2(3h + 1) が奇数
   - v2(3h + 1) が偶数のとき、g_0 = g_1 = m + 2 かつ (2m + 3, 0) が N（よって交互型でない）
   - 参考として、予想 K9（交互型 ⇔ v2(3h + 1) が奇数）が r <= 3000 で一致するかも記録。

実行方法:
  python code/gemini2_verify_k9_nec.py
結果を標準出力と data/gemini2_verify_k9_nec.txt に保存する。
"""

from __future__ import annotations

import time
from pathlib import Path


def v2(x: int) -> int:
    assert x > 0
    return (x & -x).bit_length() - 1


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


def main() -> None:
    t0 = time.perf_counter()
    lines: list[str] = []
    lines.append("=== gemini-2 独立検証: 定理 K9（⇒）（必要性） ===")

    ms = [m for m in range(5, 102) if v2(m + 1) == 1]
    max_r = 3000
    nec_errs: list[str] = []
    g1_errs: list[str] = []
    conj_errs: list[str] = []
    even_cnt = 0
    odd_cnt = 0
    total_states = 0

    for m in ms:
        tab = solve_count_dp(m, max_r)
        total_states += (max_r + 1) * (m + 1)
        h = (m + 1) // 2
        v3h1 = v2(3 * h + 1)
        a_rows = [r for r in range(max_r + 1) if all(tab[r])]
        g0 = a_rows[1] - a_rows[0]
        g1 = a_rows[2] - a_rows[1]

        if g0 != m + 2:
            nec_errs.append(f"g0 != m+2 at m={m}: g0={g0}")

        if v3h1 % 2 == 0:
            even_cnt += 1
            if g1 != m + 2 or tab[2 * m + 3][0] is not False:
                nec_errs.append(f"K9(=>) fail at m={m}: g1={g1}, P(2m+3,0)={tab[2*m+3][0]}")
        else:
            odd_cnt += 1
            if g1 != m + 1:
                g1_errs.append(f"g1 != m+1 at m={m}: g1={g1}")

        # 予想 K9 (r <= max_r) 参考確認
        mod = 2 * m + 3
        is_alt = all(tab[n][0] == (n % mod in (0, m + 2)) for n in range(1, max_r + 1))
        if is_alt != (v3h1 % 2 == 1):
            conj_errs.append(f"Conj K9 mismatch at m={m}")

    elapsed = time.perf_counter() - t0
    lines.append(f"検証範囲: v2(m+1) = 1, 5 <= m <= 101 ({len(ms)} 個の m), 0 <= r <= {max_r} (計 {total_states:,} 局面)")
    lines.append(f"  - v2(3h+1) 偶数: {even_cnt} 個, v2(3h+1) 奇数: {odd_cnt} 個")
    lines.append(f"  - 定理 K9（⇒）の反例: {len(nec_errs)} 件")
    lines.append(f"  - g_1 = m+1 ⇔ v2(3h+1) 奇数 の反例: {len(g1_errs)} 件")
    lines.append(f"  - [参考] 予想 K9（n <= {max_r}）の反例: {len(conj_errs)} 件")
    lines.append(f"所要時間: {elapsed:.2f} 秒")

    text = "\n".join(lines) + "\n"
    print(text, end="")
    out = Path(__file__).resolve().parent.parent / "data" / "gemini2_verify_k9_nec.txt"
    out.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
