"""
gemini-2 による独立な Python 全探索ソルバーを用いた定理 K7′（周期性）の数値検証。

何を計算するか:
1. PROBLEM.md の正確な定義のみから書いた全探索 DP (solve_count_dp) で全局面表を計算。
2. m = 1: 1 <= r <= 2000 で L(r) = {1}（r0 = 1, Λ = 1）を検証。
3. 2 <= m <= 20: ブロック状態 x_j = (S_j, g_j) を全探索表から直接読み取り、
   最初の繰り返し x_{j0} = x_{j1} から得た (r0, Λ) が
   - r0 <= 2^{m+1}(m+2), Λ <= 2^{m+1}(m+2) を満たすこと
   - すべての r0 <= r <= max_r - Λ で L(r + Λ) == L(r) であること
   を全探索表上で直接検証する。
4. 前周期のある例 m = 55 について、全探索表 (0 <= r <= 1500) 上で開始局面列の周期 169（r >= 59）を確認。

実行方法:
  python code/gemini2_verify_periodicity.py
結果を標準出力と data/gemini2_verify_periodicity.txt に保存する。
"""

from __future__ import annotations

import time
from pathlib import Path


def solve_count_dp(m: int, max_r: int) -> list[list[bool]]:
    """PROBLEM.md の定義通りの全探索 DP。is_p[r][p] == True ⇔ (r, p) が P 局面。"""
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
    lines.append("=== gemini-2 独立検証: 定理 K7′（周期性） ===")

    # m = 1
    t1 = solve_count_dp(1, 2000)
    assert t1[0] == [True, True]
    for r in range(1, 2001):
        assert t1[r] == [False, True], f"m=1 fail at r={r}"
    lines.append("m=1: 1 <= r <= 2000 ですべて L(r) = {1} (r0=1, Λ=1) -> OK")

    # 2 <= m <= 20: 全探索表からブロック状態 x_j の繰り返しを検出し L(r + Λ) == L(r) を検証
    max_r = 5000
    errs: list[str] = []
    verified_ms = 0
    for m in range(2, 21):
        tab = solve_count_dp(m, max_r)
        a_rows = [r for r in range(max_r + 1) if all(tab[r])]
        seen: dict[tuple[frozenset[int], int], int] = {}
        found_cycle = None
        for j in range(len(a_rows) - 1):
            aj = a_rows[j]
            gj = a_rows[j + 1] - aj
            sj = frozenset(d for d in range(1, m + 1) if tab[aj + d][d])
            state = (sj, gj)
            if state in seen:
                j0 = seen[state]
                j1 = j
                r0 = a_rows[j0]
                lam = a_rows[j1] - a_rows[j0]
                found_cycle = (j0, j1, r0, lam)
                break
            seen[state] = j

        if found_cycle is None:
            errs.append(f"m={m}: no cycle found within r <= {max_r}")
            continue

        j0, j1, r0, lam = found_cycle
        bound = (1 << (m + 1)) * (m + 2)
        if not (0 <= r0 <= bound and 1 <= lam <= bound):
            errs.append(f"m={m}: bound violated r0={r0}, lam={lam}, bound={bound}")
        # L(r + lam) == L(r) を max_r まで全検証
        checked_rows = 0
        for r in range(r0, max_r - lam + 1):
            if tab[r + lam] != tab[r]:
                errs.append(f"m={m}: L(r+lam) != L(r) at r={r}, lam={lam}")
                break
            checked_rows += 1
        verified_ms += 1
        lines.append(
            f"  m={m:2d}: j0={j0:2d}, j1={j1:2d}, r0={r0:4d}, Λ={lam:4d} (<= {bound}), "
            f"検証行数={checked_rows}"
        )

    # m = 55 の前周期確認 (0 <= r <= 1500)
    t55 = solve_count_dp(55, 1500)
    assert t55[58][0] != t55[58 + 169][0], "m=55 should have s(58) != s(227)"
    assert all(t55[n][0] == t55[n + 169][0] for n in range(59, 1501 - 169))
    lines.append("m=55 (前周期の例): s(58) != s(227), 59 <= n <= 1331 で周期 169 一致 -> OK")

    elapsed = time.perf_counter() - t0
    lines.append(f"検証完了 m 個数 (2 <= m <= 20): {verified_ms}/19, 反例: {len(errs)} 件, 所要時間: {elapsed:.2f} 秒")
    if errs:
        lines.append(f"[!] errors: {errs}")

    text = "\n".join(lines) + "\n"
    print(text, end="")
    out = Path(__file__).resolve().parent.parent / "data" / "gemini2_verify_periodicity.txt"
    out.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
