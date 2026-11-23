"""
gemini-2 による独立な Python 検証: 定理 K9-25（m ≡ 25 (mod 32)）および
K9 十分性の健全な伝播による計算機証明書（5 <= m <= 1000 の全 165 個）。

何を計算するか:
1. PROBLEM.md の正確な定義のみから書いた全探索 DP (solve_count_dp) で、
   m = 25, 57, 89（t = 3, 7, 11; m ≡ 25 (mod 32)）、0 <= r <= 3000 の全局面を計算し、
   定理 K9-25（交互型）および証明内の不変量 J(j) を直接検証。
2. 健全な 3 値伝播の証明書生成器および独立検証器（条件 1〜6 の直接点検）を Python で独立実装し、
   v2(m+1) = 1 かつ v2(3h+1) が奇数の 5 <= m <= 1000（全 165 個）すべてについて
   「h in E かつ h not in O」の証明書を再計算・検証する。

実行方法:
  python code/gemini2_verify_k9_25mod32.py
結果を標準出力と data/gemini2_verify_k9_25mod32.txt に保存する。
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


def build_and_verify_k9_cert(m: int) -> tuple[bool, int]:
    """
    m (v2(m+1)=1, v2(3h+1) odd) に対し、健全な 3 値伝播で (E, O) を生成し、
    帰納法の全条件（基底 K3 整合性、各事実の非循環正当化、E[h]=1, O[h]=0）を独立検証する。
    """
    assert v2(m + 1) == 1
    h = (m + 1) // 2
    assert h % 2 == 1

    # None = Unknown, True = in S, False = not in S
    E: list[bool | None] = [None] * (m + 1)
    O: list[bool | None] = [None] * (m + 1)
    why: dict[tuple[str, int], list[tuple[str, int]]] = {}

    changed = True
    while changed:
        changed = False
        for d in range(1, m + 1):
            if E[d] is None:
                val: bool | None = None
                deps: list[tuple[str, int]] = []
                if d % 2 == 1:
                    val = True
                else:
                    x = d // 2
                    if E[x] is True:
                        val = False
                        deps = [("E", x)]
                    elif h + x <= m and O[h + x] is True:
                        val = False
                        deps = [("O", h + x)]
                    elif E[x] is False and (h + x > m or O[h + x] is False):
                        val = True
                        deps = [("E", x)] + ([("O", h + x)] if h + x <= m else [])
                k3_val = (v2(d) % 2 == 0)
                if val is not None and val == k3_val:
                    E[d] = val
                    why[("E", d)] = deps
                    changed = True

            if O[d] is None:
                val = None
                deps = []
                if d == h - 1:
                    val = False
                elif d % 2 == 1:
                    # (m + 2 + d)/2
                    e = (m + 2 + d) // 2
                    if e > m:
                        val = True
                    elif E[e] is not None:
                        val = not E[e]
                        deps = [("E", e)]
                else:
                    x = d // 2
                    if O[x] is not None:
                        val = not O[x]
                        deps = [("O", x)]
                if val is not None:
                    O[d] = val
                    why[("O", d)] = deps
                    changed = True

    if not (E[h] is True and O[h] is False):
        return False, 0

    # 独立サウンドネスチェッカ: (E, O) の全確定事実が帰納法条件 1〜6 を満たすか検証
    for d in range(1, m + 1):
        if E[d] is not None:
            # 条件 1: 基底 j=0 (K3) と一致
            assert E[d] == (v2(d) % 2 == 0), f"K3 mismatch at m={m}, d={d}"
            # 条件 3, 4: 偶数 j>=2 の H(j)(d) から正当化される（同ブロック依存は d/2 < d のみ）
            if E[d] is True:
                if d % 2 == 0:
                    x = d // 2
                    assert E[x] is False and (h + x > m or O[h + x] is False)
            else:
                assert d % 2 == 0
                x = d // 2
                assert E[x] is True or (h + x <= m and O[h + x] is True)

        if O[d] is not None:
            # 条件 5, 6: 奇数 j>=1 の H(j)(d) から正当化される（同ブロック依存は d/2 < d のみ）
            if O[d] is True:
                assert d != h - 1
                if d % 2 == 0:
                    assert O[d // 2] is False
                else:
                    e = (m + 2 + d) // 2
                    assert e > m or E[e] is False
            else:
                ok_false = False
                if d == h - 1:
                    ok_false = True
                if d % 2 == 0 and O[d // 2] is True:
                    ok_false = True
                if d % 2 == 1:
                    e = (m + 2 + d) // 2
                    if e <= m and E[e] is True:
                        ok_false = True
                assert ok_false

    # 証明書サイズ（("E", h), ("O", h) の到達可能依存事実数）
    need: set[tuple[str, int]] = set()
    stack = [("E", h), ("O", h)]
    while stack:
        node = stack.pop()
        if node in need:
            continue
        need.add(node)
        for dep in why.get(node, []):
            stack.append(dep)
    return True, len(need)


def main() -> None:
    t0 = time.perf_counter()
    lines: list[str] = []
    lines.append("=== gemini-2 独立検証: 定理 K9-25 および K9 計算機証明書 (5 <= m <= 1000) ===")

    # 1. 全探索検証: m = 25, 57, 89 (t = 3, 7, 11)
    bf_errs: list[str] = []
    bf_states = 0
    for m in (25, 57, 89):
        t = (m - 1) // 8
        h = 4 * t + 1
        x2 = 3 * t + 1
        e_star = 6 * t + 2
        z = 7 * t + 2
        max_r = 3000
        tab = solve_count_dp(m, max_r)
        bf_states += (max_r + 1) * (m + 1)
        mod = 2 * m + 3
        for n in range(1, max_r + 1):
            if tab[n][0] != (n % mod in (0, m + 2)):
                bf_errs.append(f"alt fail at m={m}, n={n}")
                break
        a_rows = [r for r in range(max_r + 1) if all(tab[r])]
        for j in range(len(a_rows) - 1):
            aj = a_rows[j]
            gj = a_rows[j + 1] - aj
            S_j = {d for d in range(1, m + 1) if tab[aj + d][d]}
            if j % 2 == 0:
                if not all(d in S_j for d in range(1, m + 1, 2)):
                    bf_errs.append(f"E1 fail m={m} j={j}")
                if x2 in S_j or e_star not in S_j or gj != m + 2:
                    bf_errs.append(f"E2/3/4 fail m={m} j={j}")
            else:
                if h in S_j or z in S_j or gj != m + 1:
                    bf_errs.append(f"O1/2/3 fail m={m} j={j}")

    # 2. 計算機証明書 (5 <= m <= 1000) の独立再計算とサウンドネス検証
    total_m = 0
    ok_m = 0
    sizes_by_mod32: dict[int, list[int]] = {}
    for m in range(5, 1001, 4):
        if v2(m + 1) != 1:
            continue
        h = (m + 1) // 2
        if v2(3 * h + 1) % 2 != 1:
            continue
        total_m += 1
        ok, sz = build_and_verify_k9_cert(m)
        if ok:
            ok_m += 1
        sizes_by_mod32.setdefault(m % 32, []).append(sz)

    elapsed = time.perf_counter() - t0
    lines.append(f"[1] 定理 K9-25 全探索検証 (m=25,57,89; 0<=r<=3000; 計 {bf_states:,} 局面): 反例 {len(bf_errs)} 件")
    lines.append(f"[2] 健全な伝播証明書の独立再計算・サウンドネス検証 (5 <= m <= 1000): {total_m} 個中 {ok_m} 個成功")
    for mod32 in sorted(sizes_by_mod32):
        szs = sizes_by_mod32[mod32]
        lines.append(f"    m ≡ {mod32:2d} (mod 32): {len(szs):3d} 個, サイズ最小={min(szs)}, 最大={max(szs)}")
    lines.append(f"所要時間: {elapsed:.2f} 秒")

    text = "\n".join(lines) + "\n"
    print(text, end="")
    out = Path(__file__).resolve().parent.parent / "data" / "gemini2_verify_k9_25mod32.txt"
    out.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
