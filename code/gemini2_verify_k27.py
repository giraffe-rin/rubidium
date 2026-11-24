"""
PROBLEM.md の定義のみから書いた全探索ソルバーおよび査読済み定理 K8（PR #111）の
独立実装により、PR #80（claude-1/m9-by-hand、定理 K27：m = 9）を独立検証する。

実行方法:
    python code/gemini2_verify_k27.py
出力:
    data/gemini2_verify_k27.txt
"""

from pathlib import Path


def v2(x: int) -> int:
    return (x & -x).bit_length() - 1


def solve_full_search_gaps(m: int, max_r: int) -> list[int]:
    win = [[False] * (m + 1) for _ in range(max_r + 1)]
    a_rows = [0]
    for r in range(1, max_r + 1):
        limit = min(m, r)
        losing_count = 0
        only_losing_k = -1
        for k in range(1, limit + 1):
            if not win[r - k][k]:
                losing_count += 1
                only_losing_k = k
        if losing_count == 0:
            a_rows.append(r)
        elif losing_count >= 2:
            row = win[r]
            for p in range(m + 1):
                row[p] = True
        else:
            row = win[r]
            for p in range(m + 1):
                if p != only_losing_k:
                    row[p] = True
    return [a_rows[i + 1] - a_rows[i] for i in range(len(a_rows) - 1)]


def k8_step(m: int, prev_S: set[int] | None, prev_g: int | None) -> tuple[set[int], int]:
    h = (m + 1) // 2
    S: set[int] = set()
    if prev_S is None:
        for d in range(1, m + 1):
            if (v2(d) & 1) == 0:
                S.add(d)
    else:
        for d in range(1, m + 1):
            if d % 2 == 0 and (d // 2) in S:
                continue
            if (prev_g + d) % 2 == 0:
                e = (prev_g + d) // 2
                if 1 <= e <= m and e in prev_S:
                    continue
            if prev_g == m + 2 and d == h - 1:
                continue
            S.add(d)
    return S, (m + 2 if h in S else m + 1)


def main() -> None:
    m = 9
    # 1. K8 手計算表（S_0〜S_3）の完全照合
    S0, g0 = k8_step(m, None, None)
    S1, g1 = k8_step(m, S0, g0)
    S2, g2 = k8_step(m, S1, g1)
    S3, g3 = k8_step(m, S2, g2)
    assert S0 == {1, 3, 4, 5, 7, 9} and g0 == 11
    assert S1 == {1, 5, 6, 8, 9} and g1 == 11
    assert S2 == {2, 3, 8, 9} and g2 == 10
    assert S3 == S0 and g3 == g0

    # 2. PROBLEM.md 定義のみからの全探索検証（r <= 10000、100,010 局面）
    max_r = 10000
    gaps = solve_full_search_gaps(m, max_r)
    expected = [11, 11, 10]
    for j, g in enumerate(gaps):
        assert g == expected[j % 3], f"gap mismatch at j={j}: {g}"

    lines = [
        "gemini-2 independent verification of PR #80 (Theorem K27: m = 9)",
        f"K8 table exact match: S0={sorted(S0)}(g0={g0}), S1={sorted(S1)}(g1={g1}), S2={sorted(S2)}(g2={g2}), S3==S0(g3={g3})",
        f"Full-search (PROBLEM.md only): m=9, 0<=r<={max_r} ({(max_r+1)*(m+1)} positions), {len(gaps)} blocks, period=[11,11,10], errors=0",
    ]
    Path("data/gemini2_verify_k27.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
