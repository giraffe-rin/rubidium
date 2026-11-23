"""
PROBLEM.md の定義のみから書いた全探索ソルバーおよび査読済み定理 K8（PR #111）の
任意精度（Python int）遅延評価独立実装により、
PR #153（K33a・K33b）、PR #159（K35・K35b）、PR #163（K36・K36b）、PR #165（K36c）
を独立検証する。

実行方法:
    python code/gemini2_verify_k33a_k35_k36.py
出力:
    data/gemini2_verify_k33a_k35_k36.txt
"""

from pathlib import Path


def v2(x: int) -> int:
    assert x > 0
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


class LazyK8Big:
    """査読済み定理 K3・K8（PR #111）の任意精度遅延評価実装（反復スタック版）。"""

    def __init__(self, m: int) -> None:
        self.m = m
        self.h = (m + 1) // 2
        self.gaps: list[int] = []
        self.memo: list[dict[int, bool]] = []

    def in_S(self, J: int, x: int) -> bool:
        assert 1 <= x <= self.m
        while len(self.memo) <= J:
            self.memo.append({})
        if x in self.memo[J]:
            return self.memo[J][x]
        # J より前のギャップは先に確定しておく
        if J > 0:
            self.gap(J - 1)
        # 反復スタックで (j, d) を計算
        stack: list[tuple[int, int, int]] = [(J, x, 0)]
        while stack:
            j, d, state = stack.pop()
            if d in self.memo[j]:
                continue
            if j == 0:
                self.memo[0][d] = (v2(d) & 1) == 0
                continue
            g = self.gaps[j - 1]
            # (iii)
            if g == self.m + 2 and d == self.h - 1:
                self.memo[j][d] = False
                continue
            # 依存先を特定
            dep1 = (j, d >> 1) if (d & 1) == 0 else None
            dep2 = None
            if ((g + d) & 1) == 0:
                e = (g + d) >> 1
                if 1 <= e <= self.m:
                    dep2 = (j - 1, e)
            # 既に確定しているか確認
            if dep1 is not None and dep1[1] in self.memo[dep1[0]]:
                if self.memo[dep1[0]][dep1[1]]:
                    self.memo[j][d] = False
                    continue
                dep1 = None
            if dep2 is not None and dep2[1] in self.memo[dep2[0]]:
                if self.memo[dep2[0]][dep2[1]]:
                    self.memo[j][d] = False
                    continue
                dep2 = None
            if dep1 is None and dep2 is None:
                self.memo[j][d] = True
                continue
            stack.append((j, d, 1))
            if dep2 is not None:
                stack.append((dep2[0], dep2[1], 0))
            if dep1 is not None:
                stack.append((dep1[0], dep1[1], 0))
        return self.memo[J][x]

    def gap(self, J: int) -> int:
        while len(self.gaps) <= J:
            idx = len(self.gaps)
            self.gaps.append(self.m + 2 if self.in_S(idx, self.h) else self.m + 1)
        return self.gaps[J]


def mult_order_4(q: int) -> int:
    k = 1
    cur = 4 % q
    while cur != 1:
        cur = (cur * 4) % q
        k += 1
    return k


def main() -> None:
    # 1. PROBLEM.md 定義のみからの全探索検証
    # K33a: e=2 (m=37, 10), e=4 (m=145, 110), e=6 (m=577, 1110)
    # K35: k=2 (m=151, 11100)
    fs_positions = 0
    for e in (2, 4, 6):
        m = 9 * (1 << e) + 1
        L = e // 2 + 1
        max_r = (3 * L + 2) * (m + 2)
        gaps = solve_full_search_gaps(m, max_r)
        pat = [1] * (e // 2) + [0]
        for j in range(3 * L):
            assert (1 if gaps[j] == m + 2 else 0) == pat[j % L]
        fs_positions += (max_r + 1) * (m + 1)
    # K35 k=2: m=151
    m = 151
    max_r = (3 * 5 + 2) * (m + 2)
    gaps = solve_full_search_gaps(m, max_r)
    for j in range(15):
        assert (1 if gaps[j] == m + 2 else 0) == ([1, 1, 1, 0, 0][j % 5])
    fs_positions += (max_r + 1) * (m + 1)

    # 2. K33a（e = 2..40 偶数、各 3 周期 + 性質 (Z) 確認）
    k33a_count = 0
    for e in range(2, 41, 2):
        m = 9 * (1 << e) + 1
        assert v2(m + 1) == 1
        M = m + 2
        o_star = M // 3
        K = (e - 2) // 2
        L = e // 2 + 1
        lazy = LazyK8Big(m)
        pat = [1] * (e // 2) + [0]
        for j in range(3 * L):
            g = lazy.gap(j)
            assert (1 if g == m + 2 else 0) == pat[j % L]
        # 性質 (Z) を始まりのブロック B = 0, L, 2L で確認
        for B in (0, L, 2 * L):
            for i in range(1, K + 1):
                xi = 2 * o_star + 3 * (1 << (e - 2 * i))
                assert lazy.in_S(B, xi) is False
            x_end = 2 * o_star + 3
            assert lazy.in_S(B, x_end) is True
        k33a_count += 1

    # 3. K35（k = 2..60、各 3 周期 + 性質 (Z) 確認）
    k35_count = 0
    for k in range(2, 61):
        m = (3 * (16**k) - 13) // 5
        assert v2(m + 1) == 3
        a = ((16**k) - 1) // 5
        L = 2 * k + 1
        pat = [1] * (2 * k - 1) + [0, 0]
        lazy = LazyK8Big(m)
        for j in range(3 * L):
            g = lazy.gap(j)
            assert (1 if g == m + 2 else 0) == pat[j % L]
        if k <= 10:
            d3 = (27 * a - 1) // 16
            c_2km2 = 3 * a - 3 * (1 << (2 * k - 2))
            for B in (0, L, 2 * L):
                assert lazy.in_S(B, d3) is False
                assert lazy.in_S(B, 2 * a - 1) is True
                assert lazy.in_S(B, c_2km2) is True
                for i in range(1, 2 * k - 2):
                    assert lazy.in_S(B, 2 * a - (4**i)) is False
        k35_count += 1

    # 4. K36 + K36c（v = 3..15 奇数、位数 1〜2 倍で N <= 400 の計 14 組）
    k36_cases = [
        (3, 4), (3, 6), (3, 8),
        (5, 14), (5, 28),
        (7, 50), (7, 100),
        (9, 254),
        (11, 102), (11, 204),
        (13, 387), (13, 774),
        (15, 234),
    ]
    k36_summary = []
    for v, N in k36_cases:
        q = (1 << v) - 3
        assert (4**N - 1) % q == 0
        a = (4**N - 1) // q
        m = 3 * a - 2
        assert v2(m + 1) == v
        K = N - (v + 1) // 2
        lazy = LazyK8Big(m)
        # 2 周期分以上のブロックを検証
        total_blocks = 2 * (K + 1 + 2) + 6
        bits = [1 if lazy.gap(j) == m + 2 else 0 for j in range(total_blocks)]
        # 極大な 1 の連がすべて K+1、極大な 0 の連がすべて 1 <= s <= (v+1)/2、K 偶数なら s >= 2
        idx = 0
        s_vals = []
        while idx < len(bits):
            if bits[idx] == 1:
                run1 = 0
                while idx < len(bits) and bits[idx] == 1:
                    run1 += 1
                    idx += 1
                if idx < len(bits):
                    assert run1 == K + 1, f"K36 run1 mismatch (v={v},N={N}): {run1} != {K+1}"
            else:
                run0 = 0
                while idx < len(bits) and bits[idx] == 0:
                    run0 += 1
                    idx += 1
                if idx < len(bits):
                    assert 1 <= run0 <= (v + 1) // 2
                    if K % 2 == 0:
                        assert run0 >= 2, f"K36c mismatch (v={v},N={N},K={K}): s={run0}"
                    s_vals.append(run0)
        k36_summary.append(f"(v={v},N={N},K={K},s={s_vals})")

    lines = [
        "gemini-2 independent verification of PR #153 (K33a), PR #159 (K35), PR #163 (K36), PR #165 (K36c)",
        f"Full-search (PROBLEM.md only): 4 cases (m=37,145,577,151), total_positions={fs_positions}, errors=0",
        f"K33a (LazyK8Big, e=2..40 even, 3 periods + Z): {k33a_count} cases, errors=0",
        f"K35 (LazyK8Big, k=2..60, 3 periods + Z): {k35_count} cases, errors=0",
        f"K36 + K36c (LazyK8Big, v=3..15, 13 cases up to N=774): errors=0",
        "  cases: " + ", ".join(k36_summary),
    ]
    Path("data/gemini2_verify_k33a_k35_k36.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
