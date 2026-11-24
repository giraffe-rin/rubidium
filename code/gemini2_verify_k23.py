"""
PROBLEM.md の定義のみから書いた全探索ソルバーおよび査読済み定理 K8（PR #111）の
独立実装により、PR #66（claude-1/k23-recursion、定理 K23）を独立検証する。

実行方法:
    python code/gemini2_verify_k23.py
出力:
    data/gemini2_verify_k23.txt
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


class LazyK8:
    def __init__(self, m: int) -> None:
        self.m = m
        self.h = (m + 1) // 2
        self.gaps: list[int] = []
        self.memo: list[dict[int, bool]] = []

    def in_S(self, J: int, x: int) -> bool:
        assert 1 <= x <= self.m
        while len(self.memo) <= J:
            self.memo.append({})
        cache = self.memo[J]
        if x in cache:
            return cache[x]
        if J == 0:
            res = (v2(x) & 1) == 0
        else:
            g = self.gap(J - 1)
            res = True
            if (x & 1) == 0 and self.in_S(J, x >> 1):
                res = False
            elif ((g + x) & 1) == 0:
                half = (g + x) >> 1
                if 1 <= half <= self.m and self.in_S(J - 1, half):
                    res = False
            if res and g == self.m + 2 and x == self.h - 1:
                res = False
        cache[x] = res
        return res

    def gap(self, J: int) -> int:
        while len(self.gaps) <= J:
            idx = len(self.gaps)
            self.gaps.append(self.m + 2 if self.in_S(idx, self.h) else self.m + 1)
        return self.gaps[J]


def compute_F(m: int, x: int, depth: int = 0) -> tuple[int, int]:
    """定理 K23 の再帰式 F(x) と再帰深さ（段数 - 1）を返す。"""
    assert depth < 100
    E = m + 2 - 3 * x
    assert E != 0
    ell = v2(abs(E))
    if (ell & 1) == 1:
        return (ell + 1) // 2, depth
    num = m + 2 - E // (1 << ell)
    assert num > 0 and num % 3 == 0
    c = num // 3
    mu = v2(c)
    if (mu & 1) == 1:
        return ell // 2, depth
    x_next = c >> mu
    assert (x_next & 1) == 1 and 1 <= x_next < (m + 2) / 3
    val, max_d = compute_F(m, x_next, depth + 1)
    return ell // 2 + val, max_d


def main() -> None:
    # 1. PROBLEM.md 定義のみからの全探索検証（depth = 0, 1, 2, 3 および例外 m = 9）
    fs_targets = []
    seen_depth = set()
    for m in range(5, 2500, 2):
        v = v2(m + 1)
        if (v & 1) == 0:
            continue
        u = (m + 1) >> v
        f_val, depth = compute_F(m, u)
        if m == 9 or (depth in (0, 1, 2, 3) and (depth, v == 1) not in seen_depth):
            if m != 9:
                seen_depth.add((depth, v == 1))
            fs_targets.append((m, v, f_val, depth))
        if len(seen_depth) >= 6:
            break

    fs_positions = 0
    m9_info = None
    for m, v, f_val, depth in fs_targets:
        max_r = (f_val + 3) * (m + 2)
        gaps = solve_full_search_gaps(m, max_r)
        n1 = 0
        while n1 < len(gaps) and gaps[n1] == m + 2:
            n1 += 1
        assert n1 < len(gaps) and gaps[n1] == m + 1
        if m == 9:
            assert n1 == 2 and f_val == 3
            m9_info = f"m=9: n1={n1}, F(u)={f_val} (expected exception)"
        else:
            assert n1 == f_val, f"FS mismatch m={m}: n1={n1}, F={f_val}"
        fs_positions += (max_r + 1) * (m + 1)

    # 2. 査読済み定理 K8 による大規模検証（5 <= m <= 300000 の v2(m+1) 奇数全 99,999 個）
    total = 0
    mismatches = []
    depth_counts: dict[int, int] = {}
    for m in range(5, 300001, 2):
        v = v2(m + 1)
        if (v & 1) == 0:
            continue
        total += 1
        u = (m + 1) >> v
        f_val, depth = compute_F(m, u)
        depth_counts[depth] = depth_counts.get(depth, 0) + 1
        lazy = LazyK8(m)
        n1 = 0
        while lazy.gap(n1) == m + 2:
            n1 += 1
        assert lazy.gap(n1) == m + 1
        if n1 != f_val:
            mismatches.append((m, n1, f_val))

    assert mismatches == [(9, 2, 3)], f"Unexpected mismatches: {mismatches}"

    lines = [
        "gemini-2 independent verification of PR #66 (Theorem K23)",
        f"Full-search (PROBLEM.md only): {len(fs_targets)} cases, total_positions={fs_positions}, non-m9 errors=0",
        f"  exception check: {m9_info}",
        "  cases: " + ", ".join(f"m={m}(v={v},F={f},d={d})" for m, v, f, d in fs_targets),
        f"K8 verification (5 <= m <= 300000, odd v): total={total}, mismatches={mismatches}",
        "  depth_counts: " + ", ".join(f"d={k}:{v}" for k, v in sorted(depth_counts.items())),
    ]
    out_path = Path("data/gemini2_verify_k23.txt")
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
