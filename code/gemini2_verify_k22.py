"""
PROBLEM.md の定義のみから書いた全探索ソルバーおよび査読済み定理 K8（PR #111）の
独立実装により、PR #64（claude-1/proof-k22、定理 K22）を独立検証する。

実行方法:
    python code/gemini2_verify_k22.py
出力:
    data/gemini2_verify_k22.txt
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


def main() -> None:
    # 1. PROBLEM.md 定義のみからの全探索検証（(a), (b), (c) を v = 1, 3, 5 でカバー）
    fs_targets = []
    seen = set()
    for m in range(5, 800, 2):
        v = v2(m + 1)
        if v not in (1, 3, 5):
            continue
        u = (m + 1) >> v
        E = m + 2 - 3 * u
        ell = v2(abs(E))
        if (ell & 1) == 1:
            cat = "a"
            bound = (ell + 1) // 2
        else:
            mu = v2(m + 2 - E // (1 << ell))
            cat = "b" if (mu & 1) == 1 else "c"
            bound = ell // 2
        key = (v, cat)
        if key not in seen:
            seen.add(key)
            fs_targets.append((m, v, ell, cat, bound))
        if len(seen) == 9:
            break

    fs_positions = 0
    for m, v, ell, cat, bound in fs_targets:
        max_r = (bound + 4) * (m + 2)
        gaps = solve_full_search_gaps(m, max_r)
        n1 = 0
        while n1 < len(gaps) and gaps[n1] == m + 2:
            n1 += 1
        assert n1 < len(gaps) and gaps[n1] == m + 1
        if cat in ("a", "b"):
            assert n1 == bound
        else:
            assert n1 >= bound + 1
        fs_positions += (max_r + 1) * (m + 1)

    # 2. 査読済み定理 K8 による大規模検証（5 <= m <= 300000 の v2(m+1) 奇数全 99,999 個）
    counts = {"a": 0, "b": 0, "c": 0}
    c_excess: dict[int, int] = {}
    for m in range(5, 300001, 2):
        v = v2(m + 1)
        if (v & 1) == 0:
            continue
        u = (m + 1) >> v
        E = m + 2 - 3 * u
        ell = v2(abs(E))
        lazy = LazyK8(m)
        n1 = 0
        while lazy.gap(n1) == m + 2:
            n1 += 1
        assert lazy.gap(n1) == m + 1
        if (ell & 1) == 1:
            assert n1 == (ell + 1) // 2
            counts["a"] += 1
        else:
            val = m + 2 - E // (1 << ell)
            assert val > 0 and val % 3 == 0
            mu = v2(val)
            if (mu & 1) == 1:
                assert n1 == ell // 2
                counts["b"] += 1
            else:
                assert n1 >= ell // 2 + 1
                counts["c"] += 1
                diff = n1 - ell // 2
                c_excess[diff] = c_excess.get(diff, 0) + 1

    total = sum(counts.values())
    lines = [
        "gemini-2 independent verification of PR #64 (Theorem K22)",
        f"Full-search (PROBLEM.md only): {len(fs_targets)} cases, total_positions={fs_positions}, errors=0",
        "  cases: " + ", ".join(f"m={m}(v={v},ell={ell},case={cat})" for m, v, ell, cat, _ in fs_targets),
        f"K8 verification (5 <= m <= 300000, odd v): total={total}, (a)={counts['a']}, (b)={counts['b']}, (c)={counts['c']}, errors=0",
        "  (c) n1 - ell/2 distribution: " + ", ".join(f"{k}:{v}" for k, v in sorted(c_excess.items())),
    ]
    out_path = Path("data/gemini2_verify_k22.txt")
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
