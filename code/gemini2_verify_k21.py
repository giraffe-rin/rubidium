"""
PROBLEM.md の定義のみから書いた全探索ソルバーおよび査読済み定理 K8（PR #111）の
独立実装により、PR #62（claude-1/proof-k21、定理 K21）を独立検証する。

実行方法:
    python code/gemini2_verify_k21.py
出力:
    data/gemini2_verify_k21.txt
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
    """査読済み定理 K3・K8（PR #111）の厳密な遅延評価実装。"""

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


def verify_k21_lazy(m: int) -> int:
    v = v2(m + 1)
    assert (v & 1) == 1
    u = (m + 1) >> v
    E = m + 2 - 3 * u
    ell = v2(abs(E))
    assert (ell & 1) == 1
    K = (ell - 1) // 2
    lazy = LazyK8(m)
    for j in range(K + 1):
        assert lazy.gap(j) == m + 2
    assert lazy.gap(K + 1) == m + 1

    if v >= 3:
        h = (m + 1) // 2
        c = {}
        d = {}
        for k in range(1, K + 1):
            num = (4**k) * (m + 2) - E
            den = 3 * (4**k)
            assert num % den == 0
            c[k] = num // den
            assert 1 <= c[k] <= m and (c[k] & 1) == 1 and c[k] != h - 1
        for k in range(1, K + 2):
            num = (4**k) * (m + 2) - E
            den = 3 * (2 ** (2 * k - 1))
            assert num % den == 0
            d[k] = num // den
            assert 1 <= d[k] <= m
        for n in range(K + 1):
            assert lazy.in_S(n, u) is True and lazy.in_S(n, h) is True
            for k in range(1, min(K, K - n + 1) + 1):
                assert lazy.in_S(n, c[k]) is (k <= K - n)
            for k in range(1, K + 1 - n + 1):
                assert lazy.in_S(n, d[k]) is (k == K + 1 - n)
        assert lazy.in_S(K + 1, u) is False and lazy.in_S(K + 1, h) is False
    return ell


def main() -> None:
    # 1. PROBLEM.md 定義のみからの全探索検証（v = 1, 3, 5, 7 で ell = 1, 3, 5, 7 をカバー）
    fs_targets = []
    for target_v in (1, 3, 5, 7):
        seen_ell = set()
        for u in range(1, 300, 2):
            m = (1 << target_v) * u - 1
            if m < 5 or m > 1200:
                continue
            E = m + 2 - 3 * u
            ell = v2(abs(E))
            if (ell & 1) == 1 and ell not in seen_ell:
                seen_ell.add(ell)
                fs_targets.append((m, target_v, ell))
                if len(seen_ell) >= 3:
                    break

    fs_positions = 0
    for m, v, ell in fs_targets:
        K = (ell - 1) // 2
        max_r = (K + 3) * (m + 2)
        gaps = solve_full_search_gaps(m, max_r)
        assert len(gaps) >= K + 2
        for j in range(K + 1):
            assert gaps[j] == m + 2
        assert gaps[K + 1] == m + 1
        fs_positions += (max_r + 1) * (m + 1)

    # 2. 査読済み定理 K8 による大規模検証（5 <= m <= 300000 の該当全 m）
    total_k8 = 0
    v_counts: dict[int, int] = {}
    max_ell = 0
    for m in range(5, 300001, 2):
        v = v2(m + 1)
        if (v & 1) == 0:
            continue
        u = (m + 1) >> v
        E = m + 2 - 3 * u
        ell = v2(abs(E))
        if (ell & 1) == 1:
            verify_k21_lazy(m)
            total_k8 += 1
            v_counts[v] = v_counts.get(v, 0) + 1
            if ell > max_ell:
                max_ell = ell

    lines = [
        "gemini-2 independent verification of PR #62 (Theorem K21)",
        f"Full-search (PROBLEM.md only): {len(fs_targets)} cases, total_positions={fs_positions}, errors=0",
        "  cases: " + ", ".join(f"m={m}(v={v},ell={ell})" for m, v, ell in fs_targets),
        f"K8 + claim Q(n) verification (5 <= m <= 300000): count={total_k8}, max_ell={max_ell}, errors=0",
        "  counts_by_v: " + ", ".join(f"v={k}:{v}" for k, v in sorted(v_counts.items())),
    ]
    out_path = Path("data/gemini2_verify_k21.txt")
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
