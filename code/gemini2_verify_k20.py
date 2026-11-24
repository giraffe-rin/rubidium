"""
PROBLEM.md の定義のみから書いた全探索ソルバーおよび査読済み定理 K8（PR #111）の
2 通りの独立実装（全配列版＋遅延評価版）により、PR #57（claude-1/proof-k20、定理 K20）を独立検証する。

実行方法:
    python code/gemini2_verify_k20.py
出力:
    data/gemini2_verify_k20.txt
"""

from pathlib import Path


def v2(x: int) -> int:
    assert x > 0
    return (x & -x).bit_length() - 1


def solve_full_search_gaps(m: int, max_r: int) -> list[int]:
    """PROBLEM.md の定義のみに基づく全探索 DP で A 行の開始局面を抽出し、間隔列を返す。"""
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


def k8_block_step_full(m: int, prev_S: bytearray | None, prev_g: int | None) -> tuple[bytearray, int]:
    """査読済み定理 K3・K8（PR #111）の全配列実装。"""
    h = (m + 1) // 2
    S = bytearray(m + 1)
    if prev_S is None:
        for x in range(1, m + 1):
            if (v2(x) & 1) == 0:
                S[x] = 1
    else:
        g = prev_g
        odd_g = (g == m + 2)
        for x in range(1, m + 1):
            if (x & 1) == 0 and S[x >> 1]:
                continue
            if ((g + x) & 1) == 0:
                half = (g + x) >> 1
                if 1 <= half <= m and prev_S[half]:
                    continue
            if odd_g and x == h - 1:
                continue
            S[x] = 1
    return S, ((m + 2) if S[h] else (m + 1))


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


def expected_period_pattern(i: int) -> list[int]:
    if i % 2 == 1:
        return [1] * (i - 1) + [0]
    return [1] * (i - 1) + [0, 0]


def check_k20_lazy(m: int, periods: int = 3, cross_check_full: bool = False) -> None:
    assert v2(m + 1) == 3
    ell = v2(5 * m + 13)
    assert ell >= 6 and ell % 2 == 0
    i = ell // 2
    u = (m + 1) // 8
    E = 5 * u + 1
    lam = ell - 3
    K = (lam - 1) // 2
    assert u % 8 == 3 and K == i - 2 >= 1

    c: dict[int, int] = {}
    d: dict[int, int] = {}
    f: dict[int, int] = {}
    for k in range(1, K + 1):
        num = (4**k) * (8 * u + 1) - E
        den = 3 * (4**k)
        assert num % den == 0
        c[k] = num // den
        assert 1 <= c[k] <= m and (c[k] & 1) == 1 and c[k] != 4 * u - 1
    for k in range(1, K + 2):
        num = (4**k) * (8 * u + 1) - E
        den = 3 * (2 ** (2 * k - 1))
        assert num % den == 0
        d[k] = num // den
        assert 1 <= d[k] <= m
        if k <= K:
            assert d[k] == 2 * c[k] and (d[k] & 1) == 0
        else:
            assert (d[k] & 1) == 1
    for r in range(0, lam):
        assert E % (1 << r) == 0
        f[r] = 8 * u + 1 - E // (1 << r)
        assert 1 <= f[r] <= m and (f[r] & 1) == 1 and f[r] != 4 * u - 1
    assert f[0] == 3 * u
    assert (m + 2 + u) == 2 * d[1]
    for k in range(1, K + 1):
        assert (m + 2 + c[k]) == 2 * d[k + 1]
    for r in range(0, lam - 1):
        assert (m + 2 + f[r]) == 2 * f[r + 1]

    pat = expected_period_pattern(i)
    L = len(pat)
    lazy = LazyK8(m)
    S_full, g_full = None, None
    for J in range(periods * L):
        g = lazy.gap(J)
        if cross_check_full:
            S_full, g_full = k8_block_step_full(m, S_full, g_full)
            assert g_full == g
        bit = 1 if g == m + 2 else 0
        n = J % L
        assert bit == pat[n], f"gap mismatch m={m}, J={J}, got {bit}, want {pat[n]}"
        if n <= i - 2:
            assert lazy.in_S(J, u) is True
            assert lazy.in_S(J, 2 * u) is False
            assert lazy.in_S(J, 4 * u) is True
            for k in range(1, min(K, K - n + 1) + 1):
                assert lazy.in_S(J, c[k]) is (k <= K - n)
            for k in range(1, K + 1 - n + 1):
                assert lazy.in_S(J, d[k]) is (k == K + 1 - n)
            assert lazy.in_S(J, f[i - 1 - n]) is (n % 2 == 0)
        elif n == i - 1:
            assert lazy.in_S(J, u) is False
            assert lazy.in_S(J, 2 * u) is True
            assert lazy.in_S(J, 4 * u) is False
            assert lazy.in_S(J, 3 * u) is (i % 2 == 1)
            assert lazy.in_S(J, 6 * u) is (i % 2 == 0)
        else:
            assert i % 2 == 0 and n == i
            assert lazy.in_S(J, 4 * u) is False
            assert lazy.in_S(J, 3 * u) is True
            assert lazy.in_S(J, 6 * u) is False


def main() -> None:
    # 1. PROBLEM.md 定義のみからの全探索検証（ℓ = 6, 8, 10 各 2 例）
    full_search_targets: list[tuple[int, int]] = []
    for target_ell in (6, 8, 10):
        found = 0
        for u in range(1, 2000, 2):
            m = 8 * u - 1
            if v2(5 * m + 13) == target_ell:
                full_search_targets.append((m, target_ell))
                found += 1
                if found == 2:
                    break

    total_fs_positions = 0
    fs_details: list[str] = []
    for m, ell in full_search_targets:
        i = ell // 2
        pat = expected_period_pattern(i)
        L = len(pat)
        max_r = (3 * L + 2) * (m + 2)
        gaps = solve_full_search_gaps(m, max_r)
        assert len(gaps) >= 3 * L
        for J in range(3 * L):
            bit = 1 if gaps[J] == m + 2 else (0 if gaps[J] == m + 1 else -1)
            assert bit == pat[J % L], f"FS mismatch m={m}, J={J}"
        total_fs_positions += (max_r + 1) * (m + 1)
        fs_details.append(f"m={m}(ell={ell},L={L},blocks={len(gaps)})")

    # 2. 査読済み定理 K8 による大規模検証（m <= 300000 の該当全 m、m <= 10000 は全配列版とも完全照合）
    k8_count = 0
    full_cross_count = 0
    max_ell = 0
    ell_counts: dict[int, int] = {}
    for m in range(7, 300001, 16):
        ell = v2(5 * m + 13)
        if ell >= 6 and ell % 2 == 0:
            cross = (m <= 10000)
            check_k20_lazy(m, periods=3, cross_check_full=cross)
            k8_count += 1
            if cross:
                full_cross_count += 1
            max_ell = max(max_ell, ell)
            ell_counts[ell] = ell_counts.get(ell, 0) + 1

    lines = [
        "gemini-2 independent verification of PR #57 (Theorem K20)",
        f"Full-search (PROBLEM.md only): {len(full_search_targets)} cases, total_positions={total_fs_positions}, errors=0",
        "  cases: " + ", ".join(fs_details),
        f"K8 + claim Q(n) verification (m <= 300000): count={k8_count} (full-table cross-check m<=10000: {full_cross_count}), max_ell={max_ell}, errors=0",
        "  counts_by_ell: " + ", ".join(f"ell={k}:{v}" for k, v in sorted(ell_counts.items())),
    ]
    out_path = Path("data/gemini2_verify_k20.txt")
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
