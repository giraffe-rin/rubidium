"""
PROBLEM.md の定義のみから書いた全探索ソルバー、査読済み定理 K8（PR #111）の独立実装、
および 3 値記号計算（補題 Q_s 版）の独立実装により、
PR #167（定理 K37）・PR #169（定理 K37 拡大）・PR #171（定理 K38・命題 K38c）を独立検証する。

実行方法:
    python code/gemini2_verify_k37_k38.py
出力:
    data/gemini2_verify_k37_k38.txt
"""

from pathlib import Path

T, F, U = 1, 0, 2


def neg3(x: int) -> int:
    return U if x == U else (1 - x)


def and3(a: int, b: int) -> int:
    if a == F or b == F:
        return F
    if a == T and b == T:
        return T
    return U


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


def verify_k37_symbolic_cone(v: int, K_mod: int, u0: int) -> bool:
    """K37 / K37 拡大の 3 値証明書（補題 Q_s 版）の独立遅延検証。
    u ≡ u0 (mod 2^K_mod), u0 ≡ 3 (mod 4) に対し、1 0^{(v+1)/2} が確定するかを検証する。
    """
    H = 1 << (v - 1)
    L = (v + 1) // 2
    mod_mask = (1 << K_mod) - 1
    used_max_ve = 0
    memo: dict[tuple[int, int], int] = {}

    def s1_odd(q: int) -> int:
        nonlocal used_max_ve
        # e_q = ((2^v + q)u + 1)/2. Since u >= 3, e_q <= m and q*u != h - 1.
        # Compute t = v2(q*u0 + 1) if strictly less than min(K_mod, v).
        r = (q * u0 + 1) & mod_mask
        if r == 0:
            return U  # v2(q*u + 1) >= K_mod, unknown mod 2^K_mod
        t = v2(r)
        if t >= v:
            return U  # 2^v term interferes
        ve = t - 1  # v2(e_q) = t - 1 < v - 1
        assert ve >= 0
        if ve > used_max_ve:
            used_max_ve = ve
        # In Block 0 (K3) and L-th E-type block (Q_L, limit v-1), e_q in S <=> ve even
        return F if (ve % 2 == 0) else T

    def eval_S(n: int, c: int) -> int:
        key = (n, c)
        if key in memo:
            return memo[key]
        if n == 1:
            b = v2(c)
            val = s1_odd(c >> b)
            if b & 1:
                val = neg3(val)
        else:
            if c & 1:
                val = T
            else:
                a = neg3(eval_S(n, c >> 1))
                if a == F:
                    val = F
                else:
                    val = and3(a, neg3(eval_S(n - 1, H + (c >> 1))))
        memo[key] = val
        return val

    # ブロック 1..L で h ∉ S（F）を確認
    for n in range(1, L + 1):
        if eval_S(n, H) != F:
            return False
    # ブロック L+1 は L 番目の E 型ブロック。Q_L より v2(h) = v-1 (偶数) <= min(2L-1, v-1) = v-1 なので h ∈ S。
    # 周期が閉じる条件：2*L - 1 >= used_max_ve かつ v - 1 >= used_max_ve
    return used_max_ve <= min(2 * L - 1, v - 1)


def main() -> None:
    # 1. PROBLEM.md 定義のみからの全探索検証（v = 5, 7 の K38 および K38c 代表例）
    # v=5: u=7 (w=3, m=223, 1000), u=63 (w=6 >= v+1, m=2015 -> K8+FS for smaller: u=7,23,31?)
    # v=5, u=3 (w=2, m=95 -> K38c: g_1 = m+2), u=15 (w=4, m=479 -> K38c: g_1 = m+2)
    fs_positions = 0
    for m, v in [(223, 5), (735, 5), (895, 7)]:
        L = (v + 1) // 2
        max_r = (3 * (L + 1) + 2) * (m + 2)
        gaps = solve_full_search_gaps(m, max_r)
        for j in range(3 * (L + 1)):
            expected = (m + 2) if (j % (L + 1) == 0) else (m + 1)
            assert gaps[j] == expected, f"FS K38 mismatch m={m}, j={j}"
        fs_positions += (max_r + 1) * (m + 1)
    # K38c 全探索: m=95 (v=5,u=3,w=2), m=479 (v=5,u=15,w=4), m=383 (v=7,u=3,w=2)
    for m in (95, 479, 383):
        gaps = solve_full_search_gaps(m, 4 * (m + 2))
        assert gaps[0] == m + 2 and gaps[1] == m + 2
        fs_positions += (4 * (m + 2) + 1) * (m + 1)

    # 2. K37 (K=6, 5<=v<=21) および K37 拡大 (K=9, 7<=v<=15) の独立 3 値証明書再計算
    k37_k6_ok = 0
    for v in range(5, 22, 2):
        expected_u0 = [7, 23, 39, 55] if v == 5 else [7, 23, 31, 39, 55]
        proved = [u0 for u0 in range(3, 64, 4) if verify_k37_symbolic_cone(v, 6, u0)]
        assert proved == expected_u0, f"K37 K=6 mismatch v={v}: {proved} != {expected_u0}"
        k37_k6_ok += len(proved)

    k37_k9_ok = 0
    for v in range(7, 16, 2):
        proved = [u0 for u0 in range(3, 512, 4) if verify_k37_symbolic_cone(v, 9, u0)]
        expected = [u0 for u0 in range(3, 512, 4) if v2(u0 + 1) in (3, 5, 7) and v2(u0 + 1) < v]
        assert proved == expected, f"K37 K=9 mismatch v={v}: len {len(proved)} != {len(expected)}"
        k37_k9_ok += len(proved)

    # 3. 査読済み K8 による定理 K38・命題 K38c および補題 Inh'・主張 (3H/2) の検証
    #    v = 5, 7, 9, 11、u ≡ 3 (mod 4) かつ u < 2048（w >= v+1 の場合も含む）
    k38_count = 0
    k38_big_w_count = 0
    k38c_count = 0
    for v in (5, 7, 9, 11):
        H = 1 << (v - 1)
        L = (v + 1) // 2
        for u in range(3, 2048, 4):
            w = v2(u + 1)
            m = (1 << v) * u - 1
            lazy = LazyK8(m)
            if (w % 2 == 1 and 3 <= w <= v - 2) or (w >= v + 1):
                for j in range(3 * (L + 1)):
                    expected = (m + 2) if (j % (L + 1) == 0) else (m + 1)
                    assert lazy.gap(j) == expected, f"K38 mismatch v={v}, u={u}, w={w}, j={j}"
                # ブロック 1 の (B1)(B2) と主張 S_n[3H/2] = T (1 <= n <= L-1)
                assert lazy.in_S(1, u) is False
                assert lazy.in_S(1, 3 * u) is False
                assert lazy.in_S(1, 7 * u) is False
                for n in range(1, L):
                    assert lazy.in_S(n, (3 * (H >> 1)) * u) is True
                k38_count += 1
                if w >= v + 1:
                    k38_big_w_count += 1
            elif w % 2 == 0 and 2 <= w <= v - 1:
                assert lazy.gap(1) == m + 2, f"K38c mismatch v={v}, u={u}, w={w}"
                k38c_count += 1

    lines = [
        "gemini-2 independent verification of PR #167 (K37), PR #169 (K37 ext), PR #171 (K38, K38c)",
        f"Full-search (PROBLEM.md only): 6 cases (K38: m=223,735,895; K38c: m=95,479,383), total_positions={fs_positions}, errors=0",
        f"K37 3-valued certificate recomputation: K=6 (5<=v<=21) matched {k37_k6_ok} classes, K=9 (7<=v<=15) matched {k37_k9_ok} classes, errors=0",
        f"K8 verification (v=5,7,9,11, u<2048): K38={k38_count} (including w>=v+1: {k38_big_w_count}), K38c={k38c_count}, errors=0",
    ]
    Path("data/gemini2_verify_k37_k38.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
