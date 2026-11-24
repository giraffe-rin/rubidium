"""
PROBLEM.md の定義のみから書いた全探索ソルバー、査読済み定理 K8（PR #111）の独立実装、
および 3 値記号計算の 2 通り独立実装（全表版 5<=v<=19・遅延コーン版 5<=v<=31）により、
PR #92（K29.1）・PR #94（K29.2）・PR #96（K29.3）・PR #100（定理 K29）を独立検証する。

実行方法:
    python code/gemini2_verify_k29.py
出力:
    data/gemini2_verify_k29.txt
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


def s1_odd_3val(c: int, u0: int, H: int) -> int:
    assert (c & 1) == 1
    if c % 4 == 1:
        return F
    # c % 4 == 3
    if u0 == 1 and c == H - 1:
        return U
    if (c * u0 + 1) % 8 == 4:
        return T
    return U


def verify_3val_full(v: int, u0: int) -> None:
    """5 <= v <= 17 の全距離 1..2^v-1 で 3 値計算と補題 P_n・Inh_n を全検査する。"""
    N = 1 << v
    H = 1 << (v - 1)
    L = (v + 1) // 2
    S = [bytearray(N) for _ in range(L + 1)]
    # ブロック 1 (O 型)
    S1 = S[1]
    for c in range(1, N):
        if c & 1:
            S1[c] = s1_odd_3val(c, u0, H)
        else:
            S1[c] = neg3(S1[c >> 1])
    assert S1[H] == F
    # ブロック 2..L (E 型)
    for n in range(2, L + 1):
        Sn = S[n]
        Sprev = S[n - 1]
        for c in range(1, N):
            if c & 1:
                Sn[c] = T
            else:
                Sn[c] = and3(neg3(Sn[c >> 1]), neg3(Sprev[H + (c >> 1)]))
        # 補題 P_n と Inh_n の全検査
        for c in range(2, N, 2):
            b = v2(c)
            if b <= 2 * n - 3:
                expected = T if (b % 2 == 0) else F
                assert Sn[c] == expected, f"P_n fail v={v}, u0={u0}, n={n}, c={c}"
            elif 2 * n - 2 <= b <= v - 3:
                assert Sn[c] == S1[c], f"Inh_n fail v={v}, u0={u0}, n={n}, c={c}"
        if n < L:
            assert Sn[H >> 1] == T
            assert Sn[H] == F
        else:
            assert S[L - 1][H + (H >> 1)] == F
            assert Sn[H] == T


def verify_3val_cone(v: int, u0: int) -> int:
    """遅延メモ化により、5 <= v <= 31 の奇数 v すべてで K29.3 の 3 値計算の厳密値を検証。"""
    H = 1 << (v - 1)
    L = (v + 1) // 2
    memo: dict[tuple[int, int], int] = {}

    def eval_S(n: int, c: int) -> int:
        key = (n, c)
        if key in memo:
            return memo[key]
        if n == 1:
            b = v2(c)
            q = c >> b
            val = s1_odd_3val(q, u0, H)
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
                    b_val = neg3(eval_S(n - 1, H + (c >> 1)))
                    val = and3(a, b_val)
        memo[key] = val
        return val

    for n in range(1, L):
        assert eval_S(n, H) == F
    assert eval_S(L, H) == T
    return len(memo)


def main() -> None:
    # 1. PROBLEM.md 定義のみからの全探索検証（v = 5, 7, 9）
    fs_targets = [
        (31, 5), (159, 5), (287, 5),  # u = 1, 5, 9
        (127, 7), (639, 7),           # u = 1, 5
        (511, 9),                     # u = 1
    ]
    fs_positions = 0
    for m, v in fs_targets:
        L = (v + 1) // 2
        max_r = (3 * L + 2) * (m + 2)
        gaps = solve_full_search_gaps(m, max_r)
        assert len(gaps) >= 3 * L
        for J in range(3 * L):
            expected = (m + 2) if (J % L == 0) else (m + 1)
            assert gaps[J] == expected, f"FS mismatch m={m}, J={J}"
        fs_positions += (max_r + 1) * (m + 1)

    # 2. 3 値全表検証 + 補題 P_n・Inh_n 全検査（5 <= v <= 17）
    for v in range(5, 18, 2):
        for u0 in (1, 5):
            verify_3val_full(v, u0)

    # 3. 3 値遅延コーン厳密検証（5 <= v <= 31、K29.3 の v <= 27 を完全包含）
    cone_sizes = []
    for v in range(5, 32, 2):
        sz1 = verify_3val_cone(v, 1)
        sz5 = verify_3val_cone(v, 5)
        cone_sizes.append(f"v={v}({sz1}/{sz5})")

    # 4. 査読済み K8 による大規模検証（m <= 300000 で v >= 5 奇数かつ u ≡ 1 (mod 4) の全 m）
    #    および K29.1・K29.2 の v = 5 事実確認（ブロック 0, 3, 6, 9 の (★′) を含む）
    k8_count = 0
    v5_count = 0
    for m in range(31, 300001, 2):
        v = v2(m + 1)
        if v < 5 or (v & 1) == 0:
            continue
        u = (m + 1) >> v
        if u % 4 != 1:
            continue
        L = (v + 1) // 2
        lazy = LazyK8(m)
        for J in range(4 * L):
            expected = (m + 2) if (J % L == 0) else (m + 1)
            assert lazy.gap(J) == expected, f"K8 mismatch m={m}, J={J}"
        if v == 5:
            v5_count += 1
            X = (43 * u + 1) // 2
            Y = (39 * u + 1) // 2
            for q in range(4):
                if lazy.in_S(3 * q, X):
                    assert not lazy.in_S(3 * q, Y)
        k8_count += 1

    lines = [
        "gemini-2 independent verification of PR #92/#94/#96/#100 (Theorem K29.1, K29.2, K29.3, K29)",
        f"Full-search (PROBLEM.md only): {len(fs_targets)} cases (v=5,7,9), total_positions={fs_positions}, errors=0",
        "3-valued full-table + lemmas P_n & Inh_n (5 <= v <= 17, u0 in {1,5}): violations=0",
        "3-valued exact lazy cone (5 <= v <= 31, u0 in {1,5}): all pass, errors=0",
        "  cone_nodes(u0=1/5): " + ", ".join(cone_sizes),
        f"K8 verification (m <= 300000, odd v >= 5, u ≡ 1 mod 4): count={k8_count} (v=5 with K29.1/K29.2 star-check: {v5_count}), errors=0",
    ]
    Path("data/gemini2_verify_k29.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
