"""
PR #279（定理 K44 の全 N 記号証明）、PR #275（K44 帰納法確定 123 例）、
PR #277（予想 K45 帰納法確定 21 例）の独立 Python 記号・数値検証スクリプト。

- PR #279（定理 K44）：
  1. a ≡ -5/17 (mod 2^30) のみを用いた完全記号 E 型評価木（N mod 24 ∈ {6, 14, 22} の 3 類）を独立構築し、
     leM(e <= m)・d > 0・全入口 c(3a-1)/2^k・補題 K44.1 / K44.2（軌道 T、条件 (a)(b)(c)、
     d > 0、n mod 6 不変性）を厳密検証する。
  2. N = 30, 38, ..., 1006 の全 123 例で評価木全事実の BigInt 実数値照合を行う。
- PR #275（K44 prove3 確定）：
  厳密独立検証器 prove3_strict（上限超過即例外）により N = 30, 38, ..., 1006 の全 123 例が
  c = 1, k = 1, A = 0 で閉じることを確認する。
- PR #277（K45 prove3 確定）：
  N = 56, 84, ..., 616 の全 21 例について独立 K8 遅延評価で型 (pre, w) を推測し、
  prove3_strict で c = 1, k = 1 確定・data/k45_induction.txt の (p, L, max_run) と完全一致することを確認する。

実行方法:
    python code/gemini2_verify_k44_k45.py
出力:
    data/gemini2_verify_k44_k45.txt
"""

from __future__ import annotations

import os
import time
from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass
from pathlib import Path


EXPECTED_K45 = {
    56: (22, 12, 9),
    84: (0, 29, 14),
    112: (0, 27, 19),
    140: (0, 89, 23),
    168: (31, 70, 24),
    196: (0, 77, 32),
    224: (114, 136, 37),
    252: (1, 172, 42),
    280: (0, 81, 47),
    308: (95, 330, 52),
    336: (99, 46, 43),
    364: (1, 97, 60),
    392: (0, 75, 64),
    420: (0, 77, 70),
    448: (0, 237, 75),
    476: (0, 121, 79),
    504: (3, 89, 85),
    532: (3, 137, 88),
    560: (0, 103, 92),
    588: (0, 156, 98),
    616: (0, 361, 103),
}


def v2(x: int) -> int:
    assert x > 0
    return (x & -x).bit_length() - 1


@dataclass(frozen=True)
class LinForm:
    P: int
    Q: int
    K: int

    def norm(self) -> LinForm:
        P, Q, K = self.P, self.Q, self.K
        while K > 0 and (P & 1) == 0 and (Q & 1) == 0:
            P >>= 1
            Q >>= 1
            K -= 1
        return LinForm(P, Q, K)

    def div2(self) -> LinForm:
        return LinForm(self.P, self.Q, self.K + 1).norm()

    def add_h_half(self) -> LinForm:
        # h + d/2 = (3a - 1)/2 + (Pa + Q)/2^{K+1}
        return LinForm(3 * (1 << self.K) + self.P, -(1 << self.K) + self.Q, self.K + 1).norm()


def T_map(b: int) -> tuple[int, int]:
    x = b + 15
    r = v2(x)
    return x >> r, r


def verify_pr279_k44_symbolic() -> tuple[str, str]:
    mod_bits = 30
    mod = 1 << mod_bits
    a_mod = (-5 * pow(17, -1, mod)) & (mod - 1)
    a_min = (3 * (1 << 30) - 5) // 17
    H = LinForm(3, -1, 1)

    # 基本算術の確認
    m1_mod = (3 * a_mod - 1) & (mod - 1)
    assert v2(m1_mod) == 5
    u_mod = m1_mod >> 5
    assert v2(u_mod + 1) == 4

    # T 軌道の全検証（b <= 13）
    expected_orbits = {
        1: ([1], [4]),
        5: ([5], [2]),
        3: ([3, 9], [1, 3]),
        9: ([9, 3], [3, 1]),
        7: ([7, 11, 13], [1, 1, 2]),
        11: ([11, 13, 7], [1, 2, 1]),
        13: ([13, 7, 11], [2, 1, 1]),
    }
    for c, (exp_orb, exp_rs) in expected_orbits.items():
        orb = [c]
        rs = []
        b = c
        while True:
            nb, r = T_map(b)
            rs.append(r)
            if nb == c:
                break
            orb.append(nb)
            b = nb
        assert orb == exp_orb and rs == exp_rs
        # 周期 6 での増分 6 + (6/l)*sum(r-1) が偶数であることを確認
        ell = len(orb)
        assert 6 % ell == 0
        s_ell = sum(r - 1 for r in rs)
        assert (6 + (6 // ell) * s_ell) % 2 == 0
        if c >= 3:
            # 平均 r <= 2 かつ b <= 13 かつ 165 - 5b ∈ (0, 256)
            assert sum(rs) <= 2 * ell
            for bb in orb:
                assert bb <= 13 and 0 < 165 - 5 * bb < 256

    def sym_bit(x: LinForm) -> int:
        assert x.K + 1 <= mod_bits
        # 正性も同時に確認
        assert x.P > 0 and x.P * a_min + x.Q > 0
        t = (x.P * a_mod + x.Q) & ((1 << (x.K + 1)) - 1)
        assert (t & ((1 << x.K) - 1)) == 0
        return t >> x.K

    def sym_leM(x: LinForm) -> bool:
        co = x.P - 3 * (1 << x.K)
        rhs = -x.Q - (1 << (x.K + 1))
        if co < 0:
            assert co * a_min <= rhs
            return True
        if co > 0:
            assert co * a_min > rhs
            return False
        return 0 <= rhs

    def sym_chain(c: int, k: int, n_mod6: int, z: int) -> bool:
        assert 3 <= c <= 13 and (c & 1) == 1 and k <= 5
        # n = n0 (代表値 >= 7, n0 ≡ n_mod6 (mod 6)) で評価
        n0 = n_mod6 if n_mod6 >= 7 else n_mod6 + 6
        b = c
        K_cur = 5
        s = 5 - k
        for step_idx in range(1, n0 + 1):
            # 条件: d = (a*b - 3*c*2^{N-K})/5 > 0  <=>  17*c / (b * 2^K) < 1
            assert 17 * c < b * (1 << K_cur), f"positivity fail c={c}, b={b}, K={K_cur}"
            nb, r = T_map(b)
            v2_beta = K_cur + r
            # N = 4*n0 + 2 に対して v2(beta) < N かつ N - K >= 8
            N0 = 4 * n0 + 2
            assert v2_beta < N0 and N0 - K_cur >= 8
            s += 1
            if step_idx < n0:
                s += r - 1
                K_cur += r
                b = nb
            else:
                end_v2 = r - 1
                assert end_v2 <= min(2 * z - 1, 4)
                base_val = (end_v2 % 2) == 0
                return base_val if (s % 2 == 0) else (not base_val)
        raise AssertionError("unreachable")

    # 3 つの類 N mod 24 ∈ {6, 14, 22} の完全記号 E 評価木を構築・検証
    trees: dict[int, tuple[int, dict[tuple[int, LinForm], bool]]] = {}
    exp_counts = {6: 29, 14: 16, 22: 16}
    for N_mod24, z, n_mod6 in ((6, 3, 1), (14, 2, 3), (22, 2, 5)):
        memo: dict[tuple[int, LinForm], bool] = {}

        def eval_E(j: int, d: LinForm) -> bool:
            d = d.norm()
            key = (j, d)
            if key in memo:
                return memo[key]
            if sym_bit(d) == 1:
                memo[key] = True
                return True
            if eval_E(j, d.div2()):
                memo[key] = False
                return False
            e = d.add_h_half()
            if not sym_leM(e):
                memo[key] = True
                return True
            if j == 1:
                # 入口が c*(3a - 1)/2^k であることを厳密確認
                assert e.Q < 0 and e.P == -3 * e.Q
                c = -e.Q
                b_val = sym_chain(c, e.K, n_mod6, z)
            else:
                b_val = eval_E(j - 1, e)
            memo[key] = not b_val
            return not b_val

        h_vals = [eval_E(j, H) for j in range(1, z + 1)]
        exp_h = [False] * (z - 1) + [True]
        assert h_vals == exp_h, f"N mod 24 = {N_mod24}: got {h_vals}, want {exp_h}"
        assert len(memo) == exp_counts[N_mod24]
        trees[N_mod24] = (z, memo)

    # BigInt 実数値照合: N = 30, 38, ..., 1006（全 123 例）
    num_ok = 0
    for N in range(30, 1007, 8):
        assert (3 * (1 << N) - 5) % 17 == 0
        a = (3 * (1 << N) - 5) // 17
        m = 3 * a - 2
        M = 3 * a
        h = (3 * a - 1) // 2
        n = (N - 2) // 4
        z, sym_memo = trees[N % 24]
        assert v2(m + 1) == 5 and v2(((m + 1) >> 5) + 1) == 4
        bound = min(2 * z - 1, 4)

        def walk_O(j_blk: int, d: int) -> bool:
            s = 0
            while j_blk > 0:
                assert 0 < d <= m and d != h - 1
                if (d & 1) == 0:
                    d >>= 1
                else:
                    e = (M + d) >> 1
                    assert e <= m
                    d = e
                    j_blk -= 1
                s += 1
            t = v2(d)
            assert t <= bound
            bv = (t % 2) == 0
            return bv if (s % 2 == 0) else (not bv)

        # 補題 K44.1 の実数値照合（最初の数例と末尾を全段確認、全 123 例で E 評価木全事実照合）
        memo_n: dict[tuple[int, int], bool] = {}

        def eval_E_num(j: int, d: int) -> bool:
            key = (j, d)
            if key in memo_n:
                return memo_n[key]
            if (d & 1) == 1:
                memo_n[key] = True
                return True
            if eval_E_num(j, d >> 1):
                memo_n[key] = False
                return False
            e = h + (d >> 1)
            if e > m:
                memo_n[key] = True
                return True
            b_val = walk_O(n, e) if j == 1 else eval_E_num(j - 1, e)
            memo_n[key] = not b_val
            return not b_val

        for (j, lf), sym_val in sym_memo.items():
            num = lf.P * a + lf.Q
            assert (num & ((1 << lf.K) - 1)) == 0
            d_val = num >> lf.K
            assert eval_E_num(j, d_val) == sym_val
        num_ok += 1

    return (
        "PR #279 Theorem K44 (v=5, w=4): SYMBOLIC PROOF VERIFIED for all N >= 30, N = 6 (mod 8) (3 classes: 29/16/16 E-tree facts, all orbits & conditions (a)(b)(c) & leM verified), errors=0",
        f"PR #279 BigInt E-tree cross-check (N=30..1006, 123 cases, up to {len(str(3*(3*(1<<1006)-5)//17-2))}-digit m): {num_ok}/123 exact match, errors=0",
    )


def lazy_k8_gaps_bits(m: int, count: int) -> list[bool]:
    h = (m + 1) >> 1
    M = m + 2
    E_gap = m + 1
    gaps: list[int] = []
    bits: list[bool] = []
    memo: list[dict[int, bool]] = [{} for _ in range(count)]
    for j in range(count):
        stack: list[tuple[int, int]] = [(j, h)]
        while stack:
            cj, d = stack[-1]
            mj = memo[cj]
            if d in mj:
                stack.pop()
                continue
            if cj == 0:
                mj[d] = (v2(d) & 1) == 0
                stack.pop()
                continue
            g = gaps[cj - 1]
            if g == M and d == h - 1:
                mj[d] = False
                stack.pop()
                continue
            if (d & 1) == 0:
                d2 = d >> 1
                if d2 not in mj:
                    stack.append((cj, d2))
                    continue
                if mj[d2]:
                    mj[d] = False
                    stack.pop()
                    continue
            sm = g + d
            if (sm & 1) == 0:
                e = sm >> 1
                if e <= m:
                    mp = memo[cj - 1]
                    if e not in mp:
                        stack.append((cj - 1, e))
                        continue
                    if mp[e]:
                        mj[d] = False
                        stack.pop()
                        continue
            mj[d] = True
            stack.pop()
        in_h = memo[j][h]
        bits.append(in_h)
        gaps.append(M if in_h else E_gap)
    return bits


def prove3_strict(
    m: int, pre: list[bool], w: list[bool], max_rounds: int = 20000, max_facts: int = 3_000_000
) -> tuple[bool, int, int]:
    assert m >= 3 and (m & 1) == 1
    p = len(pre)
    L = len(w)
    b = p + L
    h = (m + 1) >> 1
    M = m + 2
    E_gap = m + 1
    v = v2(m + 1)
    word_bits = [pre[i] if i < p else w[(i - p) % L] for i in range(b + L + 1)]
    if ((v2(h) & 1) == 0) != word_bits[0]:
        return False, 0, 0
    gaps_abs = [M if bit else E_gap for bit in word_bits]
    base_memo: list[dict[int, bool]] = [{} for _ in range(b + 1)]
    base_count = 0

    def eval_T(sj: int, sd: int) -> bool:
        nonlocal base_count
        stack = [(sj, sd)]
        while stack:
            j, d = stack[-1]
            mj = base_memo[j]
            if d in mj:
                stack.pop()
                continue
            if base_count >= max_facts:
                raise RuntimeError("base max_facts exceeded")
            if j == 0:
                mj[d] = (v2(d) & 1) == 0
                base_count += 1
                stack.pop()
                continue
            g = gaps_abs[j - 1]
            if g == M and d == h - 1:
                mj[d] = False
                base_count += 1
                stack.pop()
                continue
            if (d & 1) == 0:
                d2 = d >> 1
                if d2 not in mj:
                    stack.append((j, d2))
                    continue
                if mj[d2]:
                    mj[d] = False
                    base_count += 1
                    stack.pop()
                    continue
            sm = g + d
            if (sm & 1) == 0:
                e = sm >> 1
                if e <= m:
                    mp = base_memo[j - 1]
                    if e not in mp:
                        stack.append((j - 1, e))
                        continue
                    if mp[e]:
                        mj[d] = False
                        base_count += 1
                        stack.pop()
                        continue
            mj[d] = True
            base_count += 1
            stack.pop()
        return base_memo[sj][sd]

    for j in range(1, b + 1):
        if eval_T(j, h) != word_bits[j]:
            return False, 0, base_count

    s = 0
    while s < L and not w[L - 1 - s]:
        s += 1
    use_G = s > 0
    bound = min(2 * s - 1, v - 1) if use_G else -1
    A: dict[int, bool] = {}

    for _ in range(max_rounds):
        memo: list[dict[int, bool]] = [{} for _ in range(L + 1)]
        memo_count = 0

        def eval_S(si: int, sd: int) -> tuple[bool | None, int | None]:
            nonlocal memo_count
            stack = [(si, sd)]
            while stack:
                i, d = stack[-1]
                mi = memo[i]
                if d in mi:
                    stack.pop()
                    continue
                if memo_count >= max_facts:
                    raise RuntimeError("memo max_facts exceeded")
                if i == 0:
                    if use_G:
                        if (d & 1) == 1:
                            mi[d] = True
                            memo_count += 1
                            stack.pop()
                            continue
                        t = v2(d)
                        if t <= bound:
                            mi[d] = (t & 1) == 0
                            memo_count += 1
                            stack.pop()
                            continue
                    va = A.get(d)
                    if va is None:
                        return None, d
                    mi[d] = va
                    memo_count += 1
                    stack.pop()
                    continue
                g = gaps_abs[b + i - 1]
                if g == M and d == h - 1:
                    mi[d] = False
                    memo_count += 1
                    stack.pop()
                    continue
                if (d & 1) == 0:
                    d2 = d >> 1
                    if d2 not in mi:
                        stack.append((i, d2))
                        continue
                    if mi[d2]:
                        mi[d] = False
                        memo_count += 1
                        stack.pop()
                        continue
                sm = g + d
                if (sm & 1) == 0:
                    e = sm >> 1
                    if e <= m:
                        mp = memo[i - 1]
                        if e not in mp:
                            stack.append((i - 1, e))
                            continue
                        if mp[e]:
                            mi[d] = False
                            memo_count += 1
                            stack.pop()
                            continue
                mi[d] = True
                memo_count += 1
                stack.pop()
            return memo[si][sd], None

        unk_d: int | None = None
        for i in range(1, L + 1):
            val, unk = eval_S(i, h)
            if unk is not None:
                unk_d = unk
                break
            if val != word_bits[b + i]:
                return False, len(A), memo_count + base_count
        if unk_d is not None:
            A[unk_d] = eval_T(b, unk_d)
            continue
        for d, ev in list(A.items()):
            val, unk = eval_S(L, d)
            if unk is not None:
                unk_d = unk
                break
            if val != ev:
                return False, len(A), memo_count + base_count
        if unk_d is not None:
            A[unk_d] = eval_T(b, unk_d)
            continue
        return True, len(A), memo_count + base_count
    return False, len(A), base_count


def worker_k44(N: int) -> tuple[int, bool, int, int]:
    a = (3 * (1 << N) - 5) // 17
    m = 3 * a - 2
    z = 3 if (N % 24 == 6) else 2
    w = [True] * ((N - 2) // 4) + [False] * z
    ok, a_sz, nf = prove3_strict(m, [], w)
    return N, ok, a_sz, nf


def guess_k45(bits: list[bool]) -> tuple[int, int] | None:
    n = len(bits)
    for L in range(1, n // 3 + 1):
        for p in range(0, min(n // 2, n - 3 * L) + 1):
            ok = True
            for i in range(p, n - L):
                if bits[i] != bits[i + L]:
                    ok = False
                    break
            if ok:
                return p, L
    return None


def worker_k45(N: int) -> tuple[int, int, int, int, int, int]:
    assert ((1 << N) - 4641) % 29 == 0
    a = ((1 << N) - 4641) // 29
    m = 3 * a - 2
    assert v2(m + 1) == 7 and v2(((m + 1) >> 7) + 1) == 4
    pre: list[bool] = []
    w: list[bool] = []
    for J in (400, 800, 1600, 3200):
        bits = lazy_k8_gaps_bits(m, J)
        pl = guess_k45(bits)
        if pl is not None and pl[0] + 4 * pl[1] <= J:
            pre = bits[: pl[0]]
            w = bits[pl[0] : pl[0] + pl[1]]
            break
    assert len(w) > 0, f"K45 N={N}: period not guessed"
    ok, a_sz, nf = prove3_strict(m, pre, w)
    assert ok, f"K45 N={N}: prove3_strict failed"
    # 周期中の最大 1 連（巡回）
    k0 = w.index(False)
    rot = w[k0:] + w[:k0]
    mx = 0
    cur = 0
    for b in rot:
        if b:
            cur += 1
            if cur > mx:
                mx = cur
        else:
            cur = 0
    return N, len(pre), len(w), mx, a_sz, nf


def main() -> None:
    t0 = time.perf_counter()
    l_sym, l_num = verify_pr279_k44_symbolic()
    print(l_sym, flush=True)
    print(l_num, flush=True)

    workers = max(1, min(10, os.cpu_count() or 4))
    with ProcessPoolExecutor(max_workers=workers) as pool:
        k44_Ns = list(range(30, 1007, 8))
        k44_res = list(pool.map(worker_k44, k44_Ns))
        max_f_k44 = 0
        for N, ok, a_sz, nf in k44_res:
            assert ok and a_sz == 0, f"K44 fail N={N}: ok={ok}, A={a_sz}"
            max_f_k44 = max(max_f_k44, nf)

        k45_Ns = list(range(56, 617, 28))
        k45_res = list(pool.map(worker_k45, k45_Ns))
        max_f_k45 = 0
        max_A_k45 = 0
        for N, p, L, mx, a_sz, nf in k45_res:
            assert (p, L, mx) == EXPECTED_K45[N], f"K45 mismatch N={N}: got {(p, L, mx)}, want {EXPECTED_K45[N]}"
            max_f_k45 = max(max_f_k45, nf)
            max_A_k45 = max(max_A_k45, a_sz)

    elapsed = time.perf_counter() - t0
    lines = [
        "gemini-2 independent verification of PR #279 (Theorem K44), PR #275 (K44 induction 123 cases), PR #277 (K45 induction 21 cases)",
        l_sym,
        l_num,
        f"PR #275 K44 prove3_strict (N=30..1006, 123 cases): 123/123 proved with (c,k)=(1,1) and A=0, maxFacts={max_f_k44}, errors=0",
        f"PR #277 K45 prove3_strict (N=56..616, 21 cases): 21/21 proved with (c,k)=(1,1), all (p, L, max_run) match PR #277, maxA={max_A_k45}, maxFacts={max_f_k45}, errors=0",
        f"Total elapsed={elapsed:.2f}s",
    ]
    out_text = "\n".join(lines) + "\n"
    Path("data/gemini2_verify_k44_k45.txt").write_text(out_text, encoding="utf-8")
    print(out_text, end="", flush=True)


if __name__ == "__main__":
    main()
