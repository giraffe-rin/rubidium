"""
gemini2_verify_k56_k57_k33d.py — PR #327（prove3 k33d 比較）・PR #329（補題 K56.1・定理 K56）・PR #331（命題 K57）の Python 独立検証

何を計算するか:
  1. PR #327（prove3 への補題 K33d 組み込み）:
     - 4 < m <= 2^20 の v2(m+1) = 1 の全奇数 m（262,143 個）について、Python 独立実装の prove3（k33d=False / k33d=True）を並列実行し、
       確定数・仮定数合計・仮定数最大・片方のみ確定数が data/k33d_compare.txt と完全一致することを検証する。
  2. PR #329（補題 K56.1 および定理 K56）:
     - 偶数 4 <= rho <= 24 について、c = 1 および 3 <= c < 2^{rho-1} の奇数 c（1 の個数 <= rho/2）すべてに対し、
       基本周期 d・周期内 1 の個数 l・l | L・delta(c) = L + (L/l)(d - l) の偶奇を全数検証し、data/k56_delta.txt と照合する。
     - さらに 4 <= rho <= 18 について、T(b) = (b + 2^rho - 1)/2^{v2} の閉路長と r(b) の和が (l, d) と一致することを直接検証する。
     - 定理 K56（R ≡ L + 1 (mod 2L)）について、K54（w < v）および K55（w = v）の双方で具体的な大きな m に対し K8 遅延計算で直接照合する。
  3. PR #331（命題 K57）:
     - data/k57_predict.txt の全 310 族（既知 10 族 + 無作為 300 族、seed = 12345）を Python で独立再検証し、
       予測一致だけでなく鎖の条件 (M+d)/2 <= m, d != h - 1, d > 0 が実際に全奇数の点で成立しているかも直接検査する。
     - 査読で発見した 2 点の境界欠陥（v >= N でのブロック 0 反例、および beta_0 = 0 / b + 3r = 0 での T(b)/v2 無限ループ条件）を具体例で確認する。

実行方法（リポジトリのルートで）:
  uv run python code/gemini2_verify_k56_k57_k33d.py > data/gemini2_verify_k56_k57_k33d.txt
"""
from __future__ import annotations

import concurrent.futures
import math
import sys
import time

sys.setrecursionlimit(200000)


def v2(x: int) -> int:
    if x < 0:
        x = -x
    return (x & -x).bit_length() - 1


# ---------------------------------------------------------------------------
# Shared lazy K8 gap evaluator (arbitrary precision)
# ---------------------------------------------------------------------------
def gaps_lazy(m: int, J: int) -> list[int]:
    h = (m + 1) // 2
    memo: dict[tuple[int, int], bool] = {}
    gm: dict[int, int] = {}

    def gap(j: int) -> int:
        if j in gm:
            return gm[j]
        r = m + 2 if (m % 2 == 1 and S(j, h)) else m + 1
        gm[j] = r
        return r

    def S(j: int, d: int) -> bool:
        key = (j, d)
        if key in memo:
            return memo[key]
        if j == 0:
            r = (v2(d) % 2 == 0)
        else:
            if d % 2 == 0 and S(j, d // 2):
                r = False
            else:
                g = gap(j - 1)
                sm = g + d
                if sm % 2 == 0 and sm // 2 <= m and S(j - 1, sm // 2):
                    r = False
                elif g == m + 2 and d == h - 1:
                    r = False
                else:
                    r = True
        memo[key] = r
        return r

    return [gap(j) - m - 1 for j in range(J)]


# ---------------------------------------------------------------------------
# 1. PR #327: prove3 k33d comparison over all 4 < m <= 2^20 with v2(m+1) = 1
# ---------------------------------------------------------------------------
def guess_lazy_int(m: int, J: int = 400) -> tuple[int, int, list[int]] | None:
    h = (m + 1) // 2
    stride = m + 2
    memo: dict[int, bool] = {}
    gm: list[int] = [-1] * J

    def gap(j: int) -> int:
        v = gm[j]
        if v != -1:
            return v
        r = m + 2 if S(j, h) else m + 1
        gm[j] = r
        return r

    def S(j: int, d: int) -> bool:
        k = j * stride + d
        res = memo.get(k)
        if res is not None:
            return res
        if j == 0:
            r = (((d & -d).bit_length() - 1) & 1) == 0
        else:
            if (d & 1) == 0 and S(j, d >> 1):
                r = False
            else:
                g = gap(j - 1)
                sm = g + d
                if (sm & 1) == 0 and (sm >> 1) <= m and S(j - 1, sm >> 1):
                    r = False
                elif g == m + 2 and d == h - 1:
                    r = False
                else:
                    r = True
        memo[k] = r
        return r

    g = [gap(j) - m - 1 for j in range(J)]
    max_L = max(120, J // 3)
    max_p = max(150, J // 2)
    for L in range(1, max_L + 1):
        lim_p = min(max_p, J - 3 * L)
        for p in range(0, lim_p + 1):
            ok = True
            for i in range(p, J - L):
                if g[i] != g[i + L]:
                    ok = False
                    break
            if ok:
                return (p, L, g)
    return None


def prove3_py(m: int, pre: str, w: str, k33d: bool, max_rounds: int = 20000, max_facts: int = 3000000) -> tuple[bool, int]:
    p = len(pre)
    L = len(w)
    v = ((m + 1) & -(m + 1)).bit_length() - 1
    h = (m + 1) // 2
    s = 0
    while s < L and w[L - 1 - s] == "0":
        s += 1

    def word(i: int) -> str:
        return pre[i] if i < p else w[(i - p) % L]

    g0 = "1" if (((h & -h).bit_length() - 1) & 1) == 0 else "0"
    if g0 != word(0):
        return (False, 0)
    b = p + L
    gap_abs = [m + 2 if word(j) == "1" else m + 1 for j in range(b + L + 1)]
    stride = m + 2
    base: dict[int, bool] = {}
    over = False

    def T(j: int, d: int) -> bool:
        nonlocal over
        if over:
            return False
        k = j * stride + d
        res = base.get(k)
        if res is not None:
            return res
        if len(base) > max_facts:
            over = True
            return False
        if j == 0:
            r = (((d & -d).bit_length() - 1) & 1) == 0
        else:
            if (d & 1) == 0 and T(j, d >> 1):
                r = False
            else:
                if over:
                    return False
                g = gap_abs[j - 1]
                sm = g + d
                if (sm & 1) == 0 and (sm >> 1) <= m and T(j - 1, sm >> 1):
                    r = False
                elif over:
                    return False
                elif g == m + 2 and d == h - 1:
                    r = False
                else:
                    r = True
        if over:
            return False
        base[k] = r
        return r

    for j in range(1, b + 1):
        x = T(j, h)
        if over:
            return (False, 0)
        if ("1" if x else "0") != word(j):
            return (False, 0)

    bound = min(2 * s - 1, v - 1) if s > 0 else -1
    use_g = s > 0
    A: dict[int, bool] = {}

    for _ in range(max_rounds):
        memo: dict[int, bool] = {}
        unknown = -1
        too_many = False

        def S(i: int, d: int) -> bool:
            nonlocal unknown, too_many
            if unknown != -1 or too_many:
                return False
            k = i * stride + d
            res = memo.get(k)
            if res is not None:
                return res
            if len(memo) > max_facts:
                too_many = True
                return False
            if i == 0:
                t = (d & -d).bit_length() - 1
                if use_g and t == 0:
                    r = True
                elif use_g and k33d and t == 1:
                    r = False
                elif use_g and t <= bound:
                    r = (t & 1) == 0
                elif d in A:
                    r = A[d]
                else:
                    unknown = d
                    return False
            else:
                if (d & 1) == 0 and S(i, d >> 1):
                    r = False
                else:
                    if unknown != -1 or too_many:
                        return False
                    g = gap_abs[b + i - 1]
                    sm = g + d
                    if (sm & 1) == 0 and (sm >> 1) <= m and S(i - 1, sm >> 1):
                        r = False
                    elif unknown != -1 or too_many:
                        return False
                    elif g == m + 2 and d == h - 1:
                        r = False
                    else:
                        r = True
            if unknown != -1 or too_many:
                return False
            memo[k] = r
            return r

        ok1 = True
        for i in range(1, L + 1):
            x = S(i, h)
            if unknown != -1 or too_many:
                break
            if ("1" if x else "0") != w[i % L]:
                ok1 = False
                break
        if too_many:
            return (False, len(A))
        if unknown != -1:
            A[unknown] = T(b, unknown)
            if over:
                return (False, len(A))
            continue
        if not ok1:
            return (False, len(A))
        for d_val, expected in list(A.items()):
            got = S(L, d_val)
            if unknown != -1 or too_many:
                break
            if got != expected:
                return (False, len(A))
        if too_many:
            return (False, len(A))
        if unknown != -1:
            A[unknown] = T(b, unknown)
            if over:
                return (False, len(A))
            continue
        return (True, len(A))
    return (False, len(A))


def try_all_prove3(m: int, pre: str, w: str, k33d: bool) -> int | None:
    for c in (1, 2, 4, 8, 16, 32):
        pre_c = pre + w * (c - 1)
        for k in (1, 2, 3, 4):
            ok, a_sz = prove3_py(m, pre_c, w * k, k33d)
            if ok:
                return a_sz
    return None


def worker_k33d_chunk(args: tuple[int, int]) -> tuple[int, int, int, int, int, int, int, int, int, int]:
    start_m, end_m = args
    n = ok0 = ok1 = only0 = only1 = sumA0 = sumA1 = maxA0 = maxA1 = no_guess = 0
    # m odd with v2(m+1) = 1 <=> m ≡ 1 (mod 4)
    m = start_m
    rem = m % 4
    if rem != 1:
        m += (1 - rem) % 4
    if m < 5:
        m = 5
    while m <= end_m:
        pl = guess_lazy_int(m, 400)
        if pl is None:
            no_guess += 1
            m += 4
            continue
        n += 1
        p, L, g = pl
        pre = "".join("1" if x else "0" for x in g[:p])
        w = "".join("1" if x else "0" for x in g[p : p + L])
        r0 = try_all_prove3(m, pre, w, False)
        r1 = try_all_prove3(m, pre, w, True)
        if r0 is not None:
            ok0 += 1
            sumA0 += r0
            if r0 > maxA0:
                maxA0 = r0
        if r1 is not None:
            ok1 += 1
            sumA1 += r1
            if r1 > maxA1:
                maxA1 = r1
        if r0 is not None and r1 is None:
            only0 += 1
        if r1 is not None and r0 is None:
            only1 += 1
        m += 4
    return (n, no_guess, ok0, ok1, only0, only1, sumA0, sumA1, maxA0, maxA1)


# ---------------------------------------------------------------------------
# 2. PR #329: Lemma K56.1 exhaustive check + Theorem K56 K8 checks
# ---------------------------------------------------------------------------
def worker_k56_rho(rho: int) -> tuple[int, int, int, int, int, int, int, int]:
    z = rho // 2
    L = 1
    for i in range(1, z + 1):
        L = math.lcm(L, i)
    divs = [dd for dd in range(1, rho) if rho % dd == 0]
    mask = (1 << rho) - 1
    n = odd_cnt = nd_cnt = per_cnt = c1_err = t_err = 0

    # Check c = 1 as well
    d1 = rho
    l1 = 1
    if L % l1 != 0 or ((L + (L // l1) * (d1 - l1)) & 1) != 0:
        c1_err += 1

    # Exhaustive check over odd 3 <= c < 2^{rho-1} with popcount <= z
    limit = 1 << (rho - 1)
    check_T = rho <= 18
    for c in range(3, limit, 2):
        if c.bit_count() > z:
            continue
        n += 1
        d = rho
        for dd in divs:
            if ((c >> dd) | ((c << (rho - dd)) & mask)) == c:
                d = dd
                break
        if d < rho:
            per_cnt += 1
        l_val = (c & ((1 << d) - 1)).bit_count()
        if L % l_val != 0:
            nd_cnt += 1
        elif ((L + (L // l_val) * (d - l_val)) & 1) != 0:
            odd_cnt += 1
        if check_T:
            b = c
            steps = 0
            r_sum = 0
            while True:
                x = b + mask
                r = (x & -x).bit_length() - 1
                b = x >> r
                steps += 1
                r_sum += r
                if b == c:
                    break
            if steps != l_val or r_sum != d:
                t_err += 1
    return (rho, L, n, odd_cnt, nd_cnt, per_cnt, c1_err, t_err)


def verify_k56_direct_k8() -> list[tuple[str, bool]]:
    """Direct K8 lazy check of Theorem K56 (R ≡ L + 1 mod 2L) for both K54 (w < v) and K55 (w = v)."""
    results: list[tuple[str, bool]] = []
    # (label, v, rho, w, R, s_mult, is_k55)
    cases = [
        ("K54 (v=5, w=4, rho=4, L=2, R=7)", 5, 4, 4, 7, 1, False),
        ("K54 (v=7, w=4, rho=4, L=2, R=11)", 7, 4, 4, 11, 1, False),
        ("K54 (v=7, w=6, rho=6, L=6, R=19)", 7, 6, 6, 19, 1, False),
        ("K54 (v=9, w=6, rho=6, L=6, R=19)", 9, 6, 6, 19, 1, False),
        ("K54 (v=9, w=8, rho=8, L=12, R=37)", 9, 8, 8, 37, 1, False),
        ("K55 (v=3, w=3, rho=4, L=2, R=11, s=1)", 3, 4, 3, 11, 1, True),
        ("K55 (v=5, w=5, rho=6, L=6, R=19, s=1)", 5, 6, 5, 19, 1, True),
        ("K55 (v=5, w=5, rho=6, L=6, R=19, s=3)", 5, 6, 5, 19, 3, True),
        ("K55 (v=7, w=7, rho=8, L=12, R=37, s=1)", 7, 8, 7, 37, 1, True),
    ]
    for label, v, rho, w, R, s_mult, is_k55 in cases:
        z = rho // 2
        L = 1
        for i in range(1, z + 1):
            L = math.lcm(L, i)
        assert R % (2 * L) == L + 1, f"R not L+1 mod 2L: {label}"
        if not is_k55:
            # K47 family: q = 2^v - 2^rho + 1, r = (2^rho - 1)/3, N EVEN with ceil((N - v)/rho) = R
            # Since v is odd and rho is even, N = v + (R - 1)*rho + 1 is even and ceil((N - v)/rho) = R.
            r_param = ((1 << rho) - 1) // 3
            q = (1 << v) - (1 << rho) + 1
            N = v + (R - 1) * rho + 1
            assert N % 2 == 0 and (N - v + rho - 1) // rho == R
            # Find odd s (starting at s_mult) with s*2^N ≡ r_param (mod q) and a odd
            X = 1 << N
            s = None
            cnt = 0
            for cand in range(1, 20 * q, 2):
                if (cand * X - r_param) % q == 0:
                    a = (cand * X - r_param) // q
                    if a > 0 and a % 2 == 1:
                        cnt += 1
                        if cnt == s_mult:
                            s = cand
                            break
            assert s is not None
            a = (s * X - r_param) // q
            m = 3 * a - 2
            assert v2(m + 1) == v and v2(((m + 1) >> v) + 1) == w
        else:
            # K47b / K55 family: rho = v + 1, r = (2^rho - 1)/3, q = -(2^v - 1),
            # q*a + r = s*2^N => (-q)*a = r - s*2^N => (2^v - 1)*a = s*2^N - r (wait: sign!)
            # Check K55: m = 3a - 2, (2^v - 1)a = s*2^N + r (so q = -(2^v - 1), -q*a + (-r)?)
            # Let's check: q*a + r = s*2^N with q = -(2^v - 1), r = (2^{v+1} - 1)/3 => s < 0, i.e., (2^v - 1)a = |s|*2^N + r
            # Verify: 3r + q = (2^{v+1} - 1) - (2^v - 1) = 2^v!
            # And (2^v - 1)(m + 1) = 3(2^v - 1)a - (2^v - 1) = 3(|s|*2^N + r) - (2^v - 1) = 3|s|*2^N + 2^v => v2(m+1) = v!
            # u = (m+1)/2^v => (2^v - 1)(u + 1) = 3|s|*2^{N - v} + 2^v => v2(u + 1) = v (since N - v > v)!
            r_param = ((1 << rho) - 1) // 3
            Q = (1 << v) - 1
            N = v + (R - 1) * rho + v
            X = 1 << N
            a = None
            cnt = 0
            for cand in range(1, 20 * Q, 2):
                if (cand * X + r_param) % Q == 0:
                    aa = (cand * X + r_param) // Q
                    if aa > 0 and aa % 2 == 1:
                        cnt += 1
                        if cnt == s_mult:
                            a = aa
                            break
            assert a is not None
            m = 3 * a - 2
            assert v2(m + 1) == v and v2(((m + 1) >> v) + 1) == v

        # Compute 3 full cycles of gaps
        J = 3 * (R + (v + 1) // 2) + 5
        g = gaps_lazy(m, J)
        # Extract runs of 1s and 0s (excluding trailing incomplete run)
        runs: list[tuple[int, int]] = []
        cur_val = g[0]
        cur_len = 1
        for x in g[1:]:
            if x == cur_val:
                cur_len += 1
            else:
                runs.append((cur_val, cur_len))
                cur_val = x
                cur_len = 1
        # Check at least 5 completed runs: all 1-runs == R, all 0-runs in [rho/2, (v+1)//2] (or == (v+1)//2 for K55)
        ok = len(runs) >= 5 and runs[0] == (1, R)
        for val, ln in runs:
            if val == 1:
                if ln != R:
                    ok = False
            else:
                if is_k55:
                    if ln != (v + 1) // 2:
                        ok = False
                else:
                    if not (rho // 2 <= ln <= (v + 1) // 2):
                        ok = False
        results.append((f"{label}: runs={runs[:6]}", ok))
    return results


# ---------------------------------------------------------------------------
# 3. PR #331: Proposition K57 verification + chain condition check + defect demo
# ---------------------------------------------------------------------------
def verify_k57() -> dict:
    # Build exact same 310 families as data/k57_predict.txt
    known = [
        (29, 4641, 1, 56),
        (29, 4641, 1, 112),
        (29, 4641, 1, 224),
        (29, 4641, 1, 336),
        (17, 5, 3, 30),
        (17, 5, 3, 62),
        (23, 1, 1, 22),
        (23, 1, 1, 88),
        (125, 1, 1, 100),
        (125, 1, 1, 200),
    ]
    seed = 12345

    def rnd(n: int) -> int:
        nonlocal seed
        seed = (seed * 1103515245 + 12345) % 2147483648
        return seed % n

    fams = list(known)
    k = 0
    while k < 300:
        q = 2 * rnd(127) + 3
        r = (2 * rnd(2500) + 1) * (1 if rnd(2) else -1)
        N = 40 + rnd(80)
        X = 1 << N
        for s in range(1, 2 * q, 2):
            if (s * X - r) % q == 0:
                a = (s * X - r) // q
                if a > 0 and a % 2 == 1:
                    fams.append((q, r, s, N))
                    k += 1
                break

    tot = 0
    pred_ok = 0
    cond_ok = 0
    cond_fail = 0
    k45_orbit = None

    for q, r, s, N in fams:
        X = 1 << N
        a = (s * X - r) // q
        m = 3 * a - 2
        M = 3 * a
        h = (m + 1) // 2
        beta0 = 3 * r + q
        assert beta0 != 0
        v = v2(beta0)
        assert v < N
        R3 = 3 * r

        def T_step(b: int) -> tuple[int, int]:
            x = b + R3
            assert x != 0
            t = v2(x)
            return (x >> t, t)

        pred = "1" if (v - 1) % 2 == 0 else "0"
        all_chain_cond_hold = True
        if pred == "1":
            b = beta0 >> v
            K = v
            bs: list[int] = []
            ts: list[int] = []
            for i in range(1, 400):
                bs.append(b)
                nb, t = T_step(b)
                if K + t >= N:
                    break
                sp = (v - 1) + i + sum(t_j - 1 for t_j in ts)
                in_b = ((t - 1) % 2 == 0)
                hin = (in_b != (sp % 2 == 1))
                pred += "1" if hin else "0"

                # Explicitly check actual chain conditions (M+d)/2 <= m, d != h-1, d > 0
                d = h
                steps_chk = 0
                for step_idx in range(i):
                    while d % 2 == 0:
                        d >>= 1
                        steps_chk += 1
                    if not (d > 0 and d != h - 1 and (M + d) // 2 <= m):
                        all_chain_cond_hold = False
                    d = (M + d) // 2
                    steps_chk += 1
                assert steps_chk == sp and v2(d) == t - 1

                if not hin:
                    break
                ts.append(t)
                K += t
                b = nb

            if (q, r, s, N) == (29, 4641, 1, 56):
                # Record K45 orbit
                orb = []
                cur = beta0 >> v
                for _ in range(6):
                    nxt, tt = T_step(cur)
                    orb.append((cur, tt))
                    cur = nxt
                k45_orbit = orb

        g = gaps_lazy(m, len(pred) + 2)
        g_str = "".join("1" if x else "0" for x in g)
        tot += 1
        if g_str[: len(pred)] == pred:
            pred_ok += 1
        if all_chain_cond_hold:
            cond_ok += 1
        else:
            cond_fail += 1

    # Verify the two boundary defects found in audit:
    # 1. Block 0 failure when v >= N
    defects_block0 = []
    for q, r, s, N in [(5, 9, 9, 4), (5, 9, 17, 5)]:
        X = 1 << N
        assert (s * X - r) % q == 0
        a = (s * X - r) // q
        assert a > 0 and a % 2 == 1
        m = 3 * a - 2
        beta0 = 3 * r + q
        v_beta = v2(beta0)
        k57_pred = "1" if (v_beta - 1) % 2 == 0 else "0"
        actual_g0 = str(gaps_lazy(m, 2)[0])
        defects_block0.append((q, r, s, N, a, m, beta0, v_beta, k57_pred, actual_g0))

    # 2. Infinite loop triggers in k57_predict.js (b + 3r == 0 or beta0 == 0)
    # (27, -1, 1, 9): 27*19 - 1 = 512, beta0 = 24, v = 3, b0 = 3, b0 + 3r = 0
    # (3, -1, 1, 4): 3*5 - 1? No, 3*5 + 1 = 16 -> r = +1, q = 3 -> beta0 = 6; for beta0 = 0 need q = -3r: q=3, r=-1, s=1, N=4 -> 3a - 1 = 16 no, N=3 -> 3*3 - 1 = 8 -> a=3, m=7!
    loop_triggers = []
    for q, r, s, N in [(27, -1, 1, 9), (3, -1, 1, 3)]:
        X = 1 << N
        assert (s * X - r) % q == 0
        a = (s * X - r) // q
        assert a > 0 and a % 2 == 1
        beta0 = 3 * r + q
        if beta0 == 0:
            loop_triggers.append((q, r, s, N, a, 3 * a - 2, "beta0 == 0 -> v2(beta0) infinite loop"))
        else:
            v_beta = v2(beta0)
            b0 = beta0 >> v_beta
            assert b0 + 3 * r == 0
            loop_triggers.append((q, r, s, N, a, 3 * a - 2, f"beta0={beta0}, v={v_beta}, b0={b0}, b0+3r=0 -> T(b0) infinite loop"))

    return {
        "tot": tot,
        "pred_ok": pred_ok,
        "cond_ok": cond_ok,
        "cond_fail": cond_fail,
        "k45_orbit": k45_orbit,
        "defects_block0": defects_block0,
        "loop_triggers": loop_triggers,
    }


def main() -> None:
    t0 = time.perf_counter()
    print("# gemini-2 独立検証: PR #327（prove3 k33d）・PR #329（補題 K56.1・定理 K56）・PR #331（命題 K57）")
    print("# 実行コマンド: uv run python code/gemini2_verify_k56_k57_k33d.py > data/gemini2_verify_k56_k57_k33d.txt")
    print()

    # 1. PR #327 (262,143 cases in 4 < m <= 2^20, v2(m+1) = 1)
    t1 = time.perf_counter()
    chunks = []
    step = 1 << 16
    for lo in range(5, 1 << 20, step):
        chunks.append((lo, min((1 << 20), lo + step - 1)))
    tot_n = tot_ng = tot_ok0 = tot_ok1 = tot_only0 = tot_only1 = tot_s0 = tot_s1 = max_a0 = max_a1 = 0
    with concurrent.futures.ProcessPoolExecutor(max_workers=10) as ex:
        for res in ex.map(worker_k33d_chunk, chunks):
            n, ng, ok0, ok1, o0, o1, s0, s1, m0, m1 = res
            tot_n += n
            tot_ng += ng
            tot_ok0 += ok0
            tot_ok1 += ok1
            tot_only0 += o0
            tot_only1 += o1
            tot_s0 += s0
            tot_s1 += s1
            max_a0 = max(max_a0, m0)
            max_a1 = max(max_a1, m1)
    pr327_match = (
        tot_n == 262143
        and tot_ng == 0
        and tot_ok0 == 262143
        and tot_ok1 == 262143
        and tot_only0 == 0
        and tot_only1 == 0
        and tot_s0 == 293753
        and tot_s1 == 176367
        and max_a0 == 128
        and max_a1 == 128
    )
    print(f"## 1. PR #327（prove3 k33d 比較: 4 < m <= 2^20, v2(m+1) = 1）[{time.perf_counter() - t1:.2f}s]")
    print(f"- 対象 m: {tot_n}（推測不能 {tot_ng}）")
    print(f"- k33d なし: 確定 {tot_ok0}, 仮定数合計 {tot_s0}, 最大 {max_a0}")
    print(f"- k33d あり: 確定 {tot_ok1}, 仮定数合計 {tot_s1}, 最大 {max_a1}")
    print(f"- 片方のみ確定: なしのみ {tot_only0}, ありのみ {tot_only1}")
    print(f"- data/k33d_compare.txt との完全一致: {pr327_match}")
    print()

    # 2. PR #329 (Lemma K56.1 exhaustive + Theorem K56 K8 checks)
    t2 = time.perf_counter()
    expected_k56 = {
        4: (2, 2, 1),
        6: (6, 10, 2),
        8: (12, 41, 3),
        10: (60, 162, 5),
        12: (60, 637, 13),
        14: (420, 2509, 17),
        16: (840, 9907, 42),
        18: (2520, 39202, 74),
        20: (2520, 155381, 165),
        22: (27720, 616665, 257),
        24: (27720, 2449867, 677),
    }
    k56_errors = 0
    print("## 2. PR #329（補題 K56.1 全数検証・定理 K56 K8 直接検証）")
    with concurrent.futures.ProcessPoolExecutor(max_workers=10) as ex:
        k56_rows = list(ex.map(worker_k56_rho, list(range(4, 25, 2))))
    for rho, L, n, odd_cnt, nd_cnt, per_cnt, c1_err, t_err in k56_rows:
        exp_L, exp_n, exp_per = expected_k56[rho]
        row_ok = (L == exp_L and n == exp_n and per_cnt == exp_per and odd_cnt == 0 and nd_cnt == 0 and c1_err == 0 and t_err == 0)
        if not row_ok:
            k56_errors += 1
        print(
            f"- rho={rho:2d}: L={L:5d}, entries={n:7d}, periodic={per_cnt:3d}, odd_delta={odd_cnt}, nd={nd_cnt}, c1_err={c1_err}, T_cycle_err={t_err}, match={row_ok}"
        )
    print(f"- 補題 K56.1 検証時間: {time.perf_counter() - t2:.2f}s, errors = {k56_errors}")

    k56_k8 = verify_k56_direct_k8()
    k56_k8_errors = sum(0 if ok else 1 for _, ok in k56_k8)
    print(f"- 定理 K56（R ≡ L + 1 mod 2L）K8 直接照合（{len(k56_k8)} 例, errors = {k56_k8_errors}）:")
    for desc, ok in k56_k8:
        print(f"  [{'OK' if ok else 'NG'}] {desc}")
    print()

    # 3. PR #331 (Proposition K57 + chain condition check + boundary defects)
    t3 = time.perf_counter()
    k57 = verify_k57()
    print(f"## 3. PR #331（命題 K57 独立検証・鎖条件確認・境界欠陥確認）[{time.perf_counter() - t3:.2f}s]")
    print(f"- 310 族（既知 10 + 無作為 300）予測一致: {k57['pred_ok']}/{k57['tot']}")
    print(f"- 全奇数の点での鎖条件 ((M+d)/2 <= m, d != h-1, d > 0) 成立: {k57['cond_ok']}/{k57['tot']} (不成立 {k57['cond_fail']})")
    print(f"- 予想 K45 族 (29, 4641) の b 軌道: {k57['k45_orbit']}")
    print("- 査読で発見した境界欠陥（1）ブロック 0 で v >= N の反例:")
    for q, r, s, N, a, m, b0, vb, kp, ag in k57["defects_block0"]:
        print(f"  (q={q}, r={r}, s={s}, N={N}) -> a={a}, m={m}, beta0={b0}, v={vb} >= N: K57予測 g0='{kp}', 実際 g0='{ag}' (不一致)")
    print("- 査読で発見した境界欠陥（2）code/k57_predict.js の無限ループ誘発例:")
    for q, r, s, N, a, m, msg in k57["loop_triggers"]:
        print(f"  (q={q}, r={r}, s={s}, N={N}) -> a={a}, m={m}: {msg}")

    total_errors = (0 if pr327_match else 1) + k56_errors + k56_k8_errors + (k57["tot"] - k57["pred_ok"])
    print()
    print(f"## 総合検証結果: verification_errors = {total_errors}, total_elapsed = {time.perf_counter() - t0:.2f}s")
    if total_errors != 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
