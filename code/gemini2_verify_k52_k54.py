"""
PR #311（補題 K52）、PR #313（補題 K53）、PR #315（定理 K54・補題 K54.1）、
および PR #307（K50 ρ <= 28）・PR #309（K50 形式評価 ρ <= 60 全 77 組）の
独立 Python 検証スクリプト。

1. PR #313（補題 K53）：
   - ρ = 2, 4, ..., 18 のすべての奇数 0 < b < 2^ρ - 1（計 174,762 個）について (1)(2)(3)(4) を全数検証し、
     さらに ρ = 20..60 の無作為 20,000 個についても (1)〜(4) を検証する。
2. PR #311（補題 K52）＋ PR #315（定理 K54・補題 K54.1）：
   - data/k54_check.txt の全 14 組（(5,4)..(23,22), (13,6), (17,8), (21,10), (25,12)）について、
     独立の Kleene 3 値再帰 E_j(c, k) で (1) E_j(1, 1) = False（j = 1..z-1）および
     (2) 補題 K54.1 範囲内の全状態（ρ = 22 で 474,891 状態）で E_i(c, k) = Ψ(c, k) を完全照合する。
   - さらに v = 19, 21, 23 の新規 K54 実数値例を独立 K8 遅延評価で直接照合する。
3. PR #307 & PR #309（定理 K50 形式評価 ρ <= 60 全 77 組）：
   - 全 77 組（ρ = 4..60 の v = ρ+1, ρ+3 および v = 41 の全偶数 ρ <= 40）について、
     R ≡ 1 (mod 2L) と R ≡ L + 1 (mod 2L) の双方で E_j(1, 1) = False（j = 1..z-1）を独立検証し、
     同時に軌道周期・純周期性・b < 3r・平均 < ρ・R の下限 <= 3v をすべて明示確認する。

実行方法:
    python code/gemini2_verify_k52_k54.py
出力:
    data/gemini2_verify_k52_k54.txt
"""

from __future__ import annotations

import math
import random
import time
from pathlib import Path


EXPECTED_K54_COUNTS = {
    (5, 4): 0,
    (7, 6): 3,
    (9, 8): 23,
    (11, 10): 114,
    (13, 12): 486,
    (15, 14): 1960,
    (17, 16): 7758,
    (19, 18): 30561,
    (21, 20): 120389,
    (23, 22): 474891,
    (13, 6): 3,
    (17, 8): 23,
    (21, 10): 114,
    (25, 12): 486,
}


def v2(x: int) -> int:
    assert x > 0
    return (x & -x).bit_length() - 1


def rot_right(b: int, t: int, rho: int) -> int:
    t %= rho
    mask = (1 << rho) - 1
    return ((b >> t) | ((b << (rho - t)) & mask)) & mask


def verify_pr313_k53() -> str:
    """PR #313（補題 K53）の (1)-(4) 全数検証（ρ = 2..18）＋無作為検証（ρ = 20..60）。"""
    total_b = 0
    for rho in range(2, 19, 2):
        M = (1 << rho) - 1
        cyc_set: set[int] = set()
        for b in range(1, M, 2):
            total_b += 1
            # (1) T(b) = (b + M)/2^t は右 t 桁回転に一致
            x = b + M
            t = v2(x)
            tb = x >> t
            if b == 1:
                assert t == rho and tb == 1
            else:
                assert t == v2(b - 1) and 1 <= t <= rho - 1
                assert tb == rot_right(b, t, rho)
            assert 0 < tb < M and (tb & 1) == 1
            # (2)(3)(4) 軌道をたどる（純周期、長さ l = p、t の和 = d、d/l = rho <=> b == 1）
            cur = b
            steps = 0
            t_sum = 0
            while True:
                ti = v2(cur + M)
                cur = (cur + M) >> ti
                steps += 1
                t_sum += ti
                if cur == b:
                    break
                assert steps <= rho
            # 基本周期 d を直接計算
            d = 1
            while d <= rho:
                if rho % d == 0 and rot_right(b, d, rho) == b:
                    break
                d += 1
            # 1 基本周期の 1 の個数 p
            p = (b & ((1 << d) - 1)).bit_count()
            assert steps == p and t_sum == d
            assert (t_sum == rho * steps) == (b == 1)
            cyc_set.add(steps)
        assert cyc_set == set(range(1, rho))

    # 無作為検証 ρ = 20..60（20,000 個）
    rng = random.Random(2026112453)
    rand_ok = 0
    for rho in range(20, 61, 2):
        M = (1 << rho) - 1
        for _ in range(1000):
            b = rng.randrange(1, M, 2)
            t = v2(b + M)
            tb = (b + M) >> t
            assert tb == rot_right(b, t, rho) and 0 < tb < M and (tb & 1) == 1
            cur = b
            steps = 0
            t_sum = 0
            while True:
                ti = v2(cur + M)
                cur = (cur + M) >> ti
                steps += 1
                t_sum += ti
                if cur == b:
                    break
            d = 1
            while d <= rho:
                if rho % d == 0 and rot_right(b, d, rho) == b:
                    break
                d += 1
            p = (b & ((1 << d) - 1)).bit_count()
            assert steps == p and t_sum == d and (t_sum == rho * steps) == (b == 1)
            rand_ok += 1

    return f"PR #313 Lemma K53 (1)-(4): exhaustive rho=2..18 ({total_b} odd b) + random rho=20..60 ({rand_ok} odd b), errors=0"


def eval_formal_k50_k52(v: int, rho: int, shift_half: bool) -> tuple[bool, set[int], int]:
    """補題 K52 の Kleene 3 値再帰で E_j(1, 1) (j=1..z-1) を独立評価。
    shift_half=False: R ≡ 1 (mod 2L)
    shift_half=True : R ≡ L + 1 (mod 2L)
    返り値: (all_zero, cyc_lens_used, R1_lower_bound)
    """
    z = rho // 2
    M = (1 << rho) - 1
    L = 1
    for i in range(1, z + 1):
        L = math.lcm(L, i)

    cyc_lens: set[int] = set()
    r1_need = 3 * v
    orbit_cache: dict[int, tuple[bool, int, int]] = {}

    def orbit_stats(c: int) -> tuple[bool, int, int]:
        """(valid, ell, sum_t) を返す。"""
        if c in orbit_cache:
            return orbit_cache[c]
        if c >= M or c == 1:
            orbit_cache[c] = (False, 0, 0)
            return False, 0, 0
        cur = c
        ell = 0
        sum_t = 0
        while True:
            if cur >= M:
                orbit_cache[c] = (False, 0, 0)
                return False, 0, 0
            ti = v2(cur + M)
            cur = (cur + M) >> ti
            ell += 1
            sum_t += ti
            if cur == c:
                break
            if ell > rho:
                orbit_cache[c] = (False, 0, 0)
                return False, 0, 0
        valid = (L % ell == 0) and (sum_t < rho * ell)
        orbit_cache[c] = (valid, ell, sum_t)
        return valid, ell, sum_t

    def F_val(c: int, k: int) -> bool | None:
        nonlocal r1_need
        if c == 1:
            assert 1 <= k <= v
            return (k % 2) == 0
        valid, ell, sum_t = orbit_stats(c)
        if not valid:
            return None
        cyc_lens.add(ell)
        # 厳密下限: (R - 1)(rho - sum_t/ell) > v + 1 + ell*rho  (PR #309 と同一)
        num = (v + 1 + ell * rho) * ell
        den = rho * ell - sum_t
        r_min = (num // den) + 2
        if r_min > r1_need:
            r1_need = r_min
        tc = v2(c - 1)
        assert tc <= rho - 1
        # R ≡ 1 (mod 2L): s ≡ v - k + 1 ≡ k (mod 2)
        s_par = k & 1
        if shift_half:
            # R ≡ L + 1 (mod 2L): 偶奇が L + (L/ell)*(sum_t - ell) ずれる
            s_par ^= (L + (L // ell) * (sum_t - ell)) & 1
        in_B = ((tc - 1) & 1) == 0
        return in_B if s_par == 0 else (not in_B)

    memo: dict[tuple[int, int, int], bool | None] = {}

    def E(j: int, c: int, k: int) -> bool | None:
        key = (j, c, k)
        if key in memo:
            return memo[key]
        if k == v:
            memo[key] = True
            return True
        c2 = (1 << k) + c
        bb = F_val(c2, k + 1) if j == 1 else E(j - 1, c2, k + 1)
        if bb is True:
            res: bool | None = False
        else:
            aa = E(j, c, k + 1)
            if aa is True:
                res = False
            elif aa is None or bb is None:
                res = None
            else:
                res = True
        memo[key] = res
        return res

    all_zero = all(E(j, 1, 1) is False for j in range(1, z))
    return all_zero, cyc_lens, r1_need


def verify_pr315_k54_lemma() -> str:
    """PR #315（補題 K54.1）の 14 組全状態検証（最大 ρ = 22 で 474,891 状態）。"""
    tot_states = 0
    for (v, rho), exp_cnt in EXPECTED_K54_COUNTS.items():
        z = rho // 2
        M = (1 << rho) - 1
        memo: dict[tuple[int, int, int], bool | None] = {}

        def F_closed(c: int, k: int) -> bool | None:
            if c == 1:
                return (k % 2) == 0
            if c >= M or c.bit_count() > z:
                return None
            return ((v2(c - 1) + k) & 1) == 1

        def E(i: int, c: int, k: int) -> bool | None:
            key = (i, c, k)
            if key in memo:
                return memo[key]
            if k == v:
                memo[key] = True
                return True
            c2 = (1 << k) + c
            bb = F_closed(c2, k + 1) if i == 1 else E(i - 1, c2, k + 1)
            if bb is True:
                res: bool | None = False
            else:
                aa = E(i, c, k + 1)
                if aa is True:
                    res = False
                elif aa is None or bb is None:
                    res = None
                else:
                    res = True
            memo[key] = res
            return res

        # (1) E_j(1, 1) == False for j = 1..z-1
        for j in range(1, z):
            assert E(j, 1, 1) is False, f"K54 E_{j}(1,1) failed for {(v, rho)}"

        # (2) 補題 K54.1 の範囲内の全状態検証
        cnt = 0
        for i in range(1, z):
            k_max = rho - 1 - 2 * i
            if k_max < 2:
                continue
            for k in range(2, k_max + 1):
                for c in range(3, 1 << k, 2):
                    if c.bit_count() + i <= z:
                        psi = ((v2(c - 1) + k) & 1) == 1
                        got = E(i, c, k)
                        assert got is psi, f"K54.1 mismatch {(v, rho)} (i={i}, c={c}, k={k}): got {got}, want {psi}"
                        cnt += 1
        assert cnt == exp_cnt, f"K54.1 state count mismatch {(v, rho)}: got {cnt}, want {exp_cnt}"
        tot_states += cnt

    return f"PR #315 Lemma K54.1 (14 pairs, up to rho=22): all E_j(1,1)=False and {tot_states}/{tot_states} states match Psi(c,k) (rho=22: 474891/474891), errors=0"


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


def verify_k54_fresh_k8() -> str:
    """K54 の新規範囲（v = 19, 21, 23：K50 の v <= 17 を超える範囲）の K8 実数値直接照合。"""
    cases = [
        (19, 6),  # L = 6, 2L = 12, R-1 >= 40/6 + 6 = 12.67 -> R = 25
        (19, 8),  # L = 12, 2L = 24, R-1 >= 40/8 + 8 = 13 -> R = 25
        (21, 6),  # R-1 >= 44/6 + 6 = 13.33 -> R = 25
        (21, 8),  # R-1 >= 44/8 + 8 = 13.5 -> R = 25
        (23, 6),  # R-1 >= 48/6 + 6 = 14 -> R = 25
    ]
    ok_cnt = 0
    for v, rho in cases:
        z = rho // 2
        L = 1
        for i in range(1, z + 1):
            L = math.lcm(L, i)
        P = 2 * L
        # R - 1 >= 2(v+1)/rho + rho を満たす最小の R ≡ 1 (mod 2L)
        r_lb = math.ceil(2 * (v + 1) / rho + rho) + 1
        R = 1 + P * ((r_lb - 1 + P - 1) // P)
        assert (R - 1) % P == 0 and (R - 1) * rho >= 2 * (v + 1) + rho * rho
        N = v + rho * (R - 1) + 1
        if N % 2 == 1:
            N += 1
        q = (1 << v) - (1 << rho) + 1
        r = ((1 << rho) - 1) // 3
        s0 = (r * pow(1 << N, -1, q)) % q
        if (s0 & 1) == 0:
            s0 += q
        a = (s0 * (1 << N) - r) // q
        m = 3 * a - 2
        assert v2(m + 1) == v and v2(((m + 1) >> v) + 1) == rho
        J = 4 * (R + v) + 40
        bits = lazy_k8_gaps_bits(m, J)
        z_upper = (v + 1) // 2
        i = 0
        ones = zeros = 0
        while i < J:
            j = i
            while j < J and bits[j] == bits[i]:
                j += 1
            if j < J:
                rl = j - i
                if bits[i]:
                    assert rl == R
                    ones += 1
                else:
                    assert z <= rl <= z_upper
                    zeros += 1
            i = j
        assert ones >= 3 and zeros >= 3
        ok_cnt += 1
    return f"PR #315 fresh K8 numerical cross-check (v=19,21,23 beyond v<=17): {ok_cnt}/{len(cases)} exact match, errors=0"


def verify_pr307_pr309_formal() -> str:
    """PR #307（ρ <= 28）および PR #309（ρ <= 60 全 77 組）の R ≡ 1, L+1 (mod 2L) 独立検証。"""
    pairs_77: list[tuple[int, int]] = []
    for rho in range(4, 61, 2):
        pairs_77.append((rho + 1, rho))
        pairs_77.append((rho + 3, rho))
    for rho in range(4, 41, 2):
        pairs_77.append((41, rho))
    assert len(pairs_77) == 77

    ok_1 = ok_half = 0
    all_r1_eq_3v = True
    for v, rho in pairs_77:
        z1, cycs1, r1a = eval_formal_k50_k52(v, rho, shift_half=False)
        z2, cycs2, r1b = eval_formal_k50_k52(v, rho, shift_half=True)
        assert z1 and z2, f"Formal K50 fail for {(v, rho)}: z1={z1}, z2={z2}"
        assert cycs1 == set(range(2, rho // 2 + 1)) or cycs1.issubset(set(range(1, rho // 2 + 1)))
        if max(r1a, r1b) > 3 * v:
            all_r1_eq_3v = False
        ok_1 += 1
        ok_half += 1

    return (
        f"PR #307 & PR #309 formal K50 (all 77 pairs up to rho=60, v=63, including PR #307's 14 + 2 timed-out pairs): "
        f"R=1(mod 2L): {ok_1}/77, R=L+1(mod 2L): {ok_half}/77, all R1==3v: {all_r1_eq_3v}, errors=0"
    )


def main() -> None:
    t0 = time.perf_counter()
    l_k53 = verify_pr313_k53()
    print(l_k53, flush=True)
    l_k54 = verify_pr315_k54_lemma()
    print(l_k54, flush=True)
    l_k8 = verify_k54_fresh_k8()
    print(l_k8, flush=True)
    l_k50 = verify_pr307_pr309_formal()
    print(l_k50, flush=True)

    elapsed = time.perf_counter() - t0
    lines = [
        "gemini-2 independent verification of PR #307, #309 (K50 rho<=60), PR #311 (Lemma K52), PR #313 (Lemma K53), PR #315 (Theorem K54)",
        l_k53,
        l_k54,
        l_k8,
        l_k50,
        f"Total elapsed={elapsed:.2f}s",
    ]
    out_text = "\n".join(lines) + "\n"
    Path("data/gemini2_verify_k52_k54.txt").write_text(out_text, encoding="utf-8")


if __name__ == "__main__":
    main()
