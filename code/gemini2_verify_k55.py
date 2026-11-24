"""
PR #317（定理 K55：w = v の類も周期部分だけで数えて型が無限に多い）の独立 Python 検証スクリプト。

1. (b′) 回転不等式の全数検証：奇数 v = 3..17（ρ = v + 1, Q = 2^v - 1, 3r = 2^ρ - 1）について、
   c < 2^{ρ-1}・popcount(c) <= z の全入口 c（v = 17 で 39,202 個）および 2 周分の全奇数の点
   （v = 17 で 602,692 点）で b*2^{v+S} + c*Q < 3r*2^{v+S} と巡回シフト一致を全数確認する。
2. 補題 K54.1 の (v, v+1) 検証：v = 3, 5, ..., 21 の全 10 組で E_j(1, 1) = False（j = 1..z-1）と
   補題 K54.1 範囲内の全状態での E_i(c, k) = Ψ(c, k) 一致を確認する。
3. 独立 K8 遅延評価による実数値直接照合：v = 3, 5, 7, 9（各 R ≡ 1 (mod 2L), R-1 >= ρ+4+2v/ρ、
   複数 e および非最小正奇数 σ も含む）について、すべての完結 m+2 連が厳密に長さ R、
   すべての完結 m+1 連が厳密に長さ z = (v+1)/2 であることを直接検証する。

実行方法:
    python code/gemini2_verify_k55.py
出力:
    data/gemini2_verify_k55.txt
"""

from __future__ import annotations

import math
import time
from pathlib import Path


EXPECTED_K55_POINTS = {
    3: (2, 8),
    5: (10, 52),
    7: (41, 274),
    9: (162, 1348),
    11: (637, 6394),
    13: (2509, 29594),
    15: (9907, 134502),
    17: (39202, 602692),
}


def v2(x: int) -> int:
    assert x > 0
    return (x & -x).bit_length() - 1


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


def verify_b_prime() -> str:
    tot_entries = 0
    tot_pts = 0
    for v in range(3, 18, 2):
        rho = v + 1
        z = rho // 2
        Q = (1 << v) - 1
        R3 = (1 << rho) - 1
        nc = np = 0
        for c in range(3, 1 << (rho - 1), 2):
            p = c.bit_count()
            if p > z:
                continue
            nc += 1
            assert c < (1 << v)
            b = c
            S = 0
            for _ in range(2 * p):
                x = b + R3
                t = v2(x)
                nb = x >> t
                rot_b = ((b >> t) | ((b << (rho - t)) & R3)) & R3
                assert nb == rot_b
                b = nb
                S += t
                np += 1
                # 厳密不等式 b * 2^{v+S} + c * Q < 3r * 2^{v+S}
                shift = v + S
                assert (b << shift) + c * Q < (R3 << shift)
        assert (nc, np) == EXPECTED_K55_POINTS[v], f"v={v}: got {(nc, np)}, want {EXPECTED_K55_POINTS[v]}"
        tot_entries += nc
        tot_pts += np
    return f"PR #317 (b') rotation inequality (v=3..17): entries={tot_entries}, odd_points={tot_pts} (v=17: 39202 / 602692), errors=0"


def verify_k54_for_k55() -> str:
    tot_states = 0
    for v in range(3, 22, 2):
        rho = v + 1
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

        for j in range(1, z):
            assert E(j, 1, 1) is False

        for i in range(1, z):
            k_max = rho - 1 - 2 * i
            if k_max < 2:
                continue
            for k in range(2, k_max + 1):
                for c in range(3, 1 << k, 2):
                    if c.bit_count() + i <= z:
                        psi = ((v2(c - 1) + k) & 1) == 1
                        assert E(i, c, k) is psi
                        tot_states += 1
    return f"PR #317 Lemma K54.1 for (v, v+1) (v=3..21, 10 pairs): all E_j(1,1)=False and {tot_states}/{tot_states} states match Psi, errors=0"


def verify_k55_k8_direct() -> str:
    # v = 3, 5, 7, 9 で定理 K55 の条件 (R ≡ 1 mod 2L, R - 1 >= rho + 4 + 2v/rho) を満たす実数値照合
    checked = 0
    for v in (3, 5, 7, 9):
        rho = v + 1
        z = rho // 2
        Q = (1 << v) - 1
        r = ((1 << rho) - 1) // 3
        L = 1
        for i in range(1, z + 1):
            L = math.lcm(L, i)
        P = 2 * L
        r_min = math.ceil(rho + 4 + 2 * v / rho) + 1
        R = 1 + P * ((r_min - 1 + P - 1) // P)
        assert (R - 1) % P == 0 and (R - 1) * rho >= rho * (rho + 4) + 2 * v
        # 複数の奇数 e ∈ {1, rho-1} と非最小 σ も検証
        e_list = [1, rho - 1] if v <= 7 else [1]
        for e in e_list:
            N = v + rho * (R - 1) + e
            assert N % 2 == 0 and (N - v + rho - 1) // rho == R
            sig0 = (-r * pow(1 << N, -1, Q)) % Q
            if (sig0 & 1) == 0:
                sig0 += Q
            sigs = [sig0, sig0 + 2 * Q] if (v <= 5 and e == 1) else [sig0]
            for sig in sigs:
                a = (sig * (1 << N) + r) // Q
                m = 3 * a - 2
                assert v2(m + 1) == v and v2(((m + 1) >> v) + 1) == v
                J = 4 * (R + z) + 20
                bits = lazy_k8_gaps_bits(m, J)
                i = 0
                ones = zeros = 0
                while i < J:
                    j = i
                    while j < J and bits[j] == bits[i]:
                        j += 1
                    if j < J:
                        rl = j - i
                        if bits[i]:
                            assert rl == R, f"K55 1-run fail v={v}, R={R}, e={e}: {rl}"
                            ones += 1
                        else:
                            assert rl == z, f"K55 0-run fail v={v}, R={R}, e={e}: {rl} != {z}"
                            zeros += 1
                    i = j
                assert ones >= 3 and zeros >= 3
                checked += 1
    return f"PR #317 direct K8 lazy cross-check (v=3,5,7,9, multiple e & non-minimal sigma): {checked}/{checked} exact match (all 1-runs=R, all 0-runs=(v+1)/2), errors=0"


def main() -> None:
    t0 = time.perf_counter()
    l1 = verify_b_prime()
    print(l1, flush=True)
    l2 = verify_k54_for_k55()
    print(l2, flush=True)
    l3 = verify_k55_k8_direct()
    print(l3, flush=True)
    elapsed = time.perf_counter() - t0
    lines = [
        "gemini-2 independent verification of PR #317 (Theorem K55: w = v periodic part has infinitely many types)",
        l1,
        l2,
        l3,
        f"Total elapsed={elapsed:.2f}s",
    ]
    out_text = "\n".join(lines) + "\n"
    Path("data/gemini2_verify_k55.txt").write_text(out_text, encoding="utf-8")


if __name__ == "__main__":
    main()
