"""
PROBLEM.md の定義のみから書いた全探索ソルバーおよび査読済み定理 K8（PR #111）の
独立実装により、PR #219（定理 K41）、PR #227（定理 K41c）、PR #221（定理 K42・系 K42b）
を独立検証する。

実行方法:
    python code/gemini2_verify_k41_k42.py
出力:
    data/gemini2_verify_k41_k42.txt
"""

from __future__ import annotations

import math
import time
from pathlib import Path


def v2(x: int) -> int:
    assert x > 0
    return (x & -x).bit_length() - 1


def solve_full_search_S(m: int, n_blocks: int) -> tuple[list[set[int]], list[int]]:
    """PROBLEM.md の定義のみから全探索 DP で各ブロックの S_j と間隔 g_j を抽出する。"""
    max_r = (n_blocks + 2) * (m + 2)
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
    assert len(a_rows) > n_blocks
    S_list: list[set[int]] = []
    gaps: list[int] = []
    for j in range(n_blocks):
        aj = a_rows[j]
        gaps.append(a_rows[j + 1] - aj)
        Sj = {d for d in range(1, m + 1) if not win[aj + d][d]}
        S_list.append(Sj)
    return S_list, gaps


def k8_step_mask(m: int, prev_mask: int | None, prev_g: int | None) -> tuple[int, int]:
    """査読済み定理 K3・K8（PR #111）のビットマスク実装。bit d が 1 ⇔ d ∈ S_j。"""
    h = (m + 1) // 2
    mask = 0
    if prev_mask is None:
        for d in range(1, m + 1):
            if (v2(d) & 1) == 0:
                mask |= 1 << d
    else:
        g = prev_g
        odd_g = (g == m + 2)
        for d in range(1, m + 1):
            if (d & 1) == 0 and ((mask >> (d >> 1)) & 1):
                continue
            if ((g + d) & 1) == 0:
                e = (g + d) >> 1
                if 1 <= e <= m and ((prev_mask >> e) & 1):
                    continue
            if odd_g and d == h - 1:
                continue
            mask |= 1 << d
    g_next = (m + 2) if ((m & 1) == 1 and ((mask >> h) & 1)) else (m + 1)
    return mask, g_next


def k41_formulas(m: int) -> tuple[int, int]:
    """偶数 m >= 2 について、定理 K41 の P（軌道式）と定理 K41c の厳密周期 λ を計算する。"""
    assert m >= 2 and m % 2 == 0
    n = m + 1
    # 1. ψ が D = {1, 3, ..., n-2} 上の置換であることを直接確認
    D = list(range(1, n, 2))
    psi: dict[int, int] = {}
    k_val: dict[int, int] = {}
    for d in D:
        e = (n + d) // 2
        t = v2(e)
        x = e >> t
        psi[d] = x
        k_val[d] = t + 1
        assert d == (1 << (t + 1)) * x - n
    assert set(psi.values()) == set(D)

    # 2. 軌道 O（r ↦ 2r mod n）による K41 の P
    vis_r = set()
    P_orbit = 1
    for r in range(1, n):
        if r in vis_r:
            continue
        cur = r
        o = 0
        ell = 0
        while cur not in vis_r:
            vis_r.add(cur)
            o += 1
            if cur & 1:
                ell += 1
            cur = (2 * cur) % n
        assert ell >= 1
        P_orbit = math.lcm(P_orbit, ell if (o % 2 == 0) else 2 * ell)

    # 3. ψ の巡回による K41 の P_psi および K41c の厳密 λ
    vis_d = set()
    P_psi = 1
    lam_exact = 1
    for d in D:
        if d in vis_d:
            continue
        cyc = []
        cur = d
        while cur not in vis_d:
            vis_d.add(cur)
            cyc.append(cur)
            cur = psi[cur]
        ell = len(cyc)
        ks = [k_val[x] for x in cyc]
        o = sum(ks)
        P_psi = math.lcm(P_psi, ell if (o % 2 == 0) else 2 * ell)
        par = [k & 1 for k in ks]
        # 最小周期 π_C
        pi_c = ell
        for p in range(1, ell + 1):
            if ell % p == 0 and all(par[i] == par[i % p] for i in range(ell)):
                pi_c = p
                break
        sigma = sum(par[:pi_c]) & 1
        lam_c = pi_c if sigma == 0 else 2 * pi_c
        lam_exact = math.lcm(lam_exact, lam_c)

    assert P_orbit == P_psi
    assert P_orbit % lam_exact == 0
    return P_orbit, lam_exact


def fast_even_step(m: int, prev_odd_bits: int, psi_inv_table: list[tuple[int, int]]) -> int:
    """偶数 m における R の 1 ブロック遷移（奇数ビットのみ）。"""
    # psi_inv_table[idx] = (next_idx, flip_bit) for odd d = 2*idx + 1
    nxt = 0
    for idx, (target_idx, flip) in enumerate(psi_inv_table):
        bit = ((prev_odd_bits >> target_idx) & 1) ^ flip
        if bit:
            nxt |= 1 << idx
    return nxt


def exact_period_from_R_even(m: int) -> tuple[int, int]:
    """偶数 m について、ブロック 0（全奇数 = 1）から直接 R で状態遷移し、
    真の最小周期と前周期 μ = 0（ブロック 0 から純周期的）を確認する。
    """
    n = m + 1
    half = m // 2
    table = []
    for idx in range(half):
        d = 2 * idx + 1
        e = (n + d) // 2
        t = v2(e)
        x = e >> t
        table.append((x >> 1, (1 + t) & 1))
    s0 = (1 << half) - 1
    # まず K8 のフル実装と 5 ブロック完全一致を確認
    mask, g = None, None
    cur = s0
    for j in range(6):
        mask, g = k8_step_mask(m, mask, g)
        assert g == m + 1
        if j > 0:
            cur = fast_even_step(m, cur, table)
        for idx in range(half):
            d = 2 * idx + 1
            assert ((mask >> d) & 1) == ((cur >> idx) & 1)
    # ブロック 0 から直接 s0 に戻る最小のステップ数を探索（上限 200000）
    cur = s0
    for step in range(1, 200001):
        cur = fast_even_step(m, cur, table)
        if cur == s0:
            return 0, step
    return -1, -1


def main() -> None:
    t0 = time.perf_counter()

    # 1. PROBLEM.md 定義のみからの全探索検証
    # (a) 偶数 m = 2, 4, 6, 8, 10, 12, 14: 状態 S_0 == S_lambda かつ λ == K41c
    fs_even_ok = 0
    for m in (2, 4, 6, 8, 10, 12, 14):
        P, lam = k41_formulas(m)
        S_list, gaps = solve_full_search_S(m, lam + 3)
        assert all(g == m + 1 for g in gaps)
        assert S_list[lam] == S_list[0]
        assert all(S_list[j] != S_list[0] for j in range(1, lam))
        fs_even_ok += 1

    # (b) v2(m+1) 偶数 >= 2 の奇数 m: m = 3 (v=2,u=1), 11 (v=2,u=3), 15 (v=4,u=1), 19 (v=2,u=5), 27 (v=2,u=7), 47 (v=4,u=3)
    fs_k42_ok = 0
    for m in (3, 11, 15, 19, 27, 47):
        v = v2(m + 1)
        u = (m + 1) >> v
        mp = u - 1
        S_m, g_m = solve_full_search_S(m, 12)
        assert all(g == m + 1 for g in g_m)
        S_mp = solve_full_search_S(mp, 12)[0] if mp >= 2 else None
        for j in range(12):
            for d in range(1, m + 1):
                b = v2(d)
                if b <= v - 1:
                    assert (d in S_m[j]) == (b % 2 == 0)
                else:
                    assert S_mp is not None
                    dp = d >> v
                    assert (d in S_m[j]) == (dp in S_mp[j])
        fs_k42_ok += 1

    # 2. K41 & K41c: 偶数 2 <= m <= 200 の全 100 個（m = 132 の λ=5544 < P=27720 を含む）
    k41_total = 0
    k41_direct_checked = 0
    m132_info = ""
    for m in range(2, 201, 2):
        P, lam = k41_formulas(m)
        k41_total += 1
        if m == 132:
            assert P == 27720 and lam == 5544
            m132_info = f"m=132: P={P}, lam={lam}"
        if lam <= 60000:
            mu, actual_lam = exact_period_from_R_even(m)
            assert mu == 0 and actual_lam == lam, f"K41c fail m={m}: got ({mu},{actual_lam}), want (0,{lam})"
            k41_direct_checked += 1

    # 3. K42: v = 2, 4, 6、奇数 u <= 61（u = 1 を含む全 93 個、各 40 ブロック）で (1)(2)(3) 全事実検査
    k42_m_count = 0
    k42_fact_checks = 0
    for v in (2, 4, 6):
        for u in range(1, 62, 2):
            m = (1 << v) * u - 1
            mp = u - 1
            mask_m, gm = None, None
            mask_mp, gmp = None, None
            for j in range(40):
                mask_m, gm = k8_step_mask(m, mask_m, gm)
                assert gm == m + 1
                if mp >= 2:
                    mask_mp, gmp = k8_step_mask(mp, mask_mp, gmp)
                    assert gmp == mp + 1
                for d in range(1, m + 1):
                    b = v2(d)
                    bit_m = (mask_m >> d) & 1
                    if b <= v - 1:
                        assert bit_m == (1 if b % 2 == 0 else 0)
                    else:
                        dp = d >> v
                        assert bit_m == ((mask_mp >> dp) & 1)
                    k42_fact_checks += 1
            k42_m_count += 1

    elapsed = time.perf_counter() - t0
    lines = [
        "gemini-2 independent verification of PR #219 (K41), PR #227 (K41c), PR #221 (K42/K42b)",
        f"Full-search (PROBLEM.md only): even m ({fs_even_ok} cases, m=2..14) and K42 ({fs_k42_ok} cases, m=3,11,15,19,27,47): errors=0",
        f"K41 & K41c (even 2<=m<=200): formula/orbit match={k41_total}/100, direct R exact-period match={k41_direct_checked} ({m132_info}), errors=0",
        f"K42 (v=2,4,6, odd u<=61 including u=1): m_count={k42_m_count}, 40 blocks each, total_fact_checks={k42_fact_checks}, errors=0",
        f"elapsed: {elapsed:.2f}s",
    ]
    out_text = "\n".join(lines) + "\n"
    Path("data/gemini2_verify_k41_k42.txt").write_text(out_text, encoding="utf-8")
    print(out_text, end="")


if __name__ == "__main__":
    main()
