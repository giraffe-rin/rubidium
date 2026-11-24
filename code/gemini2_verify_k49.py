"""
PR #296（定理 K49・補題 K49.1：w = 4 の類は周期部分だけで数えても型が無限に多い）の
独立 Python 並列検証スクリプト。

- 査読済み定理 K8・K3・補題 Q_n のみから書いた独立 K8 遅延評価器を使用。
- 検証内容：
  1. PR #296 全範囲（奇数 v = 5..15、偶数 N = v+17..200、R = ceil((N-v)/4) 奇数、計 266 例）について、
     J = max(400, 10N) ブロック中の完結するすべての m+2 連が厳密に長さ R、
     すべての m+1 連が 2..ceil(v/2) に収まることを確認し、data/k49_rho4.txt の各 v の個数・範囲と照合する。
  2. 拡張確認：v = 17（N = 34..120、R 奇数）および非最小正奇数 s（s_0 + 2q, s_0 + 4q）でも
     全連が厳密に K49 の主張を満たすことを確認する。
  3. 補題 K49.1 の鎖検証：全 266 例について 3h/2 のブロック R からの一本道鎖を 1 段ずつ実数値追跡し、
     0 < d < 9a/5・d != h-1・(M+d)/2 <= m・段数 s = v + 2R - 3（偶数）・終点奇数（3h/2 ∈ S_R）を確認する。

実行方法:
    python code/gemini2_verify_k49.py
出力:
    data/gemini2_verify_k49.txt
"""

from __future__ import annotations

import os
import time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path


EXPECTED_PR296 = {
    5: (46, 2, 3),
    7: (45, 2, 3),
    9: (44, 2, 4),
    11: (44, 2, 4),
    13: (44, 2, 4),
    15: (43, 2, 5),
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


def check_one_k49(v: int, N: int, s: int) -> tuple[int, int]:
    q = (1 << v) - 15
    r = 5
    assert (s * (1 << N) - r) % q == 0
    a = (s * (1 << N) - r) // q
    assert a > 0 and (a & 1) == 1
    m = 3 * a - 2
    M = 3 * a
    h = (3 * a - 1) >> 1
    assert v2(m + 1) == v
    u = (m + 1) >> v
    assert v2(u + 1) == 4
    R = (N - v + 3) // 4
    assert (R & 1) == 1

    # 1. 補題 K49.1 の 3h/2 鎖を 1 段ずつ厳密検証（ブロック R -> 0）
    d = (3 * h) >> 1
    assert (3 * h) % 2 == 0 and d <= m
    j_blk = R
    steps = 0
    while j_blk > 0:
        assert 0 < d <= m and d != h - 1
        if (d & 1) == 0:
            d >>= 1
        else:
            assert d < (9 * a) // 5 + 1
            e = (M + d) >> 1
            assert e <= m
            d = e
            j_blk -= 1
        steps += 1
    assert steps == v + 2 * R - 3 and (steps & 1) == 0
    assert (d & 1) == 1  # 終点奇数 => ブロック B で入る => 3h/2 ∈ S_{B+R}

    # 2. K8 遅延評価で J = max(400, 10N) ブロック中の全完結連を検証
    J = max(400, 10 * N)
    bits = lazy_k8_gaps_bits(m, J)
    zmin = 10**9
    zmax = 0
    ones_cnt = 0
    zeros_cnt = 0
    i = 0
    z_upper = (v + 1) // 2
    while i < J:
        j = i
        while j < J and bits[j] == bits[i]:
            j += 1
        if j < J:
            run_len = j - i
            if bits[i]:
                assert run_len == R, f"1-run mismatch v={v}, N={N}, s={s}: got {run_len}, want {R}"
                ones_cnt += 1
            else:
                assert 2 <= run_len <= z_upper, f"0-run mismatch v={v}, N={N}, s={s}: got {run_len}"
                zmin = min(zmin, run_len)
                zmax = max(zmax, run_len)
                zeros_cnt += 1
        i = j
    assert ones_cnt > 0 and zeros_cnt > 0
    return zmin, zmax


def worker_v(v: int) -> tuple[int, int, int, int, int]:
    q = (1 << v) - 15
    r = 5
    N_max = 200 if v <= 15 else 120
    cnt = 0
    nonmin_cnt = 0
    zmin = 10**9
    zmax = 0
    for N in range(v + 17, N_max + 1, 2):
        R = (N - v + 3) // 4
        if (R & 1) == 0:
            continue
        s0 = (r * pow(1 << N, -1, q)) % q
        if (s0 & 1) == 0:
            s0 += q
        mn, mx = check_one_k49(v, N, s0)
        zmin = min(zmin, mn)
        zmax = max(zmax, mx)
        cnt += 1
        if v <= 15 and cnt <= 2:
            for extra_s in (s0 + 2 * q, s0 + 4 * q):
                check_one_k49(v, N, extra_s)
                nonmin_cnt += 1
    return v, cnt, zmin, zmax, nonmin_cnt


def main() -> None:
    t0 = time.perf_counter()
    workers = max(1, min(8, os.cpu_count() or 4))
    with ProcessPoolExecutor(max_workers=workers) as pool:
        results = list(pool.map(worker_v, [5, 7, 9, 11, 13, 15, 17]))

    tot_pr296 = 0
    tot_nonmin = 0
    v17_cnt = 0
    detail_lines: list[str] = []
    for v, cnt, zmin, zmax, nonmin_cnt in results:
        if v <= 15:
            assert (cnt, zmin, zmax) == EXPECTED_PR296[v], (
                f"v={v}: got {(cnt, zmin, zmax)}, want {EXPECTED_PR296[v]}"
            )
            tot_pr296 += cnt
            tot_nonmin += nonmin_cnt
            detail_lines.append(
                f"  v={v:2d} (q={(1<<v)-15:5d}): {cnt}/{cnt} proved, 0-run range={zmin}..{zmax} (matches PR #296), non-min s={nonmin_cnt}/{nonmin_cnt}"
            )
        else:
            v17_cnt = cnt
            detail_lines.append(
                f"  v={v:2d} (q={(1<<v)-15:6d}, extra N<=120): {cnt}/{cnt} proved, 0-run range={zmin}..{zmax}"
            )

    assert tot_pr296 == 266
    elapsed = time.perf_counter() - t0
    lines = [
        "gemini-2 independent verification of PR #296 (Theorem K49 & Lemma K49.1: w = 4 periodic part has infinitely many types)",
        f"PR #296 full range (odd v=5..15, even N=v+17..200, odd R): {tot_pr296}/266 exact match (Lemma K49.1 chain + all completed runs in max(400, 10N) blocks), errors=0",
        f"Extra checks: non-minimal positive odd s ({tot_nonmin}/{tot_nonmin}) and v=17 ({v17_cnt}/{v17_cnt}), errors=0",
        *detail_lines,
        f"Total elapsed={elapsed:.2f}s",
    ]
    out_text = "\n".join(lines) + "\n"
    Path("data/gemini2_verify_k49.txt").write_text(out_text, encoding="utf-8")
    print(out_text, end="", flush=True)


if __name__ == "__main__":
    main()
