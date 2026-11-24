"""
PR #283（定理 K47：偶数 w <= v-1 の全類）および PR #285（定理 K47b：w = v の類）の
独立 Python 検証スクリプト。

- 査読済み定理 K8・K3 のみから書いた独立 K8 遅延評価器により、間隔列の先頭 m+2 連長 R を厳密計算する。
- PR #283（定理 K47）：
  1. 奇数 v = 3..13、偶数 ρ = 2..v-1、偶数 N = v+ρ+1..140 の全例（PR #283 の v<=11, N<=120 810 例を包含・拡張）で
     a 奇数・v2(m+1)=v・w=v2(u+1)=ρ・R = ceil((N-v)/ρ) を独立検証する。
  2. 非最小の正の奇数 s（s_min + 2q, s_min + 4q）でも定理が成立することを確認する（v = 3..11）。
- PR #285（定理 K47b）：
  1. 奇数 v = 3..21、偶数 N = 2v+2..240 の全 1,080 例で
     a 奇数・v2(m+1)=v・w=v2(u+1)=v・R = ceil((N-v)/(v+1)) を独立検証する。
  2. 非最小の正の奇数 σ（σ_min + 2Q, σ_min + 4Q）でも定理が成立することを確認する（v = 3..11）。
- さらに小規模例について PROBLEM.md のルール全探索ソルバーから直接 P 局面間隔列を生成し R 一致を確認する。

実行方法:
    python code/gemini2_verify_k47.py
出力:
    data/gemini2_verify_k47.txt
"""

from __future__ import annotations

import math
import time
from pathlib import Path


def v2(x: int) -> int:
    assert x > 0
    return (x & -x).bit_length() - 1


def first_zero_index_k8(m: int, limit: int) -> int:
    """K8 + K3 遅延評価により g_0 = ... = g_{R-1} = m+2, g_R = m+1 となる最小の R を厳密計算する。"""
    h = (m + 1) >> 1
    M = m + 2
    E_gap = m + 1
    gaps: list[int] = []
    memo: list[dict[int, bool]] = []
    for j in range(limit):
        memo.append({})
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
        if not in_h:
            return j
        gaps.append(M)
    raise AssertionError(f"no zero gap within limit={limit} for m={m}")


def first_zero_index_full_search(m: int, max_blocks: int) -> int:
    """PROBLEM.md の定義そのもの（1 <= k <= min(m, r), k != p）の全探索で
    開始局面 (n, 0) の P 局面間隔列の先頭 m+2 連長 R を求める。
    """
    N_max = (m + 2) * (max_blocks + 2) + 5
    # unique_win[r]:
    #   0  : 勝ち手なし（すべての p で P 局面、特に開始局面 (r, 0) が P 局面）
    #  k>0 : 唯一の勝ち手が k（p == k のときのみ P 局面）
    #  -1  : 勝ち手が 2 つ以上（すべての p で N 局面）
    unique_win = [0] * (N_max + 1)
    for r in range(1, N_max + 1):
        lim = min(m, r)
        w = 0
        for k in range(1, lim + 1):
            u = unique_win[r - k]
            # (r - k, k) が P 局面 ⇔ u == 0 または u == k
            if u == 0 or u == k:
                if w == 0:
                    w = k
                else:
                    w = -1
                    break
        unique_win[r] = w
    p_pos = [n for n in range(0, N_max + 1) if unique_win[n] == 0]
    gaps = [p_pos[i + 1] - p_pos[i] for i in range(len(p_pos) - 1)]
    for idx, g in enumerate(gaps):
        if g == m + 1:
            return idx
        assert g == m + 2, f"unexpected gap {g} for m={m}"
    raise AssertionError("not enough blocks")


def main() -> None:
    t0 = time.perf_counter()

    # 1. PR #283（定理 K47）：奇数 v = 3..13、偶数 2 <= rho <= v-1、偶数 N = v+rho+1..140
    k47_cnt = 0
    k47_pr283_subset = 0
    k47_nonmin_s = 0
    for v in range(3, 14, 2):
        for rho in range(2, v, 2):
            q = (1 << v) - (1 << rho) + 1
            r = ((1 << rho) - 1) // 3
            assert q + 3 * r == (1 << v) and 1 + 3 * r == (1 << rho)
            N_start = v + rho + 1
            if N_start % 2 == 1:
                N_start += 1
            for N in range(N_start, 141, 2):
                # s ≡ r * 2^{-N} (mod q) の最小正奇数代表
                s0 = (r * pow(1 << N, -1, q)) % q
                if (s0 & 1) == 0:
                    s0 += q
                s_list = [s0]
                if v <= 11 and N in (N_start, N_start + 10):
                    s_list.extend([s0 + 2 * q, s0 + 4 * q])
                for idx_s, s in enumerate(s_list):
                    assert (s * (1 << N) - r) % q == 0
                    a = (s * (1 << N) - r) // q
                    assert (a & 1) == 1
                    m = 3 * a - 2
                    assert v2(m + 1) == v
                    u = (m + 1) >> v
                    assert v2(u + 1) == rho
                    want_R = (N - v + rho - 1) // rho
                    R = first_zero_index_k8(m, want_R + 4)
                    assert R == want_R, f"K47 fail v={v}, rho={rho}, N={N}, s={s}: R={R}, want={want_R}"
                    if idx_s == 0:
                        k47_cnt += 1
                        if v <= 11 and N <= 120:
                            k47_pr283_subset += 1
                    else:
                        k47_nonmin_s += 1

    # 2. PR #285（定理 K47b）：奇数 v = 3..21、偶数 N = 2v+2..240（全 1,080 例）＋非最小 σ
    k47b_cnt = 0
    k47b_nonmin_sig = 0
    for v in range(3, 22, 2):
        rho = v + 1
        Q = (1 << v) - 1
        r = ((1 << rho) - 1) // 3
        assert -Q + 3 * r == (1 << v) and 1 + 3 * r == (1 << rho)
        for N in range(2 * v + 2, 241, 2):
            sig0 = (-r * pow(1 << N, -1, Q)) % Q
            if (sig0 & 1) == 0:
                sig0 += Q
            sig_list = [sig0]
            if v <= 11 and N in (2 * v + 2, 2 * v + 12):
                sig_list.extend([sig0 + 2 * Q, sig0 + 4 * Q])
            for idx_s, sig in enumerate(sig_list):
                assert (sig * (1 << N) + r) % Q == 0
                a = (sig * (1 << N) + r) // Q
                assert (a & 1) == 1
                m = 3 * a - 2
                assert v2(m + 1) == v
                u = (m + 1) >> v
                assert v2(u + 1) == v
                want_R = (N - v + rho - 1) // rho
                R = first_zero_index_k8(m, want_R + 4)
                assert R == want_R, f"K47b fail v={v}, N={N}, sig={sig}: R={R}, want={want_R}"
                if idx_s == 0:
                    k47b_cnt += 1
                else:
                    k47b_nonmin_sig += 1

    # 3. PROBLEM.md 全探索直接照合（小規模 4 例：K47 2 例 + K47b 2 例）
    fs_cases = [
        # K47: (v=3, rho=2, N=6 -> q=5, r=1, s=1, a=13? wait 64-1=63; s=3 -> 192-1=191; s=1 -> 64 mod 5 = 4 -> 4s=1 => s=4 -> s0=9: a=(9*64-1)/5=115, m=343)
        ("K47 v=3,rho=2,N=6", 3, 2, 6, False),
        ("K47 v=5,rho=2,N=8", 5, 2, 8, False),
        ("K47b v=3,N=8", 3, 4, 8, True),
        ("K47b v=3,N=10", 3, 4, 10, True),
    ]
    fs_ok = 0
    for label, v, rho, N, is_b in fs_cases:
        r = ((1 << rho) - 1) // 3
        if not is_b:
            q = (1 << v) - (1 << rho) + 1
            s = (r * pow(1 << N, -1, q)) % q
            if (s & 1) == 0:
                s += q
            a = (s * (1 << N) - r) // q
        else:
            Q = (1 << v) - 1
            sig = (-r * pow(1 << N, -1, Q)) % Q
            if (sig & 1) == 0:
                sig += Q
            a = (sig * (1 << N) + r) // Q
        m = 3 * a - 2
        want_R = (N - v + rho - 1) // rho
        R_fs = first_zero_index_full_search(m, want_R + 2)
        assert R_fs == want_R, f"full search mismatch {label} m={m}: R_fs={R_fs}, want={want_R}"
        fs_ok += 1

    elapsed = time.perf_counter() - t0
    lines = [
        "gemini-2 independent verification of PR #283 (Theorem K47) and PR #285 (Theorem K47b)",
        f"PR #283 Theorem K47 (odd v=3..13, even rho=2..v-1, even N<=140): {k47_cnt}/{k47_cnt} exact match (PR #283 v<=11,N<=120 subset: {k47_pr283_subset}/810), non-minimal odd s: {k47_nonmin_s}/{k47_nonmin_s}, errors=0",
        f"PR #285 Theorem K47b (odd v=3..21, even N=2v+2..240): {k47b_cnt}/1080 exact match, non-minimal odd sigma: {k47b_nonmin_sig}/{k47b_nonmin_sig}, errors=0",
        f"PROBLEM.md full-search direct cross-check (4 small K47/K47b cases): {fs_ok}/4 exact match, errors=0",
        f"Total elapsed={elapsed:.2f}s",
    ]
    out_text = "\n".join(lines) + "\n"
    Path("data/gemini2_verify_k47.txt").write_text(out_text, encoding="utf-8")
    print(out_text, end="")


if __name__ == "__main__":
    main()
