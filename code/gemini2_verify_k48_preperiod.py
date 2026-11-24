"""
PR #289（K47・K47b 875 例の prove3 確定・前周期調査）および PR #292（補題 K48・系 K48b：
v = 5..11 全 752 例・15,762 位置＋v = 3 拡張）の独立 Python 並列検証スクリプト。

- 査読済み定理 K8・K3・補題 Q_n のみから書いた独立 K8 遅延評価器および厳密 prove3_strict を使用。
- PR #289：v = 3..11、ρ ∈ {2, 4, ..., v-1, v+1}、偶数 N ≤ 100 の全 875 例を並列再検証し、
  確定 875/875・前周期空 793・周期内最大 1 連長 >= R 852 の完全一致を確認する。
- PR #292：v = 5..11、偶数 ρ ≤ v-1、偶数 N ≤ 120 の全 752 例について、J = max(400, 8N) ブロック中の
  すべての 0^{ρ/2} 1 位置（15,762 箇所）で後続の 1 の連長が厳密に R = ceil((N-v)/ρ) に一致することを確認する
  （さらに v = 3, ρ = 2 の 58 例も追加確認）。

実行方法:
    python code/gemini2_verify_k48_preperiod.py
出力:
    data/gemini2_verify_k48_preperiod.txt
"""

from __future__ import annotations

import os
import time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path


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


def guess_period(bits: list[bool]) -> tuple[int, int] | None:
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


def prove3_strict(
    m: int, pre: list[bool], w: list[bool], max_rounds: int = 20000, max_facts: int = 3_000_000
) -> tuple[bool, int]:
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
        return False, 0
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
            return False, base_count

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
                return False, memo_count + base_count
        if unk_d is not None:
            A[unk_d] = eval_T(b, unk_d)
            continue
        for d, ev in list(A.items()):
            val, unk = eval_S(L, d)
            if unk is not None:
                unk_d = unk
                break
            if val != ev:
                return False, memo_count + base_count
        if unk_d is not None:
            A[unk_d] = eval_T(b, unk_d)
            continue
        return True, memo_count + base_count
    return False, base_count


def worker_pr289(args: tuple[int, int]) -> tuple[int, int, int, int, int]:
    """(v, rho) の全偶数 N <= 100 を prove3_strict で検証。"""
    v, rho = args
    q = (1 << v) - (1 << rho) + 1
    r = ((1 << rho) - 1) // 3
    N_start = 2 * v + 2 if rho == v + 1 else v + rho + 1
    if N_start % 2 == 1:
        N_start += 1
    cnt = ok_cnt = p0_cnt = run_ge_cnt = max_f = 0
    for N in range(N_start, 101, 2):
        X = 1 << N
        # q*a + r = s*X, |s| 最小の奇数で a > 0 奇数
        abs_q = abs(q)
        if q > 0:
            s0 = (r * pow(X, -1, abs_q)) % abs_q
            if (s0 & 1) == 0:
                s0 += abs_q
            a = (s0 * X - r) // q
        else:
            sig0 = (-r * pow(X, -1, abs_q)) % abs_q
            if (sig0 & 1) == 0:
                sig0 += abs_q
            a = (sig0 * X + r) // abs_q
        assert a > 0 and (a & 1) == 1
        m = 3 * a - 2
        R = (N - v + rho - 1) // rho
        cnt += 1
        pre: list[bool] = []
        w: list[bool] = []
        for J in (400, 800, 1600):
            bits = lazy_k8_gaps_bits(m, J)
            pl = guess_period(bits)
            if pl is not None and pl[0] + 4 * pl[1] <= J:
                pre = bits[: pl[0]]
                w = bits[pl[0] : pl[0] + pl[1]]
                break
        assert len(w) > 0, f"PR#289 fail guess v={v}, rho={rho}, N={N}"
        hit = False
        for c in (1, 2, 4, 8):
            for k in (1, 2, 3, 4):
                ok, nf = prove3_strict(m, pre + w * (c - 1), w * k)
                if ok:
                    hit = True
                    max_f = max(max_f, nf)
                    break
            if hit:
                break
        assert hit, f"PR#289 prove3_strict fail v={v}, rho={rho}, N={N}"
        ok_cnt += 1
        if len(pre) == 0:
            p0_cnt += 1
        k0 = w.index(False)
        rot = w[k0:] + w[:k0]
        mx = cur = 0
        for bit in rot:
            if bit:
                cur += 1
                if cur > mx:
                    mx = cur
            else:
                cur = 0
        if mx >= R:
            run_ge_cnt += 1
    return cnt, ok_cnt, p0_cnt, run_ge_cnt, max_f


def worker_pr292(args: tuple[int, int]) -> tuple[int, int, int, int, int]:
    """(v, rho) の全偶数 N <= 120 で 0^{rho/2} 1 の後続 1 連長 == R を検証。"""
    v, rho = args
    q = (1 << v) - (1 << rho) + 1
    r = ((1 << rho) - 1) // 3
    z = rho // 2
    N_start = v + rho + 1
    if N_start % 2 == 1:
        N_start += 1
    cnt = pos_cnt = bad_cnt = late_cnt = 0
    for N in range(N_start, 121, 2):
        X = 1 << N
        s0 = (r * pow(X, -1, q)) % q
        if (s0 & 1) == 0:
            s0 += q
        a = (s0 * X - r) // q
        m = 3 * a - 2
        R = (N - v + rho - 1) // rho
        J = max(400, 8 * N)
        bits = lazy_k8_gaps_bits(m, J)
        cnt += 1
        has_late = False
        for B in range(z, J - R):
            if bits[B] and all(not bits[B - t] for t in range(1, z + 1)):
                # B から始まる 1 連の長さを数える
                run_len = 0
                while B + run_len < J and bits[B + run_len]:
                    run_len += 1
                pos_cnt += 1
                if run_len != R:
                    bad_cnt += 1
                if B >= J // 2:
                    has_late = True
        if has_late:
            late_cnt += 1
    return v, cnt, pos_cnt, bad_cnt, late_cnt


def main() -> None:
    t0 = time.perf_counter()
    workers = max(1, min(10, os.cpu_count() or 4))

    pairs_289 = []
    for v in range(3, 12, 2):
        for rho in list(range(2, v, 2)) + [v + 1]:
            pairs_289.append((v, rho))

    pairs_292 = []
    for v in range(3, 12, 2):
        for rho in range(2, v, 2):
            pairs_292.append((v, rho))

    with ProcessPoolExecutor(max_workers=workers) as pool:
        res_289 = list(pool.map(worker_pr289, pairs_289))
        res_292 = list(pool.map(worker_pr292, pairs_292))

    t_n = sum(x[0] for x in res_289)
    t_ok = sum(x[1] for x in res_289)
    t_p0 = sum(x[2] for x in res_289)
    t_run = sum(x[3] for x in res_289)
    t_mf = max(x[4] for x in res_289)
    assert (t_n, t_ok, t_p0, t_run) == (875, 875, 793, 852), f"PR#289 mismatch: {(t_n, t_ok, t_p0, t_run)}"

    k48_v5_m = sum(x[1] for x in res_292 if x[0] >= 5)
    k48_v5_pos = sum(x[2] for x in res_292 if x[0] >= 5)
    k48_v5_bad = sum(x[3] for x in res_292 if x[0] >= 5)
    k48_v3_m = sum(x[1] for x in res_292 if x[0] == 3)
    k48_v3_pos = sum(x[2] for x in res_292 if x[0] == 3)
    k48_v3_bad = sum(x[3] for x in res_292 if x[0] == 3)
    assert k48_v5_m == 752 and k48_v5_pos == 15762 and k48_v5_bad == 0
    assert k48_v3_bad == 0

    elapsed = time.perf_counter() - t0
    lines = [
        "gemini-2 independent verification of PR #289 (K47/K47b 875 cases prove3) and PR #292 (Lemma K48 / Cor K48b)",
        f"PR #289 (v=3..11, N<=100): total={t_n}/875, proved={t_ok}/875, empty_preperiod={t_p0}/793, max_run>=R={t_run}/852, maxFacts={t_mf}, errors=0",
        f"PR #292 Lemma K48 (v=5..11, N<=120): m_count={k48_v5_m}/752, positions_checked={k48_v5_pos}/15762, mismatches={k48_v5_bad}",
        f"PR #292 extra boundary v=3, rho=2 (N<=120): m_count={k48_v3_m}, positions_checked={k48_v3_pos}, mismatches={k48_v3_bad}",
        f"Total elapsed={elapsed:.2f}s",
    ]
    out_text = "\n".join(lines) + "\n"
    Path("data/gemini2_verify_k48_preperiod.txt").write_text(out_text, encoding="utf-8")
    print(out_text, end="", flush=True)


if __name__ == "__main__":
    main()
