"""
査読済み定理 K8・K3・補題 Q_n（PR #111, #202）のみから書いた厳密独立 Python 検証器（prove3_strict）により、
PR #243（prove3 健全性・奇数 5 <= m <= 3000 全 1498 例・2^40 < m < 2^41 無作為 200 例×2 + 独立シード）、
PR #245（5 <= m <= 2^20 の v2(m+1) 奇数全 349,524 例）、
PR #249（2^20 < m <= 2^22 の v2(m+1) 奇数全 1,048,576 例）を独立に全数検証する。

実行方法:
    python code/gemini2_verify_prove3_coverage.py
出力:
    data/gemini2_verify_prove3_coverage.txt
"""

from __future__ import annotations

import os
import random
import sys
import time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path


def v2(x: int) -> int:
    return (x & -x).bit_length() - 1


def lazy_k8_gaps_bits(m: int, count: int) -> list[bool]:
    """K8 遅延評価によりブロック 0..count-1 の間隔（True: m+2, False: m+1）を厳密計算する。"""
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
                mj[d] = (((d & -d).bit_length() - 1) & 1) == 0
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


def find_period(bits: list[bool], max_L: int, max_p: int) -> tuple[int, int] | None:
    n = len(bits)
    lim_L = min(max_L, n // 3)
    for L in range(1, lim_L + 1):
        lim_p = min(max_p, n - 3 * L)
        for p in range(0, lim_p + 1):
            ok = True
            for i in range(p, n - L):
                if bits[i] != bits[i + L]:
                    ok = False
                    break
            if ok:
                return p, L
    return None


def canonicalize(pre: list[bool], w: list[bool]) -> tuple[list[bool], list[bool]]:
    """pre + w^∞ を表す最小周期・最小前周期へ正規化する（文字列恒等変形）。"""
    L = len(w)
    for d in range(1, L // 2 + 1):
        if L % d == 0:
            sub = w[:d]
            if all(w[i] == sub[i % d] for i in range(L)):
                w = sub
                L = d
                break
    p = len(pre)
    w_cur = list(w)
    while p > 0 and pre[p - 1] == w_cur[-1]:
        p -= 1
        w_cur = [w_cur[-1]] + w_cur[:-1]
    return pre[:p], w_cur


def prove3_strict(
    m: int,
    pre: list[bool],
    w: list[bool],
    max_rounds: int = 20000,
    max_facts: int = 3_000_000,
) -> tuple[bool, str, int, int]:
    """厳密版 prove3：m 奇数必須・上限超過時は即時 RuntimeError・サイレント通過なし。"""
    if m < 3 or (m & 1) == 0:
        return False, "m must be odd >= 3", 0, 0
    p = len(pre)
    L = len(w)
    if L == 0:
        return False, "empty period", 0, 0
    b = p + L
    h = (m + 1) >> 1
    M = m + 2
    E_gap = m + 1
    v = (m + 1 & -(m + 1)).bit_length() - 1

    # word_bits[0 .. b + L]
    word_bits: list[bool] = [False] * (b + L + 1)
    for i in range(p):
        word_bits[i] = pre[i]
    for i in range(p, b + L + 1):
        word_bits[i] = w[(i - p) % L]

    # (0) ブロック 0 の間隔確認（K3）
    g0 = (((h & -h).bit_length() - 1) & 1) == 0
    if g0 != word_bits[0]:
        return False, "g0 mismatch", 0, 0

    gaps_abs = [M if bit else E_gap for bit in word_bits]

    # (0″) ブロック 0..b を K3 + R で厳密評価（上限超過は即例外）
    base_memo: list[dict[int, bool]] = [{} for _ in range(b + 1)]
    base_count = 0

    def eval_T(start_j: int, start_d: int) -> bool:
        nonlocal base_count
        stack: list[tuple[int, int]] = [(start_j, start_d)]
        while stack:
            j, d = stack[-1]
            mj = base_memo[j]
            if d in mj:
                stack.pop()
                continue
            if base_count >= max_facts:
                raise RuntimeError("base max_facts exceeded")
            if j == 0:
                mj[d] = (((d & -d).bit_length() - 1) & 1) == 0
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
        return base_memo[start_j][start_d]

    for j in range(1, b + 1):
        if eval_T(j, h) != word_bits[j]:
            return False, "prefix gap mismatch", 0, base_count

    s = 0
    while s < L and not w[L - 1 - s]:
        s += 1
    use_G = s > 0
    bound = min(2 * s - 1, v - 1) if use_G else -1
    A: dict[int, bool] = {}

    for _ in range(max_rounds):
        memo: list[dict[int, bool]] = [{} for _ in range(L + 1)]
        memo_count = 0

        def eval_S(start_i: int, start_d: int) -> tuple[bool | None, int | None]:
            nonlocal memo_count
            stack: list[tuple[int, int]] = [(start_i, start_d)]
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
                        t = (d & -d).bit_length() - 1
                        if t <= bound:
                            mi[d] = (t & 1) == 0
                            memo_count += 1
                            stack.pop()
                            continue
                    val_a = A.get(d)
                    if val_a is None:
                        return None, d
                    mi[d] = val_a
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
            return memo[start_i][start_d], None

        unknown_d: int | None = None
        for i in range(1, L + 1):
            val, unk = eval_S(i, h)
            if unk is not None:
                unknown_d = unk
                break
            if val != word_bits[b + i]:
                return False, "gap mismatch", len(A), memo_count + base_count
        if unknown_d is not None:
            A[unknown_d] = eval_T(b, unknown_d)
            continue
        for d, exp_val in list(A.items()):
            val, unk = eval_S(L, d)
            if unk is not None:
                unknown_d = unk
                break
            if val != exp_val:
                return False, "A not preserved", len(A), memo_count + base_count
        if unknown_d is not None:
            A[unknown_d] = eval_T(b, unknown_d)
            continue
        return True, "ok", len(A), memo_count + base_count
    return False, "round limit", len(A), base_count


def prove_one_m(m: int) -> tuple[bool, int, int, int]:
    """1 つの奇数 v の m に対して型を推測し prove3_strict で厳密確定する。
    返り値: (ok, min_p, min_L, facts)
    """
    # 高速パス：まず 40 ブロックで小さい周期を試す
    bits40 = lazy_k8_gaps_bits(m, 40)
    pl = find_period(bits40, 12, 10)
    if pl is not None:
        p, L = pl
        pre = bits40[:p]
        w = bits40[p : p + L]
        ok, _, _, nf = prove3_strict(m, pre, w)
        if ok:
            cpre, cw = canonicalize(pre, w)
            return True, len(cpre), len(cw), nf

    # 一般パス：400 ブロックで探索し c in (1,2,4,8,16,32), k in (1..4) を試す
    bits400 = lazy_k8_gaps_bits(m, 400)
    pl = find_period(bits400, 130, 130)
    if pl is None:
        return False, 0, 0, 0
    p, L = pl
    pre = bits400[:p]
    w = bits400[p : p + L]
    for c in (1, 2, 4, 8, 16, 32):
        pre_c = pre + w * (c - 1)
        for k in (1, 2, 3, 4):
            ok, _, _, nf = prove3_strict(m, pre_c, w * k)
            if ok:
                cpre, cw = canonicalize(pre, w)
                return True, len(cpre), len(cw), nf
    return False, 0, 0, 0


def worker_chunk(args: tuple[int, int]) -> tuple[int, int, int, int, int, int, int, int, int, list[int]]:
    """(m_start, m_end)（m_start < m <= m_end）内の v2(m+1) 奇数すべてを厳密証明する。"""
    m0, m1 = args
    c1 = c3 = c5 = 0
    ok1 = ok3 = ok5 = 0
    max_p = max_L = max_facts = 0
    fails: list[int] = []
    start = m0 + 1 if ((m0 + 1) & 1) == 1 else m0 + 2
    for m in range(start, m1 + 1, 2):
        v = ((m + 1) & -(m + 1)).bit_length() - 1
        if (v & 1) == 0:
            continue
        ok, mp, mL, nf = prove_one_m(m)
        if v == 1:
            c1 += 1
            if ok:
                ok1 += 1
        elif v == 3:
            c3 += 1
            if ok:
                ok3 += 1
        else:
            c5 += 1
            if ok:
                ok5 += 1
        if ok:
            if mp > max_p:
                max_p = mp
            if mL > max_L:
                max_L = mL
            if nf > max_facts:
                max_facts = nf
        else:
            if len(fails) < 20:
                fails.append(m)
    return c1, c3, c5, ok1, ok3, ok5, max_p, max_L, max_facts, fails


def verify_range_parallel(
    m0: int, m1: int, pool: ProcessPoolExecutor, chunks: int = 96
) -> tuple[int, int, int, int, int, int, int, int, int, list[int]]:
    step = max(1000, (m1 - m0 + chunks - 1) // chunks)
    ranges: list[tuple[int, int]] = []
    cur = m0
    while cur < m1:
        nxt = min(m1, cur + step)
        ranges.append((cur, nxt))
        cur = nxt
    c1 = c3 = c5 = ok1 = ok3 = ok5 = max_p = max_L = max_facts = 0
    fails: list[int] = []
    for r in pool.map(worker_chunk, ranges):
        c1 += r[0]
        c3 += r[1]
        c5 += r[2]
        ok1 += r[3]
        ok3 += r[4]
        ok5 += r[5]
        max_p = max(max_p, r[6])
        max_L = max(max_L, r[7])
        max_facts = max(max_facts, r[8])
        fails.extend(r[9])
    return c1, c3, c5, ok1, ok3, ok5, max_p, max_L, max_facts, fails


def verify_pr243_seed(seed: int, count: int = 200) -> tuple[int, int, int, int]:
    """PR #243 の LCG (K=40, COUNT=200, SEED) を完全再現して prove3_strict で厳密検証する。"""
    MASK = (1 << 64) - 1
    st = (seed * 6364136223846793005 + 1442695040888963407) & MASK

    def rnd() -> int:
        nonlocal st
        st = (st * 6364136223846793005 + 1442695040888963407) & MASK
        return st

    n = 0
    ok_cnt = 0
    non_pure0 = 0
    max_f = 0
    while n < count:
        m = (1 << 40) + (rnd() % (1 << 40))
        if (m & 1) == 0:
            continue
        if (v2(m + 1) & 1) == 0:
            continue
        n += 1
        bits = lazy_k8_gaps_bits(m, 400)
        pl = find_period(bits, 133, 100)
        assert pl is not None, f"seed={seed} m={m} no period"
        p, L = pl
        pre = bits[:p]
        w = bits[p : p + L]
        if p > 0 or w[-1]:
            non_pure0 += 1
        proved = False
        for k in (1, 2, 3, 4):
            ok, _, _, nf = prove3_strict(m, pre, w * k)
            if ok:
                proved = True
                max_f = max(max_f, nf)
                break
        assert proved, f"seed={seed} m={m} prove3_strict failed"
        ok_cnt += 1
    return n, ok_cnt, non_pure0, max_f


def main() -> None:
    t0 = time.perf_counter()

    # 1. PR #243: 奇数 5 <= m <= 3000 全 1498 例（200 ブロック K8 照合 + 末尾反転陰性テスト）
    m3000_tested = 0
    m3000_ok = 0
    m3000_mismatch = 0
    m3000_false_pos = 0
    max_f_243 = 0
    for m in range(5, 3001, 2):
        bits = lazy_k8_gaps_bits(m, 200)
        pl = find_period(bits, 60, 80)
        assert pl is not None, f"m={m} no period in 200 blocks"
        m3000_tested += 1
        p, L = pl
        pre = bits[:p]
        w = bits[p : p + L]
        proved_k = 0
        for k in (1, 2, 3, 4):
            ok, _, _, nf = prove3_strict(m, pre, w * k)
            if ok:
                proved_k = k
                max_f_243 = max(max_f_243, nf)
                break
        assert proved_k > 0, f"m={m} prove3_strict failed"
        m3000_ok += 1
        # 200 ブロック一致確認
        for i in range(200):
            exp = pre[i] if i < p else w[(i - p) % L]
            if bits[i] != exp:
                m3000_mismatch += 1
                break
        # 陰性テスト：周期の末尾 1 文字反転
        wf = list(w)
        wf[-1] = not wf[-1]
        if prove3_strict(m, pre, wf * proved_k)[0]:
            m3000_false_pos += 1
    assert m3000_tested == 1498 and m3000_ok == 1498 and m3000_mismatch == 0 and m3000_false_pos == 0

    # 2. PR #243: 2^40 < m < 2^41 無作為 200 例（seed=1, seed=2）＋独立シード 100 例
    s1_n, s1_ok, s1_np, s1_mf = verify_pr243_seed(1, 200)
    s2_n, s2_ok, s2_np, s2_mf = verify_pr243_seed(2, 200)
    rng = random.Random(2026112402)
    ind_n = 0
    ind_ok = 0
    ind_np = 0
    ind_mf = 0
    while ind_n < 100:
        m = rng.randrange((1 << 40) + 1, 1 << 41, 2)
        if (v2(m + 1) & 1) == 0:
            continue
        ind_n += 1
        bits = lazy_k8_gaps_bits(m, 400)
        pl = find_period(bits, 133, 100)
        assert pl is not None
        p, L = pl
        pre = bits[:p]
        w = bits[p : p + L]
        if p > 0 or w[-1]:
            ind_np += 1
        proved = False
        for c in (1, 2, 4):
            for k in (1, 2, 3, 4):
                ok, _, _, nf = prove3_strict(m, pre + w * (c - 1), w * k)
                if ok:
                    proved = True
                    ind_mf = max(ind_mf, nf)
                    break
            if proved:
                break
        assert proved, f"independent random m={m} failed"
        ind_ok += 1
    max_f_243 = max(max_f_243, s1_mf, s2_mf, ind_mf)
    t_243 = time.perf_counter() - t0
    print(f"[stage 1] PR #243 verified in {t_243:.2f}s (max_facts={max_f_243})", flush=True)

    # 3. PR #245 & PR #249: 5 <= m <= 2^22 の v2(m+1) 奇数全 1,398,100 例を並列厳密検証
    workers = max(1, min(10, (os.cpu_count() or 4)))
    with ProcessPoolExecutor(max_workers=workers) as pool:
        t1 = time.perf_counter()
        r_small = verify_range_parallel(4, 200000, pool, chunks=64)
        print(
            f"[stage 2a] 4 < m <= 200000 done in {time.perf_counter() - t1:.2f}s: "
            f"v1={r_small[3]}/{r_small[0]}, v3={r_small[4]}/{r_small[1]}, v>=5={r_small[5]}/{r_small[2]}, "
            f"maxP={r_small[6]}, maxL={r_small[7]}, maxFacts={r_small[8]}, fails={len(r_small[9])}",
            flush=True,
        )
        assert r_small[0] == r_small[3] == 49999
        assert r_small[1] == r_small[4] == 12500
        assert r_small[2] == r_small[5] == 4166
        assert len(r_small[9]) == 0

        t2 = time.perf_counter()
        r_20 = verify_range_parallel(200000, 1 << 20, pool, chunks=128)
        print(
            f"[stage 2b] 200000 < m <= 2^20 done in {time.perf_counter() - t2:.2f}s: "
            f"v1={r_20[3]}/{r_20[0]}, v3={r_20[4]}/{r_20[1]}, v>=5={r_20[5]}/{r_20[2]}, "
            f"maxP={r_20[6]}, maxL={r_20[7]}, maxFacts={r_20[8]}, fails={len(r_20[9])}",
            flush=True,
        )
        assert r_20[0] == r_20[3] == 212144
        assert r_20[1] == r_20[4] == 53036
        assert r_20[2] == r_20[5] == 17679
        assert len(r_20[9]) == 0

        t3 = time.perf_counter()
        r_22 = verify_range_parallel(1 << 20, 1 << 22, pool, chunks=256)
        print(
            f"[stage 3] 2^20 < m <= 2^22 done in {time.perf_counter() - t3:.2f}s: "
            f"v1={r_22[3]}/{r_22[0]}, v3={r_22[4]}/{r_22[1]}, v>=5={r_22[5]}/{r_22[2]}, "
            f"maxP={r_22[6]}, maxL={r_22[7]}, maxFacts={r_22[8]}, fails={len(r_22[9])}",
            flush=True,
        )
        assert r_22[0] == r_22[3] == 786432
        assert r_22[1] == r_22[4] == 196608
        assert r_22[2] == r_22[5] == 65536
        assert len(r_22[9]) == 0

    total_max_facts = max(max_f_243, r_small[8], r_20[8], r_22[8])
    elapsed = time.perf_counter() - t0
    lines = [
        "gemini-2 independent exhaustive verification of PR #243 (prove3), PR #245 (5 <= m <= 2^20), PR #249 (2^20 < m <= 2^22)",
        f"PR #243 odd 5 <= m <= 3000: tested={m3000_tested}/1498, proved={m3000_ok}/1498, mismatches={m3000_mismatch}, flipped_last_false_pos={m3000_false_pos}/1498",
        f"PR #243 2^40 < m < 2^41 random: seed1={s1_ok}/{s1_n} (non_pure0={s1_np}), seed2={s2_ok}/{s2_n} (non_pure0={s2_np}), independent_seed={ind_ok}/{ind_n} (non_pure0={ind_np}), errors=0",
        f"PR #245 4 < m <= 200000: v1={r_small[3]}/{r_small[0]}, v3={r_small[4]}/{r_small[1]}, v>=5={r_small[5]}/{r_small[2]}, total={r_small[3]+r_small[4]+r_small[5]}/66665, maxP={r_small[6]}, maxL={r_small[7]}, maxFacts={r_small[8]}, fails=0",
        f"PR #245 200000 < m <= 2^20: v1={r_20[3]}/{r_20[0]}, v3={r_20[4]}/{r_20[1]}, v>=5={r_20[5]}/{r_20[2]}, total={r_20[3]+r_20[4]+r_20[5]}/282859, maxP={r_20[6]}, maxL={r_20[7]}, maxFacts={r_20[8]}, fails=0",
        f"PR #249 2^20 < m <= 2^22: v1={r_22[3]}/{r_22[0]}, v3={r_22[4]}/{r_22[1]}, v>=5={r_22[5]}/{r_22[2]}, total={r_22[3]+r_22[4]+r_22[5]}/1048576, maxP={r_22[6]}, maxL={r_22[7]}, maxFacts={r_22[8]}, fails=0",
        f"Grand total odd-v proved (5 <= m <= 2^22): {66665 + 282859 + 1048576}/1398100, overall maxFacts={total_max_facts} (well below 3,000,000), elapsed={elapsed:.2f}s",
    ]
    out_text = "\n".join(lines) + "\n"
    Path("data/gemini2_verify_prove3_coverage.txt").write_text(out_text, encoding="utf-8")
    print(out_text, end="", flush=True)


if __name__ == "__main__":
    main()
