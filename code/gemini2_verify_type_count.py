"""
PR #252（m <= 2^22 の確定型種類数 7,406 種類）および PR #255（2^21 < m <= 2^22 の 30 例照合）の
独立全数検証スクリプト。

査読済み定理 K8・K3・K4・補題 Q_n のみから書いた厳密独立検証器 prove3_strict（上限超過即例外・
m 奇数必須）により、2 <= m <= 2^22 の全数（v2(m+1) 奇数 1,398,100 例＋偶数 K4）を確定し、
k = 4..22 ごとの確定型種類数（canon 基準および非巡回厳密列基準）を独立再計算する。

実行方法:
    python code/gemini2_verify_type_count.py
出力:
    data/gemini2_verify_type_count.txt
"""

from __future__ import annotations

import os
import time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path


EXPECTED_PR252 = {
    4: 4,
    5: 5,
    6: 8,
    7: 12,
    8: 17,
    9: 24,
    10: 39,
    11: 59,
    12: 89,
    13: 137,
    14: 209,
    15: 330,
    16: 492,
    17: 758,
    18: 1182,
    19: 1850,
    20: 2945,
    21: 4707,
    22: 7406,
}

PR255_SAMPLES = [
    (4012887, 0, 3),
    (3381641, 0, 4),
    (3891861, 0, 2),
    (2854193, 0, 3),
    (2208525, 0, 2),
    (4137273, 0, 2),
    (3044767, 0, 3),
    (3246055, 0, 3),
    (3366005, 0, 2),
    (3091429, 0, 2),
    (2336281, 0, 2),
    (2274449, 0, 3),
    (4039845, 0, 2),
    (3409081, 0, 2),
    (4186661, 0, 2),
    (3113349, 0, 2),
    (2470751, 0, 12),
    (2471629, 0, 2),
    (2101441, 0, 4),
    (3235965, 0, 2),
    (3653013, 0, 2),
    (2875913, 0, 4),
    (4088785, 0, 3),
    (3596345, 0, 2),
    (3829373, 0, 2),
    (3690999, 0, 3),
    (2528167, 0, 3),
    (3195801, 0, 2),
    (2803469, 0, 2),
    (3324007, 0, 2),
]


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


def canonicalize(pre: list[bool], w: list[bool]) -> tuple[str, str]:
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
    pre_s = "".join("1" if b else "0" for b in pre[:p])
    w_s = "".join("1" if b else "0" for b in w_cur)
    return pre_s, w_s


def canon_pr252(pre_s: str, w_s: str) -> str:
    """PR #252 / type_count_certified.js と同じ正規化キー（前周期 | 周期の辞書順最小巡回）。"""
    best = w_s
    for i in range(1, len(w_s)):
        rot = w_s[i:] + w_s[:i]
        if rot < best:
            best = rot
    return (pre_s if pre_s else "-") + "|" + best


def prove3_strict(
    m: int,
    pre: list[bool],
    w: list[bool],
    max_rounds: int = 20000,
    max_facts: int = 3_000_000,
) -> tuple[bool, int]:
    if m < 3 or (m & 1) == 0:
        return False, 0
    p = len(pre)
    L = len(w)
    b = p + L
    h = (m + 1) >> 1
    M = m + 2
    E_gap = m + 1
    v = (m + 1 & -(m + 1)).bit_length() - 1

    word_bits: list[bool] = [False] * (b + L + 1)
    for i in range(p):
        word_bits[i] = pre[i]
    for i in range(p, b + L + 1):
        word_bits[i] = w[(i - p) % L]

    g0 = (((h & -h).bit_length() - 1) & 1) == 0
    if g0 != word_bits[0]:
        return False, 0

    gaps_abs = [M if bit else E_gap for bit in word_bits]
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
                return False, memo_count + base_count
        if unknown_d is not None:
            A[unknown_d] = eval_T(b, unknown_d)
            continue
        for d, exp_val in list(A.items()):
            val, unk = eval_S(L, d)
            if unk is not None:
                unknown_d = unk
                break
            if val != exp_val:
                return False, memo_count + base_count
        if unknown_d is not None:
            A[unknown_d] = eval_T(b, unknown_d)
            continue
        return True, memo_count + base_count
    return False, base_count


def prove_one_m_type(m: int) -> tuple[bool, str, str, int]:
    bits40 = lazy_k8_gaps_bits(m, 40)
    pl = find_period(bits40, 12, 10)
    if pl is not None:
        p, L = pl
        pre = bits40[:p]
        w = bits40[p : p + L]
        ok, nf = prove3_strict(m, pre, w)
        if ok:
            pre_s, w_s = canonicalize(pre, w)
            return True, pre_s, w_s, nf

    bits400 = lazy_k8_gaps_bits(m, 400)
    pl = find_period(bits400, 130, 130)
    if pl is None:
        return False, "", "", 0
    p, L = pl
    pre = bits400[:p]
    w = bits400[p : p + L]
    for c in (1, 2, 4, 8, 16, 32):
        pre_c = pre + w * (c - 1)
        for k in (1, 2, 3, 4):
            ok, nf = prove3_strict(m, pre_c, w * k)
            if ok:
                pre_s, w_s = canonicalize(pre, w)
                return True, pre_s, w_s, nf
    return False, "", "", 0


def worker_chunk_types(args: tuple[int, int]) -> tuple[set[str], set[tuple[str, str]], int, int]:
    """(m0, m1] の v2(m+1) 奇数 m すべてを厳密証明し、canon 集合と厳密 (pre, w) 集合を返す。"""
    m0, m1 = args
    canon_set: set[str] = set()
    exact_set: set[tuple[str, str]] = set()
    fails = 0
    max_facts = 0
    start = m0 + 1 if ((m0 + 1) & 1) == 1 else m0 + 2
    for m in range(start, m1 + 1, 2):
        if m < 5:
            continue
        v = ((m + 1) & -(m + 1)).bit_length() - 1
        if (v & 1) == 0:
            continue
        ok, pre_s, w_s, nf = prove_one_m_type(m)
        if not ok:
            fails += 1
        else:
            if nf > max_facts:
                max_facts = nf
            canon_set.add(canon_pr252(pre_s, w_s))
            exact_set.add((pre_s, w_s))
    return canon_set, exact_set, fails, max_facts


def main() -> None:
    t0 = time.perf_counter()

    # 1. PR #255 の 30 例を独立厳密検証
    pr255_ok = 0
    for m, exp_p, exp_L in PR255_SAMPLES:
        ok, pre_s, w_s, _ = prove_one_m_type(m)
        assert ok and len(pre_s) == exp_p and len(w_s) == exp_L, (
            f"PR #255 mismatch m={m}: got ({len(pre_s)}, {len(w_s)}), want ({exp_p}, {exp_L})"
        )
        pr255_ok += 1
    print(f"[stage 1] PR #255 30/30 exact match in {time.perf_counter() - t0:.2f}s", flush=True)

    # 2. PR #252: 2 <= m <= 2^22 の全数型確定と k = 4..22 ごとの種類数集計
    workers = max(1, min(10, (os.cpu_count() or 4)))
    canon_all: set[str] = {"-|0"}  # v2(m+1) 偶数（K4）
    exact_all: set[tuple[str, str]] = {("", "0")}
    total_fails = 0
    overall_max_facts = 0

    rows: list[str] = []
    with ProcessPoolExecutor(max_workers=workers) as pool:
        prev_hi = 4
        for k in range(4, 23):
            hi = 1 << k
            span = hi - prev_hi
            n_chunks = 1 if span <= 4096 else min(128, max(workers * 4, span // 16384))
            step = max(1, (span + n_chunks - 1) // n_chunks)
            chunks = [(cur, min(hi, cur + step)) for cur in range(prev_hi, hi, step)]
            for c_set, e_set, fails, mf in pool.map(worker_chunk_types, chunks):
                canon_all.update(c_set)
                exact_all.update(e_set)
                total_fails += fails
                if mf > overall_max_facts:
                    overall_max_facts = mf
            assert total_fails == 0, f"k={k}: fails={total_fails}"
            assert len(canon_all) == EXPECTED_PR252[k], (
                f"k={k}: got canon={len(canon_all)}, expected={EXPECTED_PR252[k]}"
            )
            rows.append(
                f"k={k:2d} | canon={len(canon_all):4d} (PR#252={EXPECTED_PR252[k]:4d}, match) | exact_seq={len(exact_all):4d} (diff={len(exact_all)-len(canon_all)})"
            )
            if k >= 18:
                print(f"[progress] {rows[-1]} ({time.perf_counter() - t0:.1f}s)", flush=True)
            prev_hi = hi

    elapsed = time.perf_counter() - t0
    lines = [
        "gemini-2 independent exhaustive verification of PR #252 (certified type count m <= 2^22) and PR #255 (30 cross-check samples)",
        f"PR #255 30 samples (2^21 < m <= 2^22): {pr255_ok}/30 exact (p, L) match, errors=0",
        f"PR #252 exhaustive 2 <= m <= 2^22: unproved=0, maxFacts={overall_max_facts} (well below 3,000,000), elapsed={elapsed:.2f}s",
        *rows,
    ]
    out_text = "\n".join(lines) + "\n"
    Path("data/gemini2_verify_type_count.txt").write_text(out_text, encoding="utf-8")
    print(out_text, end="", flush=True)


if __name__ == "__main__":
    main()
