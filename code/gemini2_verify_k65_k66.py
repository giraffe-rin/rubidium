#!/usr/bin/env python3
"""
gemini2_verify_k65_k66.py — Independent Python 3 verification for PR #451 (Conjecture K65)
and PR #453 (Lean 4 Theorem K66 + 93.82% Lean coverage).

What this script independently verifies (zero reliance on K8 or recurrence R):
1. Cross-checks our O(N) exact PROBLEM.md minimax DP against naive O(N*m^2) DP on m = 9, 13, 17, 25.
2. PR #451 (Conjecture K65 & data/k65_obs.txt):
   - Enumerates all qualifying m <= 60000: v2(m+1) = 1, v2(3h+1) = 2k >= 4,
     X_0 = (m+2+w)/2, v2(X_t) = 1 for t < j, X_j odd, j >= 1.
   - Runs exact O(N) direct PROBLEM.md DP until an exact m-row state cycle
     (typ[a_b - m + 1 .. a_b] repeats), giving a direct PROBLEM.md periodicity certificate
     for every qualifying m <= 60000 without using K8 or block_rule.js.
   - Verifies Conjecture K65 (a)/(b)/(c) (59, 29, 29 cases) and every count/word in data/k65_obs.txt.
   - Checks the minor key-lookup bug in code/k65_obs.js line 25 (`other[word]`).
3. PR #453 (Theorem K66 & data/lean_coverage.txt):
   - Checks hypothesis equivalence ((m+1) % 128 == 88 <=> m+1 = 8u, u == 11 mod 16)
     and disjointness from K10a and K13 over 1 <= m <= 1,000,000.
   - Runs exact O(N) direct PROBLEM.md DP with state-cycle periodicity certificate for all
     94 cases of K66 with u <= 1500 (m = 87 .. 11991), confirming exact 110-type for all n >= 0.
   - Independently recomputes the 1 <= m <= 1,000,000 Lean coverage table for all 11 Lean theorems
     and exact rational asymptotic natural density (5404/5760 = 1351/1440 = 93.819444...%).

Usage (from repository root):
    uv run python code/gemini2_verify_k65_k66.py > data/gemini2_verify_k65_k66.txt
"""
from __future__ import annotations

import hashlib
import subprocess
import sys
from array import array
from collections import defaultdict
from fractions import Fraction


def v2(x: int) -> int:
    return (x & -x).bit_length() - 1


def naive_problem_dp(m: int, n_max: int) -> list[list[bool]]:
    """Direct O(N * m^2) PROBLEM.md minimax DP: is_p[n][prev] for 0 <= n <= n_max, 0 <= prev <= m."""
    is_p = [[False] * (m + 1) for _ in range(n_max + 1)]
    for prev in range(m + 1):
        is_p[0][prev] = True
    for n in range(1, n_max + 1):
        lim = m if m < n else n
        p_moves = []
        for k in range(1, lim + 1):
            if is_p[n - k][k]:
                p_moves.append(k)
                if len(p_moves) >= 2:
                    break
        if len(p_moves) == 0:
            row = is_p[n]
            for prev in range(m + 1):
                row[prev] = True
        elif len(p_moves) == 1:
            is_p[n][p_moves[0]] = True
    return is_p


def direct_dp_period(m: int, max_blocks: int = 200) -> tuple[int, str, list[int], int]:
    """
    Exact O(N) PROBLEM.md minimax DP (zero K8/R assumptions).

    For each row r >= 0, typ[r] encodes the exact P-set of row r:
      -1  : ALL-P row ((r, p) is P for all p in 0..m)
      k>0 : SINGLE-P row ((r, p) is P iff p == k)
      0   : NONE-P row ((r, p) is N for all p)

    Since row r depends only on rows r-m .. r-1, if two ALL-P rows a_i and a_j (with a_i >= m)
    have identical m-row tails typ[a_i - m + 1 .. a_i] == typ[a_j - m + 1 .. a_j], then by
    induction the entire exact PROBLEM.md DP table is periodic from a_i onward with block period j - i.

    Returns:
      (min_preperiod, min_period_word, all_gaps, state_cycle_end_block)
    """
    # Use a bytearray-backed chunked / growable array('i') of row types,
    # and a sparse trigger list: when typ[s] == k > 0, row s+k receives a P-move k.
    # Because s < s+k <= s+m, a circular buffer of size (m + 2) holds the exact
    # number of SINGLE-P incoming triggers for future rows r in [cur, cur + m].
    # Any two ALL-P rows are separated by at least m+1, so at most ONE ALL-P row
    # lies in [r - m, r - 1] (namely `last_all` if r - last_all <= m).
    buf_len = m + 2
    trig_cnt = [0] * buf_len
    trig_val = [0] * buf_len

    # Store only the last m+3 row types in a rolling window? No, we need the m-row tail
    # at ALL-P rows; keeping a ring buffer of length m for the last m row types uses O(m) memory!
    # Wait: even simpler, keep `tail = array('i', [0] * m)`? Actually each block has ~m+2 rows,
    # and we only need exact bytes of the last m entries at each ALL-P row.
    # A rolling array `hist` of size m_pow or just copying a slice from a flat `typ` array
    # per block (only ~10-40 blocks!) is tiny and fast. Let's use `typ = array('i')`.
    typ = array('i')
    typ_append = typ.append

    # Row 0: ALL-P
    typ_append(-1)
    last_all = 0
    all_p_rows = [0]
    gaps: list[int] = []
    # Map (blake2b_digest) -> list of (block_idx, row_a)
    seen: dict[bytes, list[tuple[int, int]]] = {}

    r = 1
    while len(gaps) < max_blocks:
        idx = r % buf_len
        cnt = trig_cnt[idx]
        val = trig_val[idx]
        if cnt:
            trig_cnt[idx] = 0
            trig_val[idx] = 0

        d_all = r - last_all
        if d_all <= m:
            if cnt == 0:
                t = d_all
            else:
                t = 0
        else:
            if cnt == 0:
                t = -1
            elif cnt == 1:
                t = val
            else:
                t = 0

        typ_append(t)
        if t > 0:
            nxt = (r + t) % buf_len
            c = trig_cnt[nxt]
            if c == 0:
                trig_cnt[nxt] = 1
                trig_val[nxt] = t
            else:
                trig_cnt[nxt] = 2
        elif t == -1:
            gap = r - last_all
            if gap != m + 1 and gap != m + 2:
                raise RuntimeError(f"Unexpected ALL-P gap {gap} for m={m} at r={r}")
            gaps.append(gap)
            last_all = r
            all_p_rows.append(r)
            if r >= m:
                tail_bytes = typ[r - m + 1 : r + 1].tobytes()
                h = hashlib.blake2b(tail_bytes, digest_size=16).digest()
                b_idx = len(gaps)  # index of ALL-P row a_{b_idx} = r
                bucket = seen.get(h)
                if bucket is not None:
                    for prev_b, prev_r in bucket:
                        if typ[prev_r - m + 1 : prev_r + 1] == typ[r - m + 1 : r + 1]:
                            # Exact state repeat proved: blocks from prev_b onward repeat with period (b_idx - prev_b)
                            seq = "".join("1" if g == m + 2 else "0" for g in gaps)
                            cyc_start = prev_b
                            cyc_len = b_idx - prev_b
                            # Minimize preperiod t and period p of the infinite ultimately periodic sequence
                            # seq[0:cyc_start] + (seq[cyc_start:cyc_start+cyc_len])^inf
                            cyc = seq[cyc_start : cyc_start + cyc_len]
                            # Find minimal period p dividing cyc_len
                            min_p = cyc_len
                            for p in range(1, cyc_len + 1):
                                if cyc_len % p == 0 and cyc[:p] * (cyc_len // p) == cyc:
                                    min_p = p
                                    break
                            # Pull back preperiod as far as possible
                            t_min = cyc_start
                            while t_min > 0 and seq[t_min - 1] == seq[t_min - 1 + min_p]:
                                t_min -= 1
                            word = seq[t_min : t_min + min_p]
                            return t_min, word, gaps, b_idx
                    bucket.append((b_idx, r))
                else:
                    seen[h] = [(b_idx, r)]
        r += 1

    raise RuntimeError(f"State cycle not found within {max_blocks} blocks for m={m}")


def check_dp_consistency() -> None:
    print("=== 1. O(N) Direct PROBLEM.md DP vs Naive O(N*m^2) DP Cross-Check ===")
    total_pos = 0
    for m in (9, 13, 17, 25):
        n_max = 10 * (m + 2)
        naive = naive_problem_dp(m, n_max)
        # Re-run the same O(N) transition and compare EVERY (n, prev)
        buf_len = m + 2
        trig_cnt = [0] * buf_len
        trig_val = [0] * buf_len
        last_all = 0
        for n in range(0, n_max + 1):
            if n == 0:
                t = -1
            else:
                idx = n % buf_len
                cnt = trig_cnt[idx]
                val = trig_val[idx]
                trig_cnt[idx] = 0
                trig_val[idx] = 0
                d_all = n - last_all
                if d_all <= m:
                    t = d_all if cnt == 0 else 0
                else:
                    t = -1 if cnt == 0 else (val if cnt == 1 else 0)
                if t > 0:
                    nxt = (n + t) % buf_len
                    if trig_cnt[nxt] == 0:
                        trig_cnt[nxt] = 1
                        trig_val[nxt] = t
                    else:
                        trig_cnt[nxt] = 2
                elif t == -1:
                    last_all = n
            for prev in range(m + 1):
                pred = (t == -1) or (t > 0 and prev == t)
                if pred != naive[n][prev]:
                    raise AssertionError(f"Mismatch at m={m}, n={n}, prev={prev}")
                total_pos += 1
        print(f"  m={m}: 0..{n_max} ({(n_max + 1) * (m + 1)} positions) -> EXACT MATCH")
    print(f"  Total positions cross-checked: {total_pos}, mismatches: 0\n")


def verify_pr451_k65(m_max: int = 60000) -> None:
    print(f"=== 2. PR #451 (Conjecture K65 & data/k65_obs.txt) Direct PROBLEM.md DP Verification (m <= {m_max}) ===")
    tab: dict[str, dict[str, int]] = defaultdict(lambda: defaultdict(int))
    other_fixed: dict[str, int] = defaultdict(int)
    other_js_bug: dict[str, int] = {}
    other_cases: list[tuple[int, int, int, int, int, str]] = []

    conj_a_total = conj_a_ok = 0
    conj_b_total = conj_b_ok = 0
    conj_c_total = conj_c_ok = 0
    total_m = 0
    max_cycle_blocks = 0

    for m in range(9, m_max + 1, 4):
        h = (m + 1) // 2
        t2 = v2(3 * h + 1)
        if t2 < 4 or t2 % 2 != 0:
            continue
        k = t2 // 2
        w = (3 * h + 1) >> t2
        X = (m + 2 + w) // 2
        j = 0
        while v2(X) == 1:
            X = (m + 2 + X // 2) // 2
            j += 1
        if v2(X) != 0 or j == 0:
            continue

        total_m += 1
        t_min, word, _gaps, b_end = direct_dp_period(m, max_blocks=200)
        if b_end > max_cycle_blocks:
            max_cycle_blocks = b_end

        pre = "1" * (j + 1)
        rest = word[j + 1 :]
        ok = (
            t_min == 0
            and word.startswith(pre)
            and len(rest) >= 2
            and len(rest) % 2 == 0
            and rest == "10" * (len(rest) // 2)
        )
        key = f"k={k} j={j} X_j mod 8={X % 8}"
        label = f"r={len(rest) // 2}" if ok else "ほかの型"
        tab[key][label] += 1
        if not ok:
            okey = word + ("（前周期あり）" if t_min > 0 else "")
            other_fixed[okey] += 1
            other_js_bug[okey] = other_js_bug.get(word, 0) + 1
            other_cases.append((m, k, j, X % 8, t_min, word))

        # Check Conjecture K65 (a), (b), (c)
        if k == 2 and j == 1 and (X % 8) in (1, 5):
            conj_a_total += 1
            if t_min == 0 and word == "1110":
                conj_a_ok += 1
            else:
                raise AssertionError(f"K65(a) counterexample at m={m}: t={t_min}, word={word}")
        elif k == 2 and j == 1 and (X % 8) == 3:
            conj_b_total += 1
            if t_min == 0 and word == "111010":
                conj_b_ok += 1
            else:
                raise AssertionError(f"K65(b) counterexample at m={m}: t={t_min}, word={word}")
        elif k == 2 and j == 2:
            conj_c_total += 1
            if t_min == 0 and word == "11110":
                conj_c_ok += 1
            else:
                raise AssertionError(f"K65(c) counterexample at m={m}: t={t_min}, word={word}")

    print(f"  Total qualifying m <= {m_max} verified by direct PROBLEM.md DP state-cycle: {total_m}")
    print(f"  Max blocks to exact m-row DP state repeat: {max_cycle_blocks}")
    print(f"  Conjecture K65 (a) [k=2, j=1, X_1 mod 8 in {{1,5}} -> 1110,   t=0]: {conj_a_ok}/{conj_a_total} EXACT MATCH")
    print(f"  Conjecture K65 (b) [k=2, j=1, X_1 mod 8 == 3      -> 111010, t=0]: {conj_b_ok}/{conj_b_total} EXACT MATCH")
    print(f"  Conjecture K65 (c) [k=2, j=2                      -> 11110,  t=0]: {conj_c_ok}/{conj_c_total} EXACT MATCH")

    # Compare directly against PR #451's data/k65_obs.txt
    pr_txt = subprocess.check_output(
        ["git", "show", "origin/claude-1/k65-obs:data/k65_obs.txt"], text=True, encoding="utf-8"
    )
    pr_rows: dict[str, dict[str, int]] = {}
    pr_other: dict[str, int] = {}
    for line in pr_txt.splitlines():
        if line.startswith("k="):
            lhs, rhs = line.split(" | ")
            d = {}
            for part in rhs.split("、"):
                rk, rv = part.split(": ")
                d[rk] = int(rv)
            pr_rows[lhs] = d
        elif line.startswith("1^{j+1}(10)^r の形でない型："):
            body = line.split("：", 1)[1]
            for part in body.split("、"):
                w_str, cnt_str = part.rsplit(" ", 1)
                pr_other[w_str] = int(cnt_str)

    tab_plain = {k: dict(v) for k, v in tab.items()}
    assert tab_plain == pr_rows, f"Table mismatch!\nDP: {tab_plain}\nPR: {pr_rows}"
    assert other_js_bug == pr_other, f"Bug-reproduction mismatch!\nBugSim: {other_js_bug}\nPR: {pr_other}"
    total_other_in_tab = sum(v.get("ほかの型", 0) for v in tab_plain.values())
    total_other_fixed = sum(other_fixed.values())
    total_other_pr = sum(pr_other.values())
    assert total_other_in_tab == total_other_fixed == len(other_cases) == 12
    print(f"  Comparison against PR #451 data/k65_obs.txt (main table): ALL {len(pr_rows)} (k,j,X_j mod 8) rows MATCH 100%")
    print(f"  BUG DETECTED in PR #451 code/k65_obs.js line 25 & data/k65_obs.txt footer:")
    print(f"    Main table 'ほかの型' sum = {total_other_in_tab}, true footer sum = {total_other_fixed}, PR #451 footer sum = {total_other_pr}")
    print(f"    True count of '1011（前周期あり）' = {other_fixed['1011（前周期あり）']}, PR #451 reported = {pr_other['1011（前周期あり）']}")
    print(f"    Cause: code/k65_obs.js line 25 reads `other[word]` instead of `other[word + (t > 0 ? '（前周期あり）' : '')]`.")
    print(f"    Simulating that exact bug reproduces PR #451 footer 100%: {other_js_bug == pr_other}")
    print(f"  All {len(other_cases)} non-standard cases (m, k, j, X_j mod 8, preperiod t, period word):")
    for m, k, j, x8, t_min, word in other_cases:
        print(f"    m={m} (k={k}, j={j}, X_j mod 8={x8}): t={t_min}, word={word}")
    print()


def verify_pr453_k66_and_coverage() -> None:
    print("=== 3. PR #453 (Theorem K66 & 93.82% Lean Coverage) Independent Verification ===")
    # 3a. Hypothesis equivalence & disjointness over 1 <= m <= 1,000,000
    m_max = 1_000_000
    k66_count = 0
    first_k66 = None
    overlap_k10a = 0
    overlap_k13 = 0
    for m in range(1, m_max + 1):
        c_lean = (m + 1) % 128 == 88
        c_math = (m + 1) % 8 == 0 and ((m + 1) // 8) % 16 == 11
        assert c_lean == c_math, f"Hyp mismatch at m={m}"
        if c_lean:
            k66_count += 1
            if first_k66 is None:
                first_k66 = m
            if m % 64 == 7 and m >= 71:
                overlap_k10a += 1
            u = (m + 1) // 8
            a, b = v2(9 * u + 1), v2(11 * u + 1)
            if (a == 1 and b == 3) or (a == 3 and b == 1):
                overlap_k13 += 1
    assert k66_count == 7812 and first_k66 == 87 and overlap_k10a == 0 and overlap_k13 == 0
    print(f"  Hypothesis equivalence (1 <= m <= {m_max}): 100% match, count={k66_count}, min m={first_k66} (u=11)")
    print(f"  Disjointness on v2(m+1)=3: overlap(K66, K10a)={overlap_k10a}, overlap(K66, K13)={overlap_k13}")

    # 3b. Direct PROBLEM.md O(N) DP verification for all u <= 1500 (94 cases)
    us = list(range(11, 1501, 16))
    for u in us:
        m = 8 * u - 1
        assert (m + 1) % 128 == 88
        t_min, word, gaps, _b_end = direct_dp_period(m, max_blocks=40)
        if t_min != 0 or word != "110":
            raise AssertionError(f"K66 DP failure at u={u}, m={m}: t={t_min}, word={word}")
        # Also verify exact residue set {0, m+2, 2m+4} mod (3m+5) from the gaps
        pos = 0
        period = 3 * m + 5
        for g in gaps:
            assert (pos % period) in (0, m + 2, 2 * m + 4)
            pos += g
    print(f"  Direct PROBLEM.md DP state-cycle verification for K66: {len(us)}/{len(us)} cases (u=11..{us[-1]}, m=87..{8*us[-1]-1}) -> ALL EXACT 110 (t=0)")

    # 3c. Independent recomputation of 1 <= m <= 1,000,000 coverage table
    stat: dict[str, list[int]] = {}
    by_thm: dict[str, int] = defaultdict(int)
    for m in range(1, m_max + 1):
        v = v2(m + 1)
        u = (m + 1) >> v
        h = (m + 1) >> 1
        covered = False
        if v % 2 == 0:
            by_thm["K4"] += 1
            covered = True
        if v == 1 and m >= 5:
            t = v2(3 * h + 1)
            if t % 2 == 1:
                by_thm["K9"] += 1
                covered = True
            if t == 2 and ((11 * h + 5) // 8) % 2 == 1:
                by_thm["K12a"] += 1
                covered = True
            if t == 2 and m >= 9:
                w = (3 * h + 1) // 4
                X = (m + 2 + w) // 2
                j = 0
                while X % 4 == 2:
                    X = (m + 2 + X // 2) // 2
                    j += 1
                if j >= 1 and X % 2 == 1:
                    by_thm["K64"] += 1
                    covered = True
            if t >= 4 and t % 2 == 0 and ((3 * h + 1) >> t) % 4 == 3:
                by_thm["K15"] += 1
                covered = True
        if m % 64 == 7 and m >= 71:
            by_thm["K10a"] += 1
            covered = True
        if m % 8 == 7:
            U = (m + 1) >> 3
            a, b = v2(9 * U + 1), v2(11 * U + 1)
            if (a == 1 and b == 3) or (a == 3 and b == 1):
                by_thm["K13"] += 1
                covered = True
        if (m + 1) % 128 == 88:
            by_thm["K66"] += 1
            covered = True
        if m % 128 == 31:
            by_thm["K29_v5"] += 1
            covered = True
        if v >= 5 and v % 2 == 1 and u % 4 == 1:
            by_thm["K29_gen"] += 1
            covered = True
        if v >= 5 and v % 2 == 1 and u % 4 == 3:
            w = v2(u + 1)
            if (w % 2 == 1 and 3 <= w <= v - 2) or w >= v + 1:
                by_thm["K38"] += 1
                covered = True

        key = "偶数" if v % 2 == 0 else str(v)
        if key not in stat:
            stat[key] = [0, 0]
        stat[key][0] += 1
        if covered:
            stat[key][1] += 1

    lines = [
        f"# Lean で型が決まる m の割合（1 ≤ m ≤ {m_max}）",
        f"# 生成: node code/lean_coverage.js {m_max}",
        "v2(m+1) | m の数 | Lean で型が決まる数 | 割合",
    ]
    tot = cov = 0
    keys = ["偶数"] + sorted((k for k in stat if k != "偶数"), key=int)
    for k in keys:
        n, c = stat[k]
        tot += n
        cov += c
        lines.append(f"{k} | {n} | {c} | {100.0 * c / n:.2f}%")
    lines.append(f"合計 | {tot} | {cov} | {100.0 * cov / tot:.2f}%")

    pr_cov = subprocess.check_output(
        ["git", "show", "origin/claude-1/lean-k66:data/lean_coverage.txt"], text=True, encoding="utf-8"
    ).strip().splitlines()
    assert lines == pr_cov[:-2], f"Coverage table mismatch!\nMine:\n{lines}\nPR:\n{pr_cov[:-2]}"

    # Check per-theorem counts line
    thm_line = pr_cov[-1].split("：", 1)[1]
    pr_by_thm = {}
    for item in thm_line.split("、"):
        tk, tv = item.split(" ")
        pr_by_thm[tk] = int(tv)
    assert dict(by_thm) == pr_by_thm, f"Per-theorem mismatch!\nMine: {dict(by_thm)}\nPR: {pr_by_thm}"
    print(f"  Lean coverage table (1 <= m <= {m_max}): {cov}/{tot} = {100.0 * cov / tot:.2f}% -> LINE-FOR-LINE MATCH with PR #453")
    print(f"  v2(m+1)=3 coverage: {stat['3'][1]}/{stat['3'][0]} = {100.0 * stat['3'][1] / stat['3'][0]:.2f}% (K66 added {by_thm['K66']} disjoint cases)")

    # Exact asymptotic natural density:
    # - v2 even (K4): 2/3
    # - v2 = 1 (weight 1/4):
    #     K9 (t odd): 2/3 of v2=1
    #     K12a (t=2, Q odd): 1/8 of v2=1
    #     K64 (t=2, X chain): 1/24 of v2=1 (geometric sum (1/2) * sum_{j>=1} (1/4)^j * ... = 1/24, total t=2 is 1/6 = 1/4 * 2/3)
    #     K15 (t=2k>=4, Q odd): (1/2) * sum_{k>=2} 1/4^k = 1/24 of v2=1
    #     Total v2=1 = 2/3 + 1/8 + 1/24 + 1/24 = 7/8 of 1/4 = 7/32
    # - v2 = 3 (weight 1/16):
    #     K10a (1/4) + K13 (1/4) + K66 (1/8) = 5/8 of 1/16 = 5/128
    # - v2 = 2s+1 >= 5 (weight 1/4^(s+1)):
    #     K29_gen (u==1 mod 4): 1/2
    #     K38 (u==3 mod 4, w odd in [3, v-2] or w >= v+1):
    #       P(w odd in [3, 2s-1] | u==3 mod 4) = sum_{r=1}^{s-1} 1/2^(2r) = (1 - 1/4^(s-1))/3
    #       P(w >= 2s+2 | u==3 mod 4) = 1/2^(2s) = 1/4^s
    #       Weighted over u==3 mod 4 (1/2): 1/2 * ((1 - 4/4^s)/3 + 1/4^s) = 1/6 - 1/(6 * 4^s)
    #     Total density for v >= 5:
    #       sum_{s>=2} (1/4^(s+1)) * (2/3 - 1/(6 * 4^s))
    #       = (2/3) * (1/64) / (3/4) - (1/6) * (1/1024) / (15/16)
    #       = 1/72 - 1/5760 = 79/5760
    d_even = Fraction(2, 3)
    d_v1 = Fraction(1, 4) * Fraction(7, 8)
    d_v3 = Fraction(1, 16) * Fraction(5, 8)
    d_v5plus = Fraction(1, 72) - Fraction(1, 5760)
    d_total = d_even + d_v1 + d_v3 + d_v5plus
    assert d_total == Fraction(5404, 5760) == Fraction(1351, 1440)
    print(f"  Exact asymptotic natural density: {d_total} = 5404/5760 = {float(d_total) * 100:.6f}% (previous 5359/5760 + 1/128)\n")


if __name__ == "__main__":
    check_dp_consistency()
    verify_pr451_k65(60000)
    verify_pr453_k66_and_coverage()
    print("ALL VERIFICATIONS PASSED.")
