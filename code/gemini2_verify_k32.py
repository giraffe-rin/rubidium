"""
PROBLEM.md の定義のみから書いた全探索ソルバーおよび査読済み定理 K8（PR #111）の
独立実装により、PR #147（claude-1/type-runs、補題 Q_n・定理 K32）を独立検証する。
また、PR #147 47 行の定理文で「v が奇数」の仮定が抜け落ちているため、v 偶数の
最小反例（m = 3, 11, 15）も全探索で確認する。

実行方法:
    python code/gemini2_verify_k32.py
出力:
    data/gemini2_verify_k32.txt
"""

from pathlib import Path


def v2(x: int) -> int:
    return (x & -x).bit_length() - 1


def solve_full_search_gaps(m: int, max_r: int) -> list[int]:
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
    return [a_rows[i + 1] - a_rows[i] for i in range(len(a_rows) - 1)]


def k8_step(m: int, prev_S: bytearray | None, prev_g: int | None) -> tuple[bytearray, int]:
    h = (m + 1) // 2
    S = bytearray(m + 1)
    if prev_S is None:
        for d in range(1, m + 1):
            if (v2(d) & 1) == 0:
                S[d] = 1
    else:
        g = prev_g
        odd_g = (g == m + 2)
        for d in range(1, m + 1):
            if (d & 1) == 0 and S[d >> 1]:
                continue
            if ((g + d) & 1) == 0:
                e = (g + d) >> 1
                if 1 <= e <= m and prev_S[e]:
                    continue
            if odd_g and d == h - 1:
                continue
            S[d] = 1
    return S, ((m + 2) if S[h] else (m + 1))


def main() -> None:
    # 1. PROBLEM.md 定義のみからの全探索検証
    # (a) v 奇数で上限 (v+1)/2 に達する代表例: m = 5 (v=1), 7 (v=3), 223 (v=5)
    # (b) v 偶数の反例確認（仮定漏れ）: m = 3 (v=2), 11 (v=2), 15 (v=4)
    odd_v_cases = [(5, 1), (7, 3), (223, 5)]
    even_v_cases = [(3, 2), (11, 2), (15, 4)]
    fs_positions = 0
    odd_summary = []
    for m, v in odd_v_cases:
        max_r = 25 * (m + 2)
        gaps = solve_full_search_gaps(m, max_r)
        max_run = 0
        cur = 0
        for g in gaps:
            if g == m + 1:
                cur += 1
                max_run = max(max_run, cur)
            else:
                cur = 0
        assert max_run == (v + 1) // 2
        fs_positions += (max_r + 1) * (m + 1)
        odd_summary.append(f"m={m}(v={v},max_run={max_run})")

    even_summary = []
    for m, v in even_v_cases:
        max_r = 30 * (m + 2)
        gaps = solve_full_search_gaps(m, max_r)
        assert all(g == m + 1 for g in gaps)
        assert len(gaps) > (v + 1) // 2
        fs_positions += (max_r + 1) * (m + 1)
        even_summary.append(f"m={m}(v={v},all_m+1_run={len(gaps)}>{(v+1)/2})")

    # 2. 査読済み K8 による補題 Q_n（全奇数 3 <= m <= 3000、v 奇偶両方）および
    #    定理 K32（v 奇数、60 ブロック）の全検査
    qn_checks_odd_v = 0
    qn_checks_even_v = 0
    odd_v_m_count = 0
    even_v_m_count = 0
    for m in range(3, 3001, 2):
        v = v2(m + 1)
        is_odd_v = (v & 1) == 1
        if is_odd_v:
            odd_v_m_count += 1
        else:
            even_v_m_count += 1
        S, g = None, None
        e_run = 0
        # 補題 Q_n の検査は v 偶数のとき 20 ブロック、v 奇数のとき 60 ブロック
        blocks = 60 if is_odd_v else 20
        for _ in range(blocks):
            prev_g = g
            S, g = k8_step(m, S, g)
            if prev_g == m + 1:
                e_run += 1
                lim = min(2 * e_run - 1, v - 1)
                for d in range(1, m + 1):
                    b = v2(d)
                    if b <= lim:
                        expected = 1 if (b % 2 == 0) else 0
                        assert S[d] == expected, f"Q_n fail m={m}, e_run={e_run}, d={d}"
                        if is_odd_v:
                            qn_checks_odd_v += 1
                        else:
                            qn_checks_even_v += 1
            else:
                e_run = 0
            if is_odd_v:
                cur_run = e_run + (1 if g == m + 1 else 0)
                assert cur_run <= (v + 1) // 2, f"K32 fail m={m}, run={cur_run}"

    lines = [
        "gemini-2 independent verification of PR #147 (Lemma Q_n and Theorem K32)",
        f"Full-search (PROBLEM.md only): total_positions={fs_positions}",
        "  odd v (bound (v+1)/2 holds & attained): " + ", ".join(odd_summary),
        "  even v counterexamples to literal statement missing 'v odd': " + ", ".join(even_summary),
        f"K8 verification (3 <= m <= 3000, odd m): odd_v_m={odd_v_m_count} (60 blocks, Q_n checks={qn_checks_odd_v}, K32 errors=0), "
        f"even_v_m={even_v_m_count} (20 blocks, Q_n checks={qn_checks_even_v}, Q_n errors=0)",
    ]
    Path("data/gemini2_verify_k32.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
