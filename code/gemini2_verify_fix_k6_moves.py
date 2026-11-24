"""
PROBLEM.md の正確な定義のみから書いた全探索ソルバーにより、
PR #122（claude-1/fix-k6-moves、K6 の補足「先手の必勝手」の訂正）を独立検証する。

実行方法:
    python code/gemini2_verify_fix_k6_moves.py
出力:
    data/gemini2_verify_fix_k6_moves.txt
"""

from pathlib import Path


def solve_game(m: int, max_r: int) -> list[list[bool]]:
    """PROBLEM.md の定義のみに基づく全探索 DP。
    win[r][p] = True ⇔ 局面 (r, p) が先手必勝（N 局面）。
    """
    win = [[False] * (m + 1) for _ in range(max_r + 1)]
    for r in range(1, max_r + 1):
        limit = min(m, r)
        # 1 <= k <= limit のうち、手 k により相手が負ける（not win[r-k][k]）ものの個数と唯一の k
        losing_count = 0
        only_losing_k = -1
        for k in range(1, limit + 1):
            if not win[r - k][k]:
                losing_count += 1
                only_losing_k = k
        if losing_count == 0:
            continue
        row = win[r]
        if losing_count >= 2:
            for p in range(m + 1):
                row[p] = True
        else:
            for p in range(m + 1):
                if p != only_losing_k:
                    row[p] = True
    return win


def verify_range(m_list: list[int], max_n: int) -> dict[str, int]:
    total_positions = 0
    total_n_starts = 0
    k6_errors = 0
    old_errors = 0
    new_errors = 0
    first_old_err = None

    for m in m_list:
        assert m % 8 == 5
        h = (m + 1) // 2
        period = 2 * m + 3
        win = solve_game(m, max_n)
        total_positions += (max_n + 1) * (m + 1)

        for n in range(1, max_n + 1):
            c = n % period
            expected_n = (c != 0 and c != m + 2)
            actual_n = win[n][0]
            if expected_n != actual_n:
                k6_errors += 1
                continue
            if not actual_n:
                continue
            total_n_starts += 1

            # 旧版の手（PR #10 の補足）
            old_k = c if c < m + 2 else c - (m + 2)
            if not (1 <= old_k <= min(m, n)) or win[n - old_k][old_k]:
                old_errors += 1
                if first_old_err is None:
                    first_old_err = (m, n, c, old_k)

            # 訂正版の手（PR #122）
            if 0 < c <= m:
                new_k = c
            elif c == m + 1:
                new_k = h
            else:
                new_k = c - (m + 2)
            if not (1 <= new_k <= min(m, n)) or win[n - new_k][new_k]:
                new_errors += 1

    return {
        "m_count": len(m_list),
        "total_positions": total_positions,
        "total_n_starts": total_n_starts,
        "k6_errors": k6_errors,
        "old_errors": old_errors,
        "new_errors": new_errors,
        "first_old_err": first_old_err,
    }


def main() -> None:
    # 検算用小さな例（PROBLEM.md）
    w1 = solve_game(1, 20)
    assert all(w1[n][0] for n in range(1, 21))
    w2 = solve_game(2, 10)
    assert w2[3][0] is False

    m_std = list(range(5, 102, 8))
    res_std = verify_range(m_std, 3000)

    m_ext = list(range(5, 134, 8))
    res_ext = verify_range(m_ext, 3000)

    lines = [
        "gemini-2 independent verification of PR #122 (fix-k6-moves)",
        f"Range 1: m ≡ 5 (mod 8), 5 <= m <= 101 ({res_std['m_count']} values), 1 <= n <= 3000",
        f"  total_positions={res_std['total_positions']}, N_starts={res_std['total_n_starts']}, "
        f"k6_errors={res_std['k6_errors']}, old_errors={res_std['old_errors']}, new_errors={res_std['new_errors']}, "
        f"first_old_err={res_std['first_old_err']}",
        f"Range 2: m ≡ 5 (mod 8), 5 <= m <= 133 ({res_ext['m_count']} values), 1 <= n <= 3000",
        f"  total_positions={res_ext['total_positions']}, N_starts={res_ext['total_n_starts']}, "
        f"k6_errors={res_ext['k6_errors']}, old_errors={res_ext['old_errors']}, new_errors={res_ext['new_errors']}",
    ]
    out_path = Path("data/gemini2_verify_fix_k6_moves.txt")
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))
    assert res_std["k6_errors"] == 0 and res_std["new_errors"] == 0
    assert res_ext["k6_errors"] == 0 and res_ext["new_errors"] == 0


if __name__ == "__main__":
    main()
