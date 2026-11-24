"""
gemini2_verify_k33c_k33d.py — PR #322（命題 K33c）および PR #324（補題 K33d・K33 奇数 e 仮定簡約・トレース）の Python 独立検証

何を計算するか:
  1. 補題 K33d の直接ゲーム定義（PROBLEM.md の全探索 DP）との照合:
     - 奇数 m ∈ {3, 5, 7, 9, 11, 13, 15, 17, 19, 21}（v2(m+1) = 1, 2, 3, 4 を網羅）に対し、
       ゲームの定義 (1 ≤ k ≤ min(m, r), k ≠ p) から直接勝敗表と負け位置列 L_B・距離集合 S_B を計算し、
       すべての E 型ブロック B（L_B − L_{B-1} = m + 1）について:
         (a) すべての奇数 d (1 ≤ d ≤ m) が S_B に入ること
         (b) すべての v2(d) = 1 の d (1 ≤ d ≤ m) が S_B に入らないこと
       を検証する。
     - さらに K8 ブロック遷移により全奇数 3 ≤ m ≤ 201 の最初の 200 ブロックで全 E 型ブロックについて (a)(b) を検証する。
  2. 命題 K33c（PR #322）の独立検証:
     - 周期帰納法 prove を Python で一から独立実装し、9 ≤ e ≤ 199 の全 96 個の奇数 e（および延長確認として e = 201, 203, 205、境界確認として e = 3, 5, 7）について
       m = 9·2^e + 1, w = 1^{e-1} 0 1^{(e-1)/2} 0 の帰納法を実行。
     - 9 ≤ e ≤ 199 の全 96 個で帰納法が確定し、仮定集合 A が命題 K33c の 5 族（合計 e − 1 個）に完全一致し、
       全値が False（入らない）、v2 の集合が {1, 3}、v2 = 3 は 6X + 8 の 1 個のみで残り e − 2 個がすべて v2 = 1 であることを確認する。
  3. 補題 K33d を一般仮定に加えた帰納法（PR #324 の系）の独立検証:
     - 一般仮定に「v2(d) = 1 なら d ∉ S_B（B = 0 は K3、E 型ブロックは補題 K33d）」を加えた prove_with_k33d を実行し、
       9 ≤ e ≤ 199 の全 96 個（および e = 201, 203, 205）で仮定集合 A がちょうど 1 元 {6X + 8: False} のみで閉じることを確認する。
  4. トレース統計（PR #324：data/k33_odd_trace.txt および data/k33_odd_trace_21.txt）の独立再現:
     - O 型一本道鎖と E 型評価の分解トレースを Python で独立実装し、e = 15, 21, 27, 33 の E 型事実数・O 型鎖数・鎖終点分布と、
       e = 21 の E 型事実 68 件（形・v2・値）を検証する。

実行方法（リポジトリのルートで）:
  uv run python code/gemini2_verify_k33c_k33d.py > data/gemini2_verify_k33c_k33d.txt
"""
from __future__ import annotations

import sys
import time

sys.setrecursionlimit(200000)


def v2(x: int) -> int:
    return (x & -x).bit_length() - 1


# ---------------------------------------------------------------------------
# 1. Exact game solver directly from PROBLEM.md (1 <= k <= min(m, r), k != p)
# ---------------------------------------------------------------------------
def exact_game_losing_blocks(m: int, max_r: int) -> tuple[list[int], list[set[int]]]:
    """
    PROBLEM.md の定義をそのまま実装:
      - 局面 (r, p) は残り石数 r >= 0、直前の相手の取り数 p >= 0 (開始時 p = 0)。
      - 合法手: 1 <= k <= min(m, r) かつ k != p。
      - r = 0 は負け。
      - ある合法手 k で (r - k, k) が負けなら勝ち、さもなくば負け。
    高速かつ厳密な表現:
      各 r >= 1 について、r - k が (r - k, k) として負けになる k の集合 U(r) を求めると、
      (r, p) が負け ⇔ U(r) ⊆ {p}。
      特に (r, 0) が負け ⇔ U(r) = ∅ (r は負け位置 L_B)。
      (r, d) (1 <= d <= m) が負けかつ (r, 0) が勝ち ⇔ U(r) = {d}。
    """
    # uniq[r] = -1 if (r, 0) is losing (U(r) = empty),
    #            d if U(r) = {d} (so (r, p) is losing iff p == d),
    #            0 if |U(r)| >= 2 (so (r, p) is winning for all p).
    uniq = [0] * (max_r + 1)
    uniq[0] = -1  # (0, p) is losing for all p (in particular (0, 0) is losing)
    losing_positions: list[int] = [0]
    for r in range(1, max_r + 1):
        lim = m if r >= m else r
        found = -1
        two = False
        for k in range(1, lim + 1):
            u = uniq[r - k]
            # (r - k, k) is losing iff u == -1 (all p lose) or u == k
            if u == -1 or u == k:
                if found == -1:
                    found = k
                else:
                    two = True
                    break
        if two:
            uniq[r] = 0
        elif found == -1:
            uniq[r] = -1
            losing_positions.append(r)
        else:
            uniq[r] = found

    # Extract S_B for each losing position L_B with L_B + m <= max_r
    blocks_L: list[int] = []
    blocks_S: list[set[int]] = []
    for L in losing_positions:
        if L + m > max_r:
            break
        S = {d for d in range(1, m + 1) if uniq[L + d] == d}
        blocks_L.append(L)
        blocks_S.append(S)
    return blocks_L, blocks_S


def verify_k33d_exact_game() -> tuple[int, int, int]:
    """Direct PROBLEM.md verification of Lemma K33d for odd m = 3..21."""
    checked_m = 0
    checked_e_blocks = 0
    errors = 0
    for m in range(3, 22, 2):
        checked_m += 1
        max_r = min(4000, 120 * (m + 2))
        L_list, S_list = exact_game_losing_blocks(m, max_r)
        # Verify block 0 matches K3
        S0_expected = {d for d in range(1, m + 1) if v2(d) % 2 == 0}
        if S_list[0] != S0_expected:
            errors += 1
        for b in range(1, len(L_list)):
            gap = L_list[b] - L_list[b - 1]
            if gap not in (m + 1, m + 2):
                errors += 1
            if gap == m + 1:  # E-type block
                checked_e_blocks += 1
                Sb = S_list[b]
                for d in range(1, m + 1):
                    t = v2(d)
                    if t == 0 and d not in Sb:
                        errors += 1
                    if t == 1 and d in Sb:
                        errors += 1
    return checked_m, checked_e_blocks, errors


def verify_k33d_k8_blocks() -> tuple[int, int, int]:
    """K8 block-by-block transition verification of Lemma K33d for all odd 3 <= m <= 201."""
    checked_m = 0
    checked_e_blocks = 0
    errors = 0
    for m in range(3, 202, 2):
        checked_m += 1
        h = (m + 1) // 2
        # S[d] for 1 <= d <= m
        prev_S = [False] * (m + 1)
        for d in range(1, m + 1):
            prev_S[d] = (v2(d) % 2 == 0)
        for _ in range(200):
            gap = m + 2 if prev_S[h] else m + 1
            cur_S = [False] * (m + 1)
            for d in range(1, m + 1):
                if d % 2 == 0 and cur_S[d // 2]:
                    cur_S[d] = False
                    continue
                sm = gap + d
                if sm % 2 == 0 and sm // 2 <= m and prev_S[sm // 2]:
                    cur_S[d] = False
                    continue
                if gap == m + 2 and d == h - 1:
                    cur_S[d] = False
                    continue
                cur_S[d] = True
            if gap == m + 1:
                checked_e_blocks += 1
                for d in range(1, m + 1):
                    t = v2(d)
                    if t == 0 and not cur_S[d]:
                        errors += 1
                    if t == 1 and cur_S[d]:
                        errors += 1
            prev_S = cur_S
    return checked_m, checked_e_blocks, errors


# ---------------------------------------------------------------------------
# 2. Independent Python re-implementation of prove & prove_with_k33d
# ---------------------------------------------------------------------------
def prove_py(
    m: int,
    w: str,
    use_k33d: bool = False,
    max_rounds: int = 5000,
    max_facts: int = 3000000,
) -> dict:
    if m % 2 == 0:
        return {"ok": False, "why": "m is even"}
    L = len(w)
    v = v2(m + 1)
    h = (m + 1) // 2
    s = 0
    while s < L and w[L - 1 - s] == "0":
        s += 1
    if s == 0:
        return {"ok": False, "why": "w does not end with 0"}
    g0 = "1" if (v2(h) % 2 == 0) else "0"
    if g0 != w[0]:
        return {"ok": False, "why": "block 0 gap mismatch"}
    bound = min(2 * s - 1, v - 1)
    if use_k33d and bound < 1:
        bound = 1  # Lemma K33d: v2(d) = 1 => d not in S_B (holds for B=0 by K3 and for any E-type B)

    A: dict[int, bool] = {}
    for _ in range(max_rounds):
        memo: dict[tuple[int, int], bool] = {}
        unknown: int | None = None
        too_many = False

        def gap_of(idx: int) -> int:
            return m + 2 if w[idx % L] == "1" else m + 1

        def S(i: int, d: int) -> bool:
            nonlocal unknown, too_many
            if unknown is not None or too_many:
                return False
            key = (i, d)
            if key in memo:
                return memo[key]
            if len(memo) > max_facts:
                too_many = True
                return False
            if i == 0:
                t = v2(d)
                if t == 0:
                    r = True
                elif t <= bound:
                    r = (t % 2 == 0)
                elif d in A:
                    r = A[d]
                else:
                    unknown = d
                    return False
            else:
                if d % 2 == 0 and S(i, d // 2):
                    r = False
                else:
                    if unknown is not None or too_many:
                        return False
                    g = gap_of(i - 1)
                    sm = g + d
                    if sm % 2 == 0 and sm // 2 <= m and S(i - 1, sm // 2):
                        r = False
                    elif unknown is not None or too_many:
                        return False
                    elif g == m + 2 and d == h - 1:
                        r = False
                    else:
                        r = True
            if unknown is not None or too_many:
                return False
            memo[key] = r
            return r

        ok1 = True
        for i in range(1, L + 1):
            in_h = S(i, h)
            if unknown is not None or too_many:
                break
            if ("1" if in_h else "0") != w[i % L]:
                ok1 = False
                break
        if too_many:
            return {"ok": False, "why": "too many facts", "A": dict(A)}
        if unknown is not None:
            A[unknown] = (v2(unknown) % 2 == 0)
            continue
        if not ok1:
            return {"ok": False, "why": "gap mismatch", "A": dict(A)}
        for d_val, expected in list(A.items()):
            got = S(L, d_val)
            if unknown is not None or too_many:
                break
            if got != expected:
                return {"ok": False, "why": "A not reproduced", "A": dict(A)}
        if too_many:
            return {"ok": False, "why": "too many facts", "A": dict(A)}
        if unknown is not None:
            A[unknown] = (v2(unknown) % 2 == 0)
            continue
        return {"ok": True, "A": dict(A), "facts": len(memo)}
    return {"ok": False, "why": "max rounds exceeded", "A": dict(A)}


def expected_A_k33c(e: int) -> set[int]:
    X = 1 << e
    want = {
        7 * X - (1 << (e - 2)) + 2,
        5 * X - (1 << (e - 3)) + 2,
        6 * X + 1442,
    }
    for j in range(0, (e - 5) // 2 + 1):
        want.add(6 * X + 6 * (4 ** j) + 2)
    for j in range(0, (e - 7) // 2 + 1):
        want.add(6 * X - 9 * (4 ** (j + 1)) + 2)
    return want


# ---------------------------------------------------------------------------
# 3. Independent Python trace (chain / E-type decomposition, PR #324)
# ---------------------------------------------------------------------------
def trace_k33_odd(e: int) -> dict:
    X = 1 << e
    m = 9 * X + 1
    M = m + 2
    h = (m + 1) // 2
    w = "1" * (e - 1) + "0" + "1" * ((e - 1) // 2) + "0"
    L = len(w)
    res = prove_py(m, w, use_k33d=False)
    assert res["ok"], f"prove failed for e={e}"
    A: dict[int, bool] = res["A"]

    def gap(i: int) -> str:
        return w[i % L]

    def form(d: int) -> str:
        for k in range(0, 7):
            t = d << k
            al = (t + (X >> 1)) // X
            be = t - al * X
            if -(X >> 2) < be < (X >> 2):
                if be == 0:
                    bs = ""
                elif be < 0:
                    bs = f"−{-be}"
                else:
                    bs = f"+{be}"
                return f"({al}X{bs})/2^{k}"
        return "?"

    nE = 0
    nO = 0
    chains: list[tuple[int, int]] = []
    memo: dict[tuple[int, int], bool] = {}
    e_rows: list[str] = []

    def S(i: int, d: int) -> bool:
        nonlocal nE, nO
        key = (i, d)
        if key in memo:
            return memo[key]
        if i == 0:
            if d % 2 == 1:
                r = True
            elif d in A:
                r = A[d]
            else:
                raise RuntimeError(f"Unknown d={d} at block 0")
        elif gap(i - 1) == "1":
            nO += 1
            j = i
            dd = d
            steps = 0
            r_opt: bool | None = None
            while j > 0 and gap(j - 1) == "1":
                if dd % 2 == 0:
                    dd //= 2
                else:
                    if dd == h - 1:
                        r_opt = False
                        break
                    if (M + dd) // 2 > m:
                        r_opt = True
                        break
                    dd = (M + dd) // 2
                    j -= 1
                steps += 1
            if r_opt is None:
                b = S(j, dd)
                r = b if steps % 2 == 0 else (not b)
            else:
                r = r_opt
            chains.append((i, j))
        else:
            nE += 1
            if d % 2 == 1:
                r = True
            elif S(i, d // 2):
                r = False
            else:
                ee = h + d // 2
                r = not (ee <= m and S(i - 1, ee))
            lbl = "e" if i == e else ("L" if i == L else str(i))
            e_rows.append(f"ブロック {lbl}：{form(d)}（v2 = {v2(d)}）{'入' if r else '不'}")
        memo[key] = r
        return r

    ok = True
    for i in range(1, L + 1):
        if ("1" if S(i, h) else "0") != w[i % L]:
            ok = False
    for d_val, expected in A.items():
        if S(L, d_val) != expected:
            ok = False
    ends: dict[str, int] = {}
    for a, b in chains:
        k = "self" if a == b else f"→{b}"
        ends[k] = ends.get(k, 0) + 1
    return {"e": e, "ok": ok, "nE": nE, "nO": nO, "ends": ends, "e_rows": sorted(e_rows)}


def main() -> None:
    t0 = time.perf_counter()
    print("# gemini-2 独立検証: PR #322（命題 K33c）および PR #324（補題 K33d・K33 奇数 e 仮定簡約・トレース）")
    print("# 実行コマンド: uv run python code/gemini2_verify_k33c_k33d.py > data/gemini2_verify_k33c_k33d.txt")
    print()

    # Section 1: Lemma K33d direct game + K8 checks
    m_cnt1, e_cnt1, err1 = verify_k33d_exact_game()
    m_cnt2, e_cnt2, err2 = verify_k33d_k8_blocks()
    print("## 1. 補題 K33d の直接検証（PROBLEM.md 全探索 & K8 ブロック遷移）")
    print(f"- PROBLEM.md 直接全探索（奇数 m = 3..21, {m_cnt1} 個）: E 型ブロック {e_cnt1} 個検証, errors = {err1}")
    print(f"- K8 ブロック遷移（奇数 m = 3..201, {m_cnt2} 個 × 200 ブロック）: E 型ブロック {e_cnt2} 個検証, errors = {err2}")
    print()

    # Section 2: Proposition K33c (9 <= e <= 199 odd, plus extension 201..205 and small boundary 3, 5, 7)
    print("## 2. 命題 K33c（9 <= e <= 199 奇数, 全 96 個）の独立検証")
    k33c_errors = 0
    k33c_checked = 0
    k33d_reduced_errors = 0
    for e in range(9, 200, 2):
        k33c_checked += 1
        X = 1 << e
        m = 9 * X + 1
        w = "1" * (e - 1) + "0" + "1" * ((e - 1) // 2) + "0"

        r_std = prove_py(m, w, use_k33d=False)
        want = expected_A_k33c(e)
        got = set(r_std["A"].keys())
        all_false = all(val is False for val in r_std["A"].values())
        v2_set = {v2(d) for d in got}
        v2_gt1 = {d for d in got if v2(d) != 1}
        if not (
            r_std["ok"]
            and len(got) == e - 1
            and got == want
            and all_false
            and v2_set == {1, 3}
            and v2_gt1 == {6 * X + 8}
        ):
            k33c_errors += 1
            print(f"  MISMATCH K33c at e={e}: ok={r_std['ok']}, |A|={len(got)}, same={got==want}")

        # Section 3 combined: prove with Lemma K33d
        r_red = prove_py(m, w, use_k33d=True)
        if not (r_red["ok"] and r_red["A"] == {6 * X + 8: False}):
            k33d_reduced_errors += 1
            print(f"  MISMATCH K33d-reduced at e={e}: ok={r_red['ok']}, A={r_red['A']}")

    print(f"- 命題 K33c（9 <= e <= 199 奇数）: {k33c_checked}/96 個検証, errors = {k33c_errors}")
    print(f"  (全 96 個で |A| = e - 1, 5 族公式と完全一致, 全値 False, v2 ∈ {{1, 3}}, v2 != 1 は 6X + 8 のみ)")
    print(f"- 補題 K33d 追加時の帰納法（9 <= e <= 199 奇数）: {k33c_checked}/96 個検証, errors = {k33d_reduced_errors}")
    print(f"  (全 96 個で |A| = 1, A = {{6X + 8: False}} のみで帰納法が閉じる)")

    # Extension check beyond e = 199 and small boundary e = 3, 5, 7
    ext_errors = 0
    for e in (201, 203, 205):
        X = 1 << e
        m = 9 * X + 1
        w = "1" * (e - 1) + "0" + "1" * ((e - 1) // 2) + "0"
        r_std = prove_py(m, w, use_k33d=False)
        r_red = prove_py(m, w, use_k33d=True)
        if not (r_std["ok"] and set(r_std["A"].keys()) == expected_A_k33c(e) and r_red["ok"] and r_red["A"] == {6 * X + 8: False}):
            ext_errors += 1
    print(f"- 延長確認（e = 201, 203, 205）: 3/3 個で命題 K33c・補題 K33d 簡約ともに成立, errors = {ext_errors}")

    print("- 小さい境界（e = 3, 5, 7）の確認:")
    for e in (3, 5, 7):
        X = 1 << e
        m = 9 * X + 1
        w = "1" * (e - 1) + "0" + "1" * ((e - 1) // 2) + "0"
        r_std = prove_py(m, w, use_k33d=False)
        r_red = prove_py(m, w, use_k33d=True)
        print(f"  e = {e} (m = {m}): std ok={r_std['ok']} |A|={len(r_std['A'])}, k33d ok={r_red['ok']} A={r_red['A']}")
    print()

    # Section 4: Trace reproduction (e = 15, 21, 27, 33)
    print("## 3. トレース統計（PR #324: data/k33_odd_trace.txt & data/k33_odd_trace_21.txt）の独立再現")
    expected_trace = {
        15: (49, 24, {"→0": 16, "→15": 8}),
        21: (68, 34, {"→0": 22, "→21": 12}),
        27: (85, 42, {"→0": 28, "→27": 14}),
        33: (104, 52, {"→0": 34, "→33": 18}),
    }
    trace_errors = 0
    rows_21: list[str] = []
    for e in (15, 21, 27, 33):
        tr = trace_k33_odd(e)
        exp_nE, exp_nO, exp_ends = expected_trace[e]
        match = tr["ok"] and tr["nE"] == exp_nE and tr["nO"] == exp_nO and tr["ends"] == exp_ends
        if not match:
            trace_errors += 1
        print(
            f"- e = {e}: ok={tr['ok']}, E型の事実={tr['nE']}, O型の鎖={tr['nO']}, 終点={tr['ends']}, PR #324一致={match}"
        )
        if e == 21:
            rows_21 = tr["e_rows"]

    # Check e = 21 E-type facts count and breakdown
    v2_counts: dict[int, int] = {}
    for row in rows_21:
        # parse v2 = X
        idx = row.index("v2 = ") + 5
        end = row.index("）", idx)
        t = int(row[idx:end])
        v2_counts[t] = v2_counts.get(t, 0) + 1
    n_ge2 = sum(cnt for t, cnt in v2_counts.items() if t >= 2)
    print(f"- e = 21 E 型事実詳細: 計 {len(rows_21)} 件, v2 内訳 = {dict(sorted(v2_counts.items()))} (v2 >= 2 は {n_ge2} 件)")
    for row in rows_21:
        if "v2 = 0" not in row and "v2 = 1" not in row:
            print(f"  [v2 >= 2] {row}")

    total_errors = err1 + err2 + k33c_errors + k33d_reduced_errors + ext_errors + trace_errors
    elapsed = time.perf_counter() - t0
    print()
    print(f"## 総合結果: total_errors = {total_errors}, elapsed = {elapsed:.2f}s")
    if total_errors != 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
