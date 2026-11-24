"""
gemini2_verify_lean_k12_k10c_k11.py — PR #404（Lean K12a）・PR #406（Lean K10c/K10b）・
PR #408（Lean K11）・PR #410（Lean not_alt_seven / K10c_full）および PR #401（claims-sync）の
独立 Python 3 検証・直接 DP クロスチェックスクリプト。

何を計算するか:
  1. PROBLEM.md の定義のみに基づく O(N) 厳密 DP（漸化式 R / K8 不使用）を用いて、
     - 定理 K12 (a)：m % 4 = 1, m ≥ 5, v2(3h+1) = 2, Q = (11h+5)/8 が奇数（m ≤ 2000 全件）で
       0 ≤ n ≤ 6(3m+5) + 10 において (n, 0) が P ⇔ n mod (3m+5) ∈ {0, m+2, 2m+4} を検証。
     - 定理 K10c / K10c_full・系 K10 (b)・not_alt_seven：m + 1 = 8u（u 奇数、m ≤ 2000 全件、m = 7 含む）で
       交互型なら u ≥ 3 ∧ v2(9u+1) 奇数 ∧ v2(11u+1) 偶数（かつ v2(9u+1) = 1 と同値）、
       u ≡ 3, 7 (mod 8) なら非交互型、m = 7 は (25, 0) ∈ P で非交互型を検証。
     - 定理 K11：m + 1 = 2^v * u（v ≥ 5 奇数、u 奇数、m ≤ 2000 全件）で非交互型かつ
       Lean 証明の反例位置 n ∈ {2m+3, 3m+4} での破れを検証。
  2. PR #401（origin/claude-1/claims-sync）の 12 個の claims/*.yaml が gemini-2 査読 PR 群と
     バイト単位で完全一致することを検証。

実行方法（リポジトリのルートで）:
  uv run python code/gemini2_verify_lean_k12_k10c_k11.py > data/gemini2_verify_lean_k12_k10c_k11.txt
"""

from __future__ import annotations

import subprocess
import time


def v2(x: int) -> int:
    c = 0
    while (x & 1) == 0:
        x >>= 1
        c += 1
    return c


def fast_exact_dp_rows(m: int, nmax: int) -> list[int]:
    """PROBLEM.md の定義のみに基づく O(N) 厳密 DP（漸化式 R / K8 不使用）。"""
    typ = [0] * (nmax + 1)
    typ[0] = -1
    single_cnt = [0] * (nmax + 1)
    single_val = [0] * (nmax + 1)
    last_all = 0
    for r in range(1, nmax + 1):
        cnt = single_cnt[r]
        val = single_val[r]
        d = r - last_all
        if d <= m:
            cnt += 1
            if cnt == 1:
                val = d
        if cnt == 0:
            typ[r] = -1
            last_all = r
        elif cnt == 1:
            typ[r] = val
            nxt = r + val
            if nxt <= nmax:
                c2 = single_cnt[nxt] + 1
                single_cnt[nxt] = c2
                if c2 == 1:
                    single_val[nxt] = val
        else:
            typ[r] = -2
    return typ


def is_alt_on(typ: list[int], m: int) -> bool:
    per = 2 * m + 3
    return all((typ[n] == -1) == (n % per in (0, m + 2)) for n in range(len(typ)))


def main() -> None:
    t0 = time.perf_counter()
    print("# gemini-2 独立 Python 3 検証：Lean 4 PR #404/#406/#408/#410 および PR #401")

    # 1. Theorem K12 (a) (PR #404)
    k12_ms = []
    for m in range(5, 2001, 4):
        h = (m + 1) // 2
        if v2(3 * h + 1) == 2 and ((11 * h + 5) // 8) % 2 == 1:
            k12_ms.append(m)
            L = 3 * m + 5
            nmax = 6 * L + 10
            typ = fast_exact_dp_rows(m, nmax)
            ok = all(
                (typ[n] == -1) == (n % L in (0, m + 2, 2 * m + 4))
                for n in range(nmax + 1)
            )
            assert ok, f"K12a DP mismatch at m={m}"
    print(f"\n[1] 定理 K12 (a) 直接 DP クロスチェック (5 <= m <= 2000):")
    print(f"    該当 m 個数 = {len(k12_ms)} (最小={k12_ms[0]}, 最大={k12_ms[-1]}), 110型一致 = {len(k12_ms)}/{len(k12_ms)}")

    # 2. Theorem K10c / K10c_full / K10b / not_alt_seven (PR #406, #410)
    k10c_ms = [8 * u - 1 for u in range(1, 251, 2) if 8 * u - 1 <= 2000]
    k10c_alt_cnt = 0
    k10b_cnt = 0
    k10c_witness_ok = 0
    k10c_nonalt_cnt = 0
    for m in k10c_ms:
        u = (m + 1) // 8
        assert u % 2 == 1
        nmax = 6 * (2 * m + 3) + 10
        typ = fast_exact_dp_rows(m, nmax)
        alt = is_alt_on(typ, m)
        cond_lean = (u >= 3) and (v2(9 * u + 1) % 2 == 1) and (v2(11 * u + 1) % 2 == 0)
        cond_v1 = (u >= 3) and (v2(9 * u + 1) == 1) and (v2(11 * u + 1) % 2 == 0)
        assert cond_lean == cond_v1, f"Equivalence mismatch at u={u}"
        if alt:
            assert cond_lean, f"K10c_full violated at m={m}, u={u}"
            k10c_alt_cnt += 1
        else:
            k10c_nonalt_cnt += 1
        if u % 8 in (3, 7):
            assert not alt, f"K10b violated at m={m}, u={u}"
            k10b_cnt += 1
        if not cond_lean:
            # Verify explicit witness from Lean proof: either (2m+3,0) is N or (3m+4,0) is P
            w_ok = (typ[2 * m + 3] != -1) or (typ[3 * m + 4] == -1)
            assert w_ok, f"K10c witness mismatch at m={m}, u={u}"
            k10c_witness_ok += 1
    # Explicit m = 7 check (not_alt_seven)
    typ7 = fast_exact_dp_rows(7, 40)
    assert typ7[25] == -1 and (25 % 17 == 8)
    # Equivalence check over u odd < 10000
    for u in range(1, 10000, 2):
        lhs = (v2(9 * u + 1) % 2 == 1) and (v2(11 * u + 1) % 2 == 0)
        rhs = (v2(9 * u + 1) == 1) and (v2(11 * u + 1) % 2 == 0)
        assert lhs == rhs
    print(f"\n[2] 定理 K10c / K10c_full・系 K10 (b)・not_alt_seven 直接 DP 検証 (m+1=8u, u奇数, m<=2000):")
    print(f"    対象 m = {len(k10c_ms)} 件 (交互型={k10c_alt_cnt}, 非交互型={k10c_nonalt_cnt})")
    print(f"    K10c_full 必要条件違反 = 0, K10b (u≡3,7 mod 8) 非交互型 = {k10b_cnt}/{k10b_cnt}")
    print(f"    条件不成立 {k10c_witness_ok} 件すべてで Lean 反例位置 (2m+3 ∈ N または 3m+4 ∈ P) を確認")
    print(f"    m=7: (25, 0) ∈ P (25 mod 17 = 8), および v2(9u+1) 奇数⇔=1 (under v2(11u+1) 偶数) 全奇数 u<10000 一致")

    # 3. Theorem K11 (PR #408)
    k11_ms = []
    k11_w_b = 0
    k11_w_c = 0
    for m in range(2, 2001):
        v = v2(m + 1)
        if v >= 5 and v % 2 == 1:
            k11_ms.append(m)
            nmax = 4 * (2 * m + 3) + 10
            typ = fast_exact_dp_rows(m, nmax)
            assert not is_alt_on(typ, m), f"K11 violated at m={m}"
            # Verify Lean proof witnesses: either (2m+3, 0) is N (g_notalt_b) or (3m+4, 0) is P (g_notalt_c)
            if typ[2 * m + 3] != -1:
                k11_w_b += 1
            elif typ[3 * m + 4] == -1:
                k11_w_c += 1
            else:
                raise AssertionError(f"K11 witness mismatch at m={m}")
    print(f"\n[3] 定理 K11 直接 DP 検証 (v2(m+1) >= 5 奇数, m <= 2000):")
    print(f"    対象 m = {len(k11_ms)} 件すべて非交互型 (2m+3 ∈ N: {k11_w_b} 件, 3m+4 ∈ P: {k11_w_c} 件)")

    # 4. PR #401 claims/*.yaml exact byte-for-byte audit vs gemini-2 review PRs
    sources = {
        "K33d.yaml": "origin/gemini-2/review-k33c-k33d",
        "K59.yaml": "origin/gemini-2/review-k33ext-k58-k59",
        "K57.yaml": "origin/gemini-2/review-k57fix-k34-k58",
        "K33.yaml": "origin/gemini-2/review-k33-k34-k58-symbolic",
        "K34.yaml": "origin/gemini-2/review-k33-k34-k58-symbolic",
        "K58.yaml": "origin/gemini-2/review-k33-k34-k58-symbolic",
        "K3.yaml": "origin/gemini-2/review-lean-k60-k62",
        "K5.yaml": "origin/gemini-2/review-lean-k60-k62",
        "K60.yaml": "origin/gemini-2/review-lean-k60-k62",
        "K4.yaml": "origin/gemini-2/review-k61k62fix-lean-k4-dp",
        "K61.yaml": "origin/gemini-2/review-k61k62fix-lean-k4-dp",
        "K62.yaml": "origin/gemini-2/review-k61k62fix-lean-k4-dp",
    }

    def show(ref: str, p: str) -> str:
        return subprocess.check_output(
            ["git", "show", f"{ref}:{p}"], text=True, encoding="utf-8"
        ).replace("\r\n", "\n")

    matched = 0
    for fname, gbr in sources.items():
        assert show("origin/claude-1/claims-sync", f"claims/{fname}") == show(
            gbr, f"claims/{fname}"
        ), f"PR #401 claims/{fname} differs from {gbr}"
        matched += 1
    print(f"\n[4] PR #401 (claims-sync) 監査:")
    print(f"    claims/*.yaml バイト一致 = {matched}/{len(sources)} (改変・自己昇格 0 件)")

    elapsed = time.perf_counter() - t0
    print(f"\nALL CHECKS PASSED in {elapsed:.2f}s.")


if __name__ == "__main__":
    main()
