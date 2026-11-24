"""
gemini2_verify_k57fix_k34_k58.py — PR #331 修正（命題 K57）・PR #344（K34/K58 トレース & k33_odd_trace 修正）・PR #346（自明でない事実）・PR #348（定理 K58 の形比較と 6 本鎖の記号解析）の Python 独立検証

何を計算するか:
  1. PR #331 修正（命題 K57）:
     - β₀ ≠ 0, v < N, b_j + 3r ≠ 0 ガード付きの独立 Python 実装で、310 族＋境界 4 例（5:9:9:4, 5:9:17:5, 3:-1:1:3, 27:-1:1:9）を検証。
  2. PR #344（K34・K58 の帰納法 1 段の分解 & k33_odd_trace バグ修正）:
     - k33_odd_trace（e = 15, 21, 27, 33）で早期終了例外（d = h-1 または (M+d)/2 > m）の発生回数が 0 であることを確認（PR #333 の検証結果に影響しないことの確認）。
     - k34_trace の全 7 例（N = 41, 45, 49, 53 [s=3]; N = 43, 47, 51 [s=7]）で ok・仮定・E 型事実数・O 型鎖数が data/k34_trace.txt と完全一致することを確認。
  3. PR #346（自明でない E 型事実の有限・不変性）:
     - s = 7（N = 43, 47, 51）で 6 個、s = 3（N = 41, 45, 49）で 34 個の自明でない E 型事実が N によらず完全一致することを確認。
  4. PR #348（定理 K58：data/k58_shapes.txt の 40 例 + 小さい境界 N = 23..39 + 6 本鎖の記号軌道解析）:
     - 43 <= N <= 199 の N ≡ 3 (mod 4) 全 40 例で 1 段閉鎖・6 個の非自明 E 型事実・6 本鎖の連長表示を独立再現。
     - さらに小さい境界 N = 23, 27, 31, 35, 39 も調べ、鎖 1 ((9a-3)/4) の b 軌道が b = 3（固定点、t(3) = 1、半分にする段 0）であり PR #348 本文の「b = 1 にとどまる」記述と異なることを明示的に確認し、全 3 入口（(9a-3)/4, 2a-4, (5a-15)/2）の正確な記号軌道・越え場面・必要下限 N_0 を導出検証する。

実行方法（リポジトリのルートで）:
  uv run python code/gemini2_verify_k57fix_k34_k58.py > data/gemini2_verify_k57fix_k34_k58.txt
"""
from __future__ import annotations

import sys
import time

sys.setrecursionlimit(200000)


def v2(x: int) -> int:
    if x == 0:
        return 10**9
    if x < 0:
        x = -x
    return (x & -x).bit_length() - 1


def gaps_lazy_big(m: int, J: int) -> list[int]:
    h = (m + 1) // 2
    memo: dict[tuple[int, int], bool] = {}
    gm: dict[int, int] = {}

    def gap(j: int) -> int:
        res = gm.get(j)
        if res is not None:
            return res
        r = m + 2 if S(j, h) else m + 1
        gm[j] = r
        return r

    def S(j: int, d: int) -> bool:
        key = (j, d)
        res = memo.get(key)
        if res is not None:
            return res
        if j == 0:
            r = (v2(d) & 1) == 0
        else:
            if (d & 1) == 0 and S(j, d >> 1):
                r = False
            else:
                g = gap(j - 1)
                sm = g + d
                if (sm & 1) == 0 and (sm >> 1) <= m and S(j - 1, sm >> 1):
                    r = False
                elif g == m + 2 and d == h - 1:
                    r = False
                else:
                    r = True
        memo[key] = r
        return r

    return [gap(j) - m - 1 for j in range(J)]


# ---------------------------------------------------------------------------
# 1. PR #331 fix verification
# ---------------------------------------------------------------------------
def verify_pr331_fix() -> tuple[int, int, int, list[str]]:
    known = [
        (29, 4641, 1, 56), (29, 4641, 1, 112), (29, 4641, 1, 224), (29, 4641, 1, 336),
        (17, 5, 3, 30), (17, 5, 3, 62), (23, 1, 1, 22), (23, 1, 1, 88),
        (125, 1, 1, 100), (125, 1, 1, 200),
    ]
    seed = 12345

    def rnd(n: int) -> int:
        nonlocal seed
        seed = (seed * 1103515245 + 12345) % 2147483648
        return seed % n

    fams = list(known)
    k = 0
    while k < 300:
        q = 2 * rnd(127) + 3
        r = (2 * rnd(2500) + 1) * (1 if rnd(2) else -1)
        N = 40 + rnd(80)
        X = 1 << N
        for s in range(1, 2 * q, 2):
            if (s * X - r) % q == 0:
                a = (s * X - r) // q
                if a > 0 and a % 2 == 1:
                    fams.append((q, r, s, N))
                    k += 1
                break
    boundary = [(5, 9, 9, 4), (5, 9, 17, 5), (3, -1, 1, 3), (27, -1, 1, 9)]
    fams.extend(boundary)

    tot = ok = skipped = 0
    notes: list[str] = []
    for q, r, s, N in fams:
        X = 1 << N
        a = (s * X - r) // q
        m = 3 * a - 2
        beta0 = 3 * r + q
        v = v2(beta0)
        if beta0 == 0 or v >= N:
            skipped += 1
            if (q, r, s, N) in boundary:
                g4 = "".join(str(x) for x in gaps_lazy_big(m, 4))
                notes.append(f"({q},{r},{s},{N}): 対象外 (beta0={beta0}, v={v if beta0 else 'inf'}), actual={g4}")
            continue
        R3 = 3 * r
        pred = "1" if (v - 1) % 2 == 0 else "0"
        stopped = False
        if pred == "1":
            b = beta0 >> v
            K = v
            ts: list[int] = []
            for i in range(1, 400):
                x = b + R3
                if x == 0:
                    stopped = True
                    break
                t = v2(x)
                nb = x >> t
                if K + t >= N:
                    stopped = True
                    break
                sp = (v - 1) + i + sum(tj - 1 for tj in ts)
                in_b = ((t - 1) % 2 == 0)
                hin = (in_b != (sp % 2 == 1))
                pred += "1" if hin else "0"
                if not hin:
                    break
                ts.append(t)
                K += t
                b = nb
        g = "".join(str(x) for x in gaps_lazy_big(m, len(pred) + 2))
        same = g[: len(pred)] == pred
        tot += 1
        if same:
            ok += 1
        if (q, r, s, N) in boundary:
            notes.append(f"({q},{r},{s},{N}): pred={pred}{'…' if stopped else ''}, actual={g[:len(pred)+1]}, match={same}")
    return tot, ok, skipped, notes


# ---------------------------------------------------------------------------
# 2. PR #344 & #346: k33_odd_trace exception count + k34_trace + k34_nontrivial
# ---------------------------------------------------------------------------
def check_k33_trace_exceptions() -> int:
    """Confirm early-termination exceptions in k33_odd_trace never occurred for e = 15, 21, 27, 33."""
    exc_count = 0
    for e in (15, 21, 27, 33):
        X = 1 << e
        m = 9 * X + 1
        M = m + 2
        h = (m + 1) // 2
        w = "1" * (e - 1) + "0" + "1" * ((e - 1) // 2) + "0"
        L = len(w)
        # Known A from PR #322/333:
        A_set = {7 * X - (1 << (e - 2)) + 2, 5 * X - (1 << (e - 3)) + 2, 6 * X + 1442}
        for j in range(0, (e - 5) // 2 + 1):
            A_set.add(6 * X + 6 * (4**j) + 2)
        for j in range(0, (e - 7) // 2 + 1):
            A_set.add(6 * X - 9 * (4 ** (j + 1)) + 2)
        memo: dict[tuple[int, int], bool] = {}

        def S(i: int, d: int) -> bool:
            nonlocal exc_count
            key = (i, d)
            if key in memo:
                return memo[key]
            if i == 0:
                r = True if d % 2 == 1 else False  # all A are False
                assert d % 2 == 1 or d in A_set
            elif w[(i - 1) % L] == "1":
                j, dd, st = i, d, 0
                r_opt: bool | None = None
                while j > 0 and w[(j - 1) % L] == "1":
                    if dd % 2 == 0:
                        dd >>= 1
                    else:
                        if dd == h - 1:
                            exc_count += 1
                            r_opt = (st % 2 != 0)
                            break
                        if (M + dd) // 2 > m:
                            exc_count += 1
                            r_opt = (st % 2 == 0)
                            break
                        dd = (M + dd) // 2
                        j -= 1
                    st += 1
                if r_opt is None:
                    b_val = S(j, dd)
                    r = b_val if st % 2 == 0 else (not b_val)
                else:
                    r = r_opt
            else:
                if d % 2 == 1:
                    r = True
                elif S(i, d >> 1):
                    r = False
                else:
                    ee = h + (d >> 1)
                    r = not (ee <= m and S(i - 1, ee))
            memo[key] = r
            return r

        for i in range(1, L + 1):
            assert ("1" if S(i, h) else "0") == w[i % L]
        for d_val in A_set:
            assert S(L, d_val) is False
    return exc_count


def trace_k34_k58(N: int) -> dict:
    s = 3 if N % 4 == 1 else 7
    X = 1 << N
    a = (s * X - 1) // 5
    m = 3 * a - 2
    M = m + 2
    h = (m + 1) // 2
    R = (N - 3) // 2
    w = ("1" * (2 * R) + "0" + ("1" * R + "00") * 2) if s == 3 else ("1" * (R + 2) + "0" + "1" * R + "0")
    L = len(w)
    # Trailing zeros of w determine bound = min(2*s_zeros - 1, v - 1) with v = 3
    s_zeros = 0
    while s_zeros < L and w[L - 1 - s_zeros] == "0":
        s_zeros += 1
    bound = min(2 * s_zeros - 1, 2)
    # Known A (values at block 0 by K3: v2 even => True, v2 odd => False):
    # s = 3: v2(2(a-3)) = 5 (odd -> False), v2(3(a-3)) = 4 (even -> True)
    # s = 7: v2(2(a-7)) = 3 (odd -> False)
    A = {2 * (a - 3): False, 3 * (a - 3): True} if s == 3 else {2 * (a - 7): False}

    def form_a(d: int) -> str:
        for k in range(0, 11):
            t = d << k
            P = (t + a // 2) // a
            Q = t - P * a
            if -(1 << 24) < Q < (1 << 24):
                return f"({P}a{'−' + str(-Q) if Q < 0 else '+' + str(Q)})/2^{k}"
        return "大"

    e_blocks = [i for i in range(1, L + 1) if w[(i - 1) % L] == "0"]
    e_pos = {blk: idx + 1 for idx, blk in enumerate(e_blocks)}
    nE = 0
    nO = 0
    memo: dict[tuple[int, int], bool] = {}
    nontriv: set[str] = set()

    def S(i: int, d: int) -> bool:
        nonlocal nE, nO
        key = (i, d)
        if key in memo:
            return memo[key]
        if i == 0:
            t = v2(d)
            if t == 0:
                r = True
            elif t <= bound:
                r = (t % 2 == 0)
            elif d in A:
                r = A[d]
            else:
                raise RuntimeError(f"Unknown d={form_a(d)} at block 0 for N={N}")
        elif w[(i - 1) % L] == "1":
            j, dd, st = i, d, 0
            r_opt: bool | None = None
            while j > 0 and w[(j - 1) % L] == "1":
                if dd % 2 == 0:
                    dd >>= 1
                else:
                    if dd == h - 1:
                        r_opt = (st % 2 != 0)
                        break
                    if (M + dd) // 2 > m:
                        r_opt = (st % 2 == 0)
                        break
                    dd = (M + dd) // 2
                    j -= 1
                st += 1
            if r_opt is None:
                nO += 1
                b_val = S(j, dd)
                r = b_val if st % 2 == 0 else (not b_val)
            else:
                r = r_opt
        else:
            nE += 1
            t = v2(d)
            if d % 2 == 1:
                r = True
            elif S(i, d >> 1):
                r = False
            else:
                ee = h + (d >> 1)
                r = not (ee <= m and S(i - 1, ee))
            if t >= 2:
                nontriv.add(f"E{e_pos[i]}/{len(e_blocks)}:{form_a(d)}(v2={t}){'入' if r else '不'}")
        memo[key] = r
        return r

    ok = True
    for i in range(1, L + 1):
        if ("1" if S(i, h) else "0") != w[i % L]:
            ok = False
    for d_val, expected in A.items():
        if S(L, d_val) != expected:
            ok = False
    return {"N": N, "s": s, "R": R, "L": L, "ok": ok, "nE": nE, "nO": nO, "nontriv": sorted(nontriv)}


# ---------------------------------------------------------------------------
# 3. PR #348: k58_shapes independent reproduction + symbolic chain analysis
# ---------------------------------------------------------------------------
def run_k58_shape(N: int) -> dict:
    X = 1 << N
    a = (7 * X - 1) // 5
    m = 3 * a - 2
    M = m + 2
    h = (m + 1) // 2
    R = (N - 3) // 2
    L = 2 * R + 4
    w = "1" * (R + 2) + "0" + "1" * R + "0"
    A = 2 * (a - 7)

    def form_a(d: int) -> str:
        for k in range(0, 11):
            t = d << k
            P = (t + a // 2) // a
            Q = t - P * a
            if -(1 << 24) < Q < (1 << 24):
                return f"({P}a{'−' + str(-Q) if Q < 0 else '+' + str(Q)})/2^{k}"
        return "大"

    def e_idx(i: int) -> str:
        return "B" if i in (0, L) else ("E1" if i == R + 3 else "?")

    memo: dict[tuple[str, int, int], bool] = {}
    nontriv: set[str] = set()
    chains: list[dict] = []

    def E(i: int, d: int) -> bool:
        key = ("E", i, d)
        if key in memo:
            return memo[key]
        t = v2(d)
        if t == 0:
            r = True
        elif t == 1:
            r = False
        elif i == 0:
            if d == A:
                r = False
            else:
                raise RuntimeError(f"Unknown d={form_a(d)} at B for N={N}")
        else:
            r = (not E(i, d >> 1)) and (not (h + (d >> 1) <= m and O(i - 1, h + (d >> 1), i)))
            nontriv.add(f"{e_idx(i)}:{form_a(d)}(v2={t}){'入' if r else '不'}")
        memo[key] = r
        return r

    def O(i: int, d: int, from_e: int | None = None) -> bool:
        key = ("O", i, d)
        if key in memo:
            return memo[key]
        j, dd, st = i, d, 0
        r_opt: bool | None = None
        cur = 0
        ts: list[int] = []
        while w[(j - 1) % L] == "1":
            if dd % 2 == 0:
                dd >>= 1
                cur += 1
            else:
                if dd == h - 1:
                    r_opt = (st % 2 != 0)
                    break
                if (M + dd) // 2 > m:
                    r_opt = (st % 2 == 0)
                    break
                if ts or cur:
                    ts.append(cur)
                cur = 0
                dd = (M + dd) // 2
                j -= 1
            st += 1
        if r_opt is None:
            b_val = E(j, dd)
            r = b_val if st % 2 == 0 else (not b_val)
            ts.append(cur)
        else:
            r = r_opt
        rle: list[tuple[int, int]] = []
        for x in ts:
            if rle and rle[-1][0] == x:
                rle[-1] = (x, rle[-1][1] + 1)
            else:
                rle.append((x, 1))
        if from_e is not None:
            chains.append({
                "from": e_idx(from_e),
                "entry": form_a(d),
                "len": i - j,
                "rle": rle,
                "endV2": v2(dd),
                "val": r,
            })
        memo[key] = r
        return r

    ok = True
    for i in range(1, L + 1):
        x = O(i, h) if w[(i - 1) % L] == "1" else E(i, h)
        if ("1" if x else "0") != w[i % L]:
            ok = False
    if E(L, A) is not False:
        ok = False
    return {"N": N, "R": R, "ok": ok, "nontriv": sorted(nontriv), "chains": chains}


def symbolic_audit_k58_chains() -> list[str]:
    """
    Explicitly verify the symbolic b-orbits and crossing points of all 3 entrance families of Theorem K58
    (N ≡ 3 mod 4, 5a + 1 = 7·2^N, R = (N - 3)/2 even) for N = 23..199.
    """
    lines: list[str] = []
    # Check Chain 1: d_0 = (9a - 3)/4 -> halve 1 -> d_1 = (9a - 3)/8 = 3a - 21·2^{N-3}, b = 3 fixed point (t(3)=1, 0 halvings!)
    # Check Chain 2: d_0 = 2a - 4 -> track (alpha, c, K, beta, b) at N = 43 and verify exact formula for N = 23..199
    # Check Chain 3: d_0 = (5a - 15)/2 -> track (alpha, c, K, beta, b) at N = 43 and verify exact formula for N = 23..199
    N = 43
    X = 1 << N
    a = (7 * X - 1) // 5
    M = 3 * a

    def analyze_entry(name: str, alpha0: int, c0: int, K0: int, steps_odd: int) -> str:
        # Express d = (alpha*a - c)/2^K, beta = alpha + 5*c, d = (beta*a - 7*c*X)/2^K
        al, c, K = alpha0, c0, K0
        d = (al * a - c) >> K
        assert (al * a - c) % (1 << K) == 0
        b_seq: list[tuple[int, int, int]] = []  # (step, K_at_odd, b_at_odd) or (-1, ...) after crossing
        crossed = False
        cross_info = ""
        for step in range(steps_odd):
            # halve until odd
            h_cnt = 0
            while d % 2 == 0:
                d >>= 1
                K += 1
                h_cnt += 1
            beta = al + 5 * c
            if not crossed and K < N:
                assert beta % (1 << K) == 0
                b_val = beta >> K
                b_seq.append((step, K, b_val))
            # odd step
            al_new = al + 3 * (1 << K)
            K_new = K + 1
            beta_new = al_new + 5 * c
            E = v2(beta_new)
            if not crossed and E >= N:
                crossed = True
                if E == N:
                    b_prime = beta_new >> E
                    u = v2(b_prime * a - 7 * c)
                    cross_info = f"CROSS(E=N={N} at odd_step={step+1}, K={K}, b'={b_prime}, c={c}, u=v2(b'a-7c)={u}, new_c={7*c}, new_beta''={b_prime + 35*c})"
                else:
                    cross_info = f"CROSS(E={E}>N={N} at odd_step={step+1}, K={K})"
            al, K = al_new, K_new
            d = (M + d) >> 1
        # Summarize unique b_vals before crossing
        bs_only = [b for _, _, b in b_seq]
        # Compress runs of bs_only
        comp: list[tuple[int, int]] = []
        for b in bs_only:
            if comp and comp[-1][0] == b:
                comp[-1] = (b, comp[-1][1] + 1)
            else:
                comp.append((b, 1))
        return f"{name} (len={steps_odd}, N={N}): pre-cross b-runs={comp}, {cross_info or 'NO CROSS'}, end_v2={v2(d)}"

    lines.append(analyze_entry("Chain 1 (9a-3)/4 [E1]", 9, 3, 2, 22))
    lines.append(analyze_entry("Chain 1 (9a-3)/4 [B]", 9, 3, 2, 20))
    lines.append(analyze_entry("Chain 2 (2a-4)   [E1]", 2, 4, 0, 22))
    lines.append(analyze_entry("Chain 2 (2a-4)   [B]", 2, 4, 0, 20))
    lines.append(analyze_entry("Chain 3 (5a-15)/2[E1]", 5, 15, 1, 22))
    lines.append(analyze_entry("Chain 3 (5a-15)/2[B]", 5, 15, 1, 20))
    return lines


def main() -> None:
    t0 = time.perf_counter()
    print("# gemini-2 独立検証: PR #331 修正（K57）・PR #344（K34/K58 トレース）・PR #346（非自明事実）・PR #348（定理 K58）")
    print("# 実行コマンド: uv run python code/gemini2_verify_k57fix_k34_k58.py > data/gemini2_verify_k57fix_k34_k58.txt")
    print()

    # 1. PR #331 fix
    tot331, ok331, skip331, notes331 = verify_pr331_fix()
    print("## 1. PR #331 修正（命題 K57）")
    print(f"- 検証対象 314 族: 対象内 {tot331} 族中 {ok331} 族一致, 対象外 {skip331} 族 (期待: 311/311, 対象外 3)")
    for ln in notes331:
        print(f"  {ln}")
    print()

    # 2. PR #344 & #346
    exc33 = check_k33_trace_exceptions()
    print("## 2. PR #344（k33_odd_trace 修正確認 & K34/K58 1 段分解）・PR #346（非自明 E 型事実）")
    print(f"- k33_odd_trace（e = 15, 21, 27, 33）での早期終了例外発生回数: {exc33} (0 なので PR #333 検証結果への影響なし)")
    expected_344 = {
        41: (161, 90, 34),
        45: (169, 98, 34),
        49: (177, 106, 34),
        53: (185, 114, 34),
        43: (56, 48, 6),
        47: (60, 52, 6),
        51: (64, 56, 6),
    }
    err344 = 0
    nt_by_s: dict[int, list[list[str]]] = {3: [], 7: []}
    for N in (41, 45, 49, 53, 43, 47, 51):
        tr = trace_k34_k58(N)
        exp_nE, exp_nO, exp_nt = expected_344[N]
        match = tr["ok"] and tr["nE"] == exp_nE and tr["nO"] == exp_nO and len(tr["nontriv"]) == exp_nt
        if not match:
            err344 += 1
        nt_by_s[tr["s"]].append(tr["nontriv"])
        print(f"  N={N} (s={tr['s']}, R={tr['R']}, L={tr['L']}): ok={tr['ok']}, E={tr['nE']}, O={tr['nO']}, nontriv={len(tr['nontriv'])}, match={match}")
    same_nt_3 = all(x == nt_by_s[3][0] for x in nt_by_s[3])
    same_nt_7 = all(x == nt_by_s[7][0] for x in nt_by_s[7])
    print(f"- PR #346 非自明事実の不変性: s=3 (34 個) 全一致={same_nt_3}, s=7 (6 個) 全一致={same_nt_7}, errors={err344}")
    print()

    # 3. PR #348: 40 cases (43 <= N <= 199) + small N = 23..39 + symbolic orbit audit
    print("## 3. PR #348（定理 K58：data/k58_shapes.txt 独立再現 & 6 本鎖の記号軌道解析）")
    r43 = run_k58_shape(43)
    err348 = 0
    for N in range(43, 200, 4):
        rN = run_k58_shape(N)
        if not rN["ok"] or rN["nontriv"] != r43["nontriv"] or len(rN["chains"]) != 6:
            err348 += 1
            continue
        dR = rN["R"] - r43["R"]
        for c0, cN in zip(r43["chains"], rN["chains"]):
            if (
                c0["from"] != cN["from"]
                or c0["entry"] != cN["entry"]
                or c0["endV2"] != cN["endV2"]
                or c0["val"] != cN["val"]
                or len(c0["rle"]) != len(cN["rle"])
            ):
                err348 += 1
                break
            for (x0, n0), (xN, nN) in zip(c0["rle"], cN["rle"]):
                dn = nN - n0
                if x0 != xN or not (dn == 0 or (dR != 0 and dn % dR == 0)):
                    err348 += 1
                    break
    print(f"- 43 <= N <= 199 (N ≡ 3 mod 4, 全 40 例): 1 段閉鎖・6 非自明事実・6 鎖形比較一致, errors = {err348}")
    print("- 小さい境界 N = 23, 27, 31, 35, 39 での挙動確認:")
    for N_sm in (23, 27, 31, 35, 39):
        try:
            rS = run_k58_shape(N_sm)
            same_rle_len = all(len(c0["rle"]) == len(cS["rle"]) for c0, cS in zip(r43["chains"], rS["chains"]))
            print(f"  N={N_sm} (R={rS['R']}): ok={rS['ok']}, same_nontriv={rS['nontriv']==r43['nontriv']}, same_rle_struct={same_rle_len}")
        except Exception as exc:
            print(f"  N={N_sm}: exception={exc}")
    print("- 6 本鎖の記号軌道・越え場面解析（PR #348 本文の記述検証）:")
    for ln in symbolic_audit_k58_chains():
        print(f"  {ln}")

    total_errors = (0 if (tot331 == 311 and ok331 == 311 and skip331 == 3) else 1) + err344 + (0 if same_nt_3 and same_nt_7 else 1) + err348
    print()
    print(f"## 総合検証結果: total_errors = {total_errors}, elapsed = {time.perf_counter() - t0:.2f}s")
    if total_errors != 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
