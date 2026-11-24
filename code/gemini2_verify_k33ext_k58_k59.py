"""
gemini2_verify_k33ext_k58_k59.py — PR #334（K33 奇数 e <= 399）・PR #336（K34/K58 N <= 401）・PR #338（補題 K59.1・定理 K59）の Python 独立検証

何を計算するか:
  1. PR #334（予想 K33 奇数 e の型確定拡大: 9 <= e <= 399 全 196 個）:
     - BigInt 相当の Python 多倍長整数で prove3(..., k33d=True) を独立実装し、全 196 個の奇数 e を並列検証する。
     - すべて確定し、仮定集合 A がちょうど {6·2^e + 8: False} の 1 元であることを確認し、e = 199, 399 等の事実数を出力する。
  2. PR #336（定理 K47 族 v=3, rho=2 の奇数 N: 予想 K34・K58, 21 <= N <= 401 全 191 個）:
     - 予想 K34 の式 m = 8(36·16^k - 1)/5 - 1 が 5a + 1 = 3·2^{4k+5}, m = 3a - 2 に恒等的に一致することを確認する。
     - 21 <= N <= 401 の全 191 個の奇数 N（N ≡ 1 mod 4: 96 個、N ≡ 3 mod 4: 95 個）を Python 独立実装の prove3(..., k33d=False) で並列検証する。
     - 小さい境界 N = 15, 19（K58）も確認する。
  3. PR #338（補題 K59.1・定理 K59: 9 <= N <= 401 全 197 個 + 鎖の越え場面の直接追跡）:
     - 9 <= N <= 401 の全 197 個の奇数 N（および境界 N = 5, 7）について K8 遅延計算で先頭 m+2 連を直接計算し、
       s = 3 で 2R、s = 7 で R + 2、かつ v2(a - s) が 4 / 2 に一致することを並列検証する。
     - 代表例（N = 9, 11, 41, 43, 45, 99, 101）について、h の鎖の越え場面（E = N）から終点までを直接追跡し、
       d' = (a - s)/2^u、d_end = 2a - 9（s = 3, i = 2R）、d'_2 = (13a - 7)/16（s = 7, i = R + 2）、段数 2i + 5 / 2R + 5 / 2R + 7 を確認する。

実行方法（リポジトリのルートで）:
  uv run python code/gemini2_verify_k33ext_k58_k59.py > data/gemini2_verify_k33ext_k58_k59.txt
"""
from __future__ import annotations

import concurrent.futures
import sys
import time

sys.setrecursionlimit(300000)


def v2(x: int) -> int:
    if x < 0:
        x = -x
    return (x & -x).bit_length() - 1


def prove3_big(
    m: int,
    pre: str,
    w: str,
    k33d: bool = False,
    max_rounds: int = 20000,
    max_facts: int = 20000000,
) -> tuple[bool, dict[int, bool], int]:
    """Independent Python arbitrary-precision implementation of prove3."""
    p = len(pre)
    L = len(w)
    v = v2(m + 1)
    h = (m + 1) // 2
    s = 0
    while s < L and w[L - 1 - s] == "0":
        s += 1

    def word(i: int) -> str:
        return pre[i] if i < p else w[(i - p) % L]

    g0 = "1" if (v2(h) % 2 == 0) else "0"
    if g0 != word(0):
        return (False, {}, 0)
    b = p + L
    gap_abs = [m + 2 if word(j) == "1" else m + 1 for j in range(b + L + 1)]
    base: dict[tuple[int, int], bool] = {}
    over = False

    def T(j: int, d: int) -> bool:
        nonlocal over
        if over:
            return False
        key = (j, d)
        res = base.get(key)
        if res is not None:
            return res
        if len(base) > max_facts:
            over = True
            return False
        if j == 0:
            r = (v2(d) & 1) == 0
        else:
            if (d & 1) == 0 and T(j, d >> 1):
                r = False
            else:
                if over:
                    return False
                g = gap_abs[j - 1]
                sm = g + d
                if (sm & 1) == 0 and (sm >> 1) <= m and T(j - 1, sm >> 1):
                    r = False
                elif over:
                    return False
                elif g == m + 2 and d == h - 1:
                    r = False
                else:
                    r = True
        if over:
            return False
        base[key] = r
        return r

    for j in range(1, b + 1):
        x = T(j, h)
        if over:
            return (False, {}, 0)
        if ("1" if x else "0") != word(j):
            return (False, {}, 0)

    bound = min(2 * s - 1, v - 1) if s > 0 else -1
    use_g = s > 0
    A: dict[int, bool] = {}

    for _ in range(max_rounds):
        memo: dict[tuple[int, int], bool] = {}
        unknown = -1
        too_many = False

        def S(i: int, d: int) -> bool:
            nonlocal unknown, too_many
            if unknown != -1 or too_many:
                return False
            key = (i, d)
            res = memo.get(key)
            if res is not None:
                return res
            if len(memo) > max_facts:
                too_many = True
                return False
            if i == 0:
                t = v2(d)
                if use_g and t == 0:
                    r = True
                elif use_g and k33d and t == 1:
                    r = False
                elif use_g and t <= bound:
                    r = (t & 1) == 0
                elif d in A:
                    r = A[d]
                else:
                    unknown = d
                    return False
            else:
                if (d & 1) == 0 and S(i, d >> 1):
                    r = False
                else:
                    if unknown != -1 or too_many:
                        return False
                    g = gap_abs[b + i - 1]
                    sm = g + d
                    if (sm & 1) == 0 and (sm >> 1) <= m and S(i - 1, sm >> 1):
                        r = False
                    elif unknown != -1 or too_many:
                        return False
                    elif g == m + 2 and d == h - 1:
                        r = False
                    else:
                        r = True
            if unknown != -1 or too_many:
                return False
            memo[key] = r
            return r

        ok1 = True
        for i in range(1, L + 1):
            x = S(i, h)
            if unknown != -1 or too_many:
                break
            if ("1" if x else "0") != w[i % L]:
                ok1 = False
                break
        if too_many:
            return (False, dict(A), 0)
        if unknown != -1:
            A[unknown] = T(b, unknown)
            if over:
                return (False, dict(A), 0)
            continue
        if not ok1:
            return (False, dict(A), 0)
        for d_val, expected in list(A.items()):
            got = S(L, d_val)
            if unknown != -1 or too_many:
                break
            if got != expected:
                return (False, dict(A), 0)
        if too_many:
            return (False, dict(A), 0)
        if unknown != -1:
            A[unknown] = T(b, unknown)
            if over:
                return (False, dict(A), 0)
            continue
        return (True, dict(A), len(memo) + len(base))
    return (False, dict(A), 0)


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
# Workers
# ---------------------------------------------------------------------------
def worker_pr334(e: int) -> tuple[int, bool, bool, int, int]:
    X = 1 << e
    m = 9 * X + 1
    w = "1" * (e - 1) + "0" + "1" * ((e - 1) // 2) + "0"
    ok, A, facts = prove3_big(m, "", w, k33d=True)
    only8 = ok and (A == {6 * X + 8: False})
    return (e, ok, only8, len(str(m)), facts)


def worker_pr336(N: int) -> tuple[int, int, bool, int]:
    s = 3 if (N % 4 == 1) else 7
    X = 1 << N
    assert (s * X - 1) % 5 == 0
    a = (s * X - 1) // 5
    m = 3 * a - 2
    R = (N - 3) // 2
    if N % 4 == 1:
        k = (N - 5) // 4
        m_k34 = 8 * (36 * (16 ** k) - 1) // 5 - 1
        assert m == m_k34
        w = "1" * (2 * R) + "0" + ("1" * R + "00") * 2
    else:
        w = "1" * (R + 2) + "0" + "1" * R + "0"
    ok, A, _ = prove3_big(m, "", w, k33d=False)
    return (N, s, ok, len(A))


def worker_pr338(N: int) -> tuple[int, int, int, int, int, bool]:
    s = 3 if (N % 4 == 1) else 7
    X = 1 << N
    a = (s * X - 1) // 5
    m = 3 * a - 2
    R = (N - 3) // 2
    want = 2 * R if s == 3 else R + 2
    g = gaps_lazy_big(m, want + 3)
    run = g.index(0)
    u = v2(a - s)
    good = (run == want) and (u == (4 if s == 3 else 2))
    return (N, s, R, run, u, good)


def trace_k59_crossing(N: int) -> tuple[bool, str]:
    """Explicitly trace the h-chain crossing E = N and verify Lemma K59.1 & Theorem K59 formulas."""
    s = 3 if (N % 4 == 1) else 7
    X = 1 << N
    a = (s * X - 1) // 5
    m = 3 * a - 2
    M = 3 * a
    h = (m + 1) // 2
    R = (N - 3) // 2
    u = 4 if s == 3 else 2
    stop_i = 2 * R if s == 3 else R + 2

    # Trace block stop_i down to block 0 (assuming g_0..g_{stop_i-1} = m+2)
    d = h
    steps = 0
    odd_pts: list[int] = []
    for blk in range(stop_i, 0, -1):
        while d % 2 == 0:
            d >>= 1
            steps += 1
        odd_pts.append(d)
        if not (0 < d <= 3 * a - 4 and d != h - 1):
            return (False, f"N={N}: chain condition failed at blk={blk}")
        d = (M + d) // 2
        steps += 1

    # Check the crossing point (odd_pts[R] is d' = (a - s)/2^u)
    d_prime_exp = (a - s) // (1 << u)
    if odd_pts[R] != d_prime_exp:
        return (False, f"N={N}: d' mismatch")

    if s == 3:
        # At i = 2R: d_end == 2a - 9, steps == 2*stop_i + 5
        if d != 2 * a - 9 or steps != 2 * stop_i + 5:
            return (False, f"N={N} (s=3): d_end or steps mismatch")
        # Also verify odd_pts[R + j] == a - 9*2^{N - (2j + 4)} for j = 0..R-1
        for j in range(R):
            K_p = 2 * j + 4
            if odd_pts[R + j] != a - 9 * (1 << (N - K_p)):
                return (False, f"N={N} (s=3): second chain point j={j} mismatch")
        return (True, f"N={N} (s=3, R={R}): d'=(a-3)/16 OK, d_end=2a-9 OK, steps={steps}=4R+5 OK")
    else:
        # At i = R + 2: odd_pts[R] == (a-7)/4, odd_pts[R+1] == (13a-7)/16, v2(d_end) == 0, steps == 2R + 7
        if odd_pts[R + 1] != (13 * a - 7) // 16 or (d % 2 != 1) or steps != 2 * R + 7:
            return (False, f"N={N} (s=7): second chain or steps mismatch")
        return (True, f"N={N} (s=7, R={R}): d'=(a-7)/4 OK, d'_2=(13a-7)/16 OK, d_end odd OK, steps={steps}=2R+7 OK")


def main() -> None:
    t0 = time.perf_counter()
    print("# gemini-2 独立検証: PR #334（K33 e <= 399）・PR #336（K34/K58 N <= 401）・PR #338（補題 K59.1・定理 K59）")
    print("# 実行コマンド: uv run python code/gemini2_verify_k33ext_k58_k59.py > data/gemini2_verify_k33ext_k58_k59.txt")
    print()

    # 1. PR #334: 9 <= e <= 399 odd (196 cases)
    t1 = time.perf_counter()
    es = list(range(9, 400, 2))
    with concurrent.futures.ProcessPoolExecutor(max_workers=10) as ex:
        res334 = list(ex.map(worker_pr334, es))
    ok334 = sum(1 for _, ok, _, _, _ in res334 if ok)
    only8_334 = sum(1 for _, _, o8, _, _ in res334 if o8)
    by_e = {e: (ok, o8, dig, facts) for e, ok, o8, dig, facts in res334}
    print(f"## 1. PR #334（予想 K33 奇数 e: 9 <= e <= 399, 全 {len(es)} 個）[{time.perf_counter() - t1:.2f}s]")
    print(f"- 確定: {ok334}/{len(es)}, A = {{6X + 8: False}} 単独: {only8_334}/{len(es)}")
    for e_sample in (9, 199, 399):
        ok, o8, dig, facts = by_e[e_sample]
        print(f"  e = {e_sample}: digits = {dig}, ok = {ok}, only_6X+8 = {o8}, facts = {facts}")
    print()

    # 2. PR #336: 21 <= N <= 401 odd (191 cases) + boundary N = 15, 19
    t2 = time.perf_counter()
    Ns336 = list(range(21, 402, 2))
    with concurrent.futures.ProcessPoolExecutor(max_workers=10) as ex:
        res336 = list(ex.map(worker_pr336, Ns336))
    ok336_k34 = sum(1 for N, s, ok, _ in res336 if N % 4 == 1 and ok)
    tot336_k34 = sum(1 for N, _, _, _ in res336 if N % 4 == 1)
    ok336_k58 = sum(1 for N, s, ok, _ in res336 if N % 4 == 3 and ok)
    tot336_k58 = sum(1 for N, _, _, _ in res336 if N % 4 == 3)
    a_sizes_k34 = sorted({a_sz for N, _, _, a_sz in res336 if N % 4 == 1})
    a_sizes_k58 = sorted({a_sz for N, _, _, a_sz in res336 if N % 4 == 3})
    print(f"## 2. PR #336（K47 奇数 N: 予想 K34・K58, 21 <= N <= 401, 全 {len(Ns336)} 個）[{time.perf_counter() - t2:.2f}s]")
    print(f"- N ≡ 1 (mod 4) [予想 K34, s=3, 4 <= k <= 99]: 確定 {ok336_k34}/{tot336_k34}, |A| の集合 = {a_sizes_k34}")
    print(f"- N ≡ 3 (mod 4) [予想 K58, s=7, 23 <= N <= 399]: 確定 {ok336_k58}/{tot336_k58}, |A| の集合 = {a_sizes_k58}")
    for N_sm in (15, 19):
        _, s_sm, ok_sm, a_sm = worker_pr336(N_sm)
        print(f"  小さい境界 N = {N_sm} (s={s_sm}, K58): prove3 ok = {ok_sm}, |A| = {a_sm}")
    print()

    # 3. PR #338: 9 <= N <= 401 odd (197 cases) + crossing trace + boundary N = 5, 7
    t3 = time.perf_counter()
    Ns338 = list(range(9, 402, 2))
    with concurrent.futures.ProcessPoolExecutor(max_workers=10) as ex:
        res338 = list(ex.map(worker_pr338, Ns338))
    ok338 = sum(1 for _, _, _, _, _, g in res338 if g)
    print(f"## 3. PR #338（補題 K59.1・定理 K59: 9 <= N <= 401, 全 {len(Ns338)} 個）[{time.perf_counter() - t3:.2f}s]")
    print(f"- 先頭連 & v2(a - s) 一致: {ok338}/{len(Ns338)}")
    for N_sm in (5, 7):
        _, s_sm, R_sm, run_sm, u_sm, good_sm = worker_pr338(N_sm)
        print(f"  小さい境界 N = {N_sm} (s={s_sm}, R={R_sm}): run = {run_sm}, v2(a-s) = {u_sm}, K59一致 = {good_sm}")

    trace_err = 0
    print("- 越え場面（E = N）の記号式・段数の直接追跡:")
    for N_tr in (9, 11, 41, 43, 45, 99, 101):
        ok_tr, msg_tr = trace_k59_crossing(N_tr)
        if not ok_tr:
            trace_err += 1
        print(f"  [{'OK' if ok_tr else 'NG'}] {msg_tr}")

    total_errors = (len(es) - ok334) + (len(es) - only8_334) + (tot336_k34 - ok336_k34) + (tot336_k58 - ok336_k58) + (len(Ns338) - ok338) + trace_err
    print()
    print(f"## 総合検証結果: total_errors = {total_errors}, total_elapsed = {time.perf_counter() - t0:.2f}s")
    if total_errors != 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
