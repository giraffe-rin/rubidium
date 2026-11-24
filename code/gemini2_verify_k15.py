"""
gemini-2 による独立な Python 実装を用いた定理 K15・系 K15.1（2 <= k <= 16 の記号証明書）の検証。

何を計算するか:
1. PR #42（notes/2026-11-23-claude-1-proof-k12-general.md）の補題 B・C・D および
   「証明書から定理へ」の仕様のみに基づき、w に依存しない記号証明書を
   2 <= k <= 16 のすべてについて独立に再計算し、以下を全件検証する：
   - 循環依存なし（DAG）
   - すべての事実が 3 つの形 W(c), H(c), Q(b) と補題 B の範囲内で閉じる
   - 各剰余 r (0 <= r <= 2k) で h = H(0) の所属が 1(10)^k 型と一致
   - r = 0 の全事実が定理 K3（W(c): v2(c) 偶数, 奇数 H(c)/Q(b): True, 偶数 H(c) なし）と一致
2. PROBLEM.md の定義のみから書いた全探索 DP (solve_count_dp) で
   k = 2 (m = 73) および k = 3 (m = 297) の 1(10)^k 型と証明書の全事実を直接検証。
3. 査読済み定理 K8 の独立実装で、k = 2..6 の最小例 (w = 7: m = 73, 297, 1193, 4777, 19113)
   の 3 周期分について証明書の全事実と照合。

実行方法:
  python code/gemini2_verify_k15.py
結果を標準出力と data/gemini2_verify_k15.txt に保存する。
"""

from __future__ import annotations

import time
from pathlib import Path


TAG_W = 0
TAG_H = 1
TAG_Q = 2
SHIFT_VAL = 38  # 2^38 > 2.7e11 >> A(k=16) ~ 2.86e9
MASK_VAL = (1 << SHIFT_VAL) - 1


def v2(n: int) -> int:
    return (n & -n).bit_length() - 1


def solve_count_dp(m: int, max_r: int) -> list[list[bool]]:
    is_p: list[list[bool]] = [[False] * (m + 1) for _ in range(max_r + 1)]
    is_p[0] = [True] * (m + 1)
    for r in range(1, max_r + 1):
        limit = m if r >= m else r
        p_dest = [False] * (limit + 1)
        total_p = 0
        for k in range(1, limit + 1):
            if is_p[r - k][k]:
                p_dest[k] = True
                total_p += 1
        row = is_p[r]
        for p in range(m + 1):
            legal_p = total_p - (1 if (1 <= p <= limit and p_dest[p]) else 0)
            row[p] = (legal_p == 0)
    return is_p


def run_k8_blocks(m: int, n_blocks: int) -> tuple[list[set[int]], list[int]]:
    h = (m + 1) // 2
    S_list: list[set[int]] = []
    g_list: list[int] = []
    for j in range(n_blocks):
        S_j: set[int] = set()
        for d in range(1, m + 1):
            blocked = False
            if d % 2 == 0 and (d // 2) in S_j:
                blocked = True
            if not blocked and j >= 1:
                gp = g_list[j - 1]
                if (gp + d) % 2 == 0:
                    e = (gp + d) // 2
                    if e <= m and e in S_list[j - 1]:
                        blocked = True
            if not blocked and j >= 1:
                if g_list[j - 1] == m + 2 and d == h - 1:
                    blocked = True
            if not blocked:
                S_j.add(d)
        g_j = (m + 2) if (h in S_j) else (m + 1)
        S_list.append(S_j)
        g_list.append(g_j)
    return S_list, g_list


def build_and_verify_certificate(k: int) -> tuple[bool, int, dict[int, int], str]:
    L = 2 * k + 1
    pow4 = 1 << (2 * k)
    B = (pow4 - 1) // 3
    A = 2 * B

    # Precompute E-type and previous remainder arrays
    is_e = [(r == 0) or (r >= 3 and (r & 1) == 1) for r in range(L)]
    prev_r = [(r - 1) % L for r in range(L)]

    # memo[key] = -1 (visiting), 0 (False), 1 (True)
    memo: dict[int, int] = {}

    def pack(r: int, tag: int, val: int) -> int:
        return (((r << 2) | tag) << SHIFT_VAL) | val

    def evaluate(start_r: int, start_tag: int, start_val: int) -> int:
        start_key = pack(start_r, start_tag, start_val)
        got = memo.get(start_key)
        if got is not None:
            if got == -1:
                raise RuntimeError(f"cycle at {(start_r, start_tag, start_val)}")
            return got

        # Iterative DFS stack: (state, key, r, tag, val, aux_key)
        # state 0: enter node
        # state 1: E-type W(c even) after checking (i) W(c/2)
        # state 2: E-type W(c even) after checking (ii) H(c/2)
        # state 3: O-type negate single child
        stack: list[tuple[int, int, int, int, int, int]] = [
            (0, start_key, start_r, start_tag, start_val, 0)
        ]

        while stack:
            st, key, r, tag, val, aux = stack.pop()
            if st == 0:
                cur = memo.get(key)
                if cur is not None:
                    if cur == -1:
                        raise RuntimeError(f"cycle detected at r={r} tag={tag} val={val}")
                    continue
                memo[key] = -1

                # Bounds check (Lemma B)
                if tag == TAG_W:
                    if val < 1 or val > A:
                        raise RuntimeError(f"W out of range: {val}")
                    odd = val & 1
                elif tag == TAG_H:
                    if val < 0 or val > B:
                        raise RuntimeError(f"H out of range: {val}")
                    odd = (val + 1) & 1
                else:  # TAG_Q
                    if val < 0 or (2 * val + 1) > A:
                        raise RuntimeError(f"Q out of range: {val}")
                    odd = (val + 1) & 1

                if is_e[r]:
                    if odd:
                        memo[key] = 1
                    else:
                        if tag != TAG_W:
                            raise RuntimeError(f"even non-W in E-type: r={r} tag={tag} val={val}")
                        c_half = val >> 1
                        k_i = pack(r, TAG_W, c_half)
                        res_i = memo.get(k_i)
                        if res_i is not None and res_i != -1:
                            if res_i == 1:
                                memo[key] = 0
                            else:
                                pr = prev_r[r]
                                k_ii = pack(pr, TAG_H, c_half)
                                res_ii = memo.get(k_ii)
                                if res_ii is not None and res_ii != -1:
                                    memo[key] = 0 if res_ii == 1 else 1
                                else:
                                    stack.append((2, key, r, tag, val, k_ii))
                                    stack.append((0, k_ii, pr, TAG_H, c_half, 0))
                        else:
                            stack.append((1, key, r, tag, val, k_i))
                            stack.append((0, k_i, r, TAG_W, c_half, 0))
                else:
                    # O-type
                    if tag == TAG_Q:
                        raise RuntimeError(f"Q in O-type: r={r} val={val}")
                    if not odd:
                        if tag != TAG_W:
                            raise RuntimeError(f"even H in O-type: r={r} val={val}")
                        c_half = val >> 1
                        k_c = pack(r, TAG_W, c_half)
                        res_c = memo.get(k_c)
                        if res_c is not None and res_c != -1:
                            memo[key] = 0 if res_c == 1 else 1
                        else:
                            stack.append((3, key, r, tag, val, k_c))
                            stack.append((0, k_c, r, TAG_W, c_half, 0))
                    else:
                        pr = prev_r[r]
                        if tag == TAG_W:
                            b = (val - 1) >> 1
                            k_c = pack(pr, TAG_Q, b)
                            res_c = memo.get(k_c)
                            if res_c is not None and res_c != -1:
                                memo[key] = 0 if res_c == 1 else 1
                            else:
                                stack.append((3, key, r, tag, val, k_c))
                                stack.append((0, k_c, pr, TAG_Q, b, 0))
                        else:  # TAG_H, val is even
                            ec = (pow4 + val) >> 1
                            if ec > A:
                                memo[key] = 1
                            else:
                                k_c = pack(pr, TAG_W, ec)
                                res_c = memo.get(k_c)
                                if res_c is not None and res_c != -1:
                                    memo[key] = 0 if res_c == 1 else 1
                                else:
                                    stack.append((3, key, r, tag, val, k_c))
                                    stack.append((0, k_c, pr, TAG_W, ec, 0))

            elif st == 1:
                res_i = memo[aux]
                if res_i == 1:
                    memo[key] = 0
                else:
                    c_half = val >> 1
                    pr = prev_r[r]
                    k_ii = pack(pr, TAG_H, c_half)
                    res_ii = memo.get(k_ii)
                    if res_ii is not None and res_ii != -1:
                        memo[key] = 0 if res_ii == 1 else 1
                    else:
                        stack.append((2, key, r, tag, val, k_ii))
                        stack.append((0, k_ii, pr, TAG_H, c_half, 0))

            elif st == 2:
                res_ii = memo[aux]
                memo[key] = 0 if res_ii == 1 else 1

            elif st == 3:
                res_c = memo[aux]
                memo[key] = 0 if res_c == 1 else 1

        return memo[start_key]

    try:
        # 1. Evaluate h = H(0) for every residue r = 0..2k and verify 1(10)^k pattern
        for r in range(L):
            want = 1 if (r == 0 or (r & 1) == 1) else 0
            got = evaluate(r, TAG_H, 0)
            if got != want:
                return False, len(memo), memo, f"h mismatch at r={r}: got={got}, want={want}"

        # 2. Verify all r = 0 facts against Theorem K3
        r0_prefix_limit = 4 << SHIFT_VAL
        for key, res in memo.items():
            if res not in (0, 1):
                return False, len(memo), memo, f"unresolved key {key}"
            if key < r0_prefix_limit:
                tag = (key >> SHIFT_VAL) & 3
                val = key & MASK_VAL
                if tag == TAG_W:
                    want_k3 = 1 if (v2(val) % 2 == 0) else 0
                    if res != want_k3:
                        return False, len(memo), memo, f"K3 W({val}) fail: got={res}, want={want_k3}"
                elif tag == TAG_H:
                    if (val & 1) != 0 or res != 1:
                        return False, len(memo), memo, f"K3 H({val}) fail: res={res}"
                else:  # TAG_Q
                    if (val & 1) != 0 or (2 * val + 1) > A or res != 1:
                        return False, len(memo), memo, f"K3 Q({val}) fail: res={res}"

    except RuntimeError as exc:
        return False, len(memo), memo, str(exc)

    return True, len(memo), memo, "OK"


def check_facts_against_blocks(
    k: int, w: int, memo: dict[int, int], S_list: list[set[int]], g_list: list[int]
) -> list[str]:
    L = 2 * k + 1
    h = ((1 << (2 * k)) * w - 1) // 3
    m = 2 * h - 1
    Qk = (m + 2 + w) // 2
    errs: list[str] = []
    for j, (S_j, g_j) in enumerate(zip(S_list, g_list)):
        r = j % L
        want_g = (m + 2) if (r == 0 or (r & 1) == 1) else (m + 1)
        if g_j != want_g:
            errs.append(f"gap mismatch k={k} w={w} j={j}")
            break
    for key, res in memo.items():
        r = key >> (SHIFT_VAL + 2)
        tag = (key >> SHIFT_VAL) & 3
        val = key & MASK_VAL
        if tag == TAG_W:
            d = val * w
        elif tag == TAG_H:
            d = h + val * w
        else:
            d = Qk + val * w
        want_in = (res == 1)
        for j in range(r, len(S_list), L):
            if (d in S_list[j]) != want_in:
                errs.append(f"fact mismatch k={k} w={w} j={j} d={d} want={want_in}")
                return errs
    return errs


def main() -> None:
    t0 = time.perf_counter()
    lines: list[str] = []
    lines.append("=== gemini-2 独立検証: 定理 K15・系 K15.1（2 <= k <= 16 の記号証明書） ===")

    cert_errs: list[str] = []
    saved_small: dict[int, dict[int, int]] = {}
    lines.append("[1] 記号証明書の独立再計算 (2 <= k <= 16):")
    for k in range(2, 17):
        tk0 = time.perf_counter()
        ok, nfacts, memo, msg = build_and_verify_certificate(k)
        dt = time.perf_counter() - tk0
        lines.append(f"  k={k:2d}: ok={ok}, facts={nfacts:>9,d}, time={dt:.2f}s ({msg})")
        if not ok:
            cert_errs.append(f"k={k}: {msg}")
        if k <= 6:
            saved_small[k] = memo
        else:
            del memo  # free memory for large k

    # [2] Direct brute-force DP check for k = 2 (m = 73) and k = 3 (m = 297)
    bf_errs: list[str] = []
    bf_states = 0
    for k, w, max_r in [(2, 7, 1500), (3, 7, 3000)]:
        h = ((1 << (2 * k)) * w - 1) // 3
        m = 2 * h - 1
        tab = solve_count_dp(m, max_r)
        bf_states += (max_r + 1) * (m + 1)
        a_rows = [r for r in range(max_r + 1) if all(tab[r])]
        S_list = [
            {d for d in range(1, m + 1) if tab[a_rows[j] + d][d]}
            for j in range(len(a_rows) - 1)
        ]
        g_list = [a_rows[j + 1] - a_rows[j] for j in range(len(a_rows) - 1)]
        bf_errs.extend(check_facts_against_blocks(k, w, saved_small[k], S_list, g_list))

    # [3] K8 cross-check for k = 2..6 with w = 7 (3 periods each)
    k8_errs: list[str] = []
    for k in range(2, 7):
        w = 7
        h = ((1 << (2 * k)) * w - 1) // 3
        m = 2 * h - 1
        L = 2 * k + 1
        S_list, g_list = run_k8_blocks(m, 3 * L)
        k8_errs.extend(check_facts_against_blocks(k, w, saved_small[k], S_list, g_list))

    elapsed = time.perf_counter() - t0
    lines.append(f"[1] 記号証明書エラー: {len(cert_errs)} 件")
    lines.append(f"[2] 全探索検証 (k=2 m=73, k=3 m=297; 計 {bf_states:,} 局面): 反例 {len(bf_errs)} 件")
    lines.append(f"[3] 査読済み K8 照合 (k=2..6, w=7, 各 3 周期): 反例 {len(k8_errs)} 件")
    if cert_errs or bf_errs or k8_errs:
        lines.append("ERRORS:")
        lines.extend((cert_errs + bf_errs + k8_errs)[:20])
    lines.append(f"所要時間: {elapsed:.2f} 秒")

    text = "\n".join(lines) + "\n"
    print(text, end="")
    out = Path(__file__).resolve().parent.parent / "data" / "gemini2_verify_k15.txt"
    out.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
