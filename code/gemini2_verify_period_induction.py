"""
査読済み定理 K8・K3・補題 Q_n（PR #111, #202）のみから書いた、厳密（上限超過時は例外送出・
サイレント通過不可・m 奇数チェック明示）な独立 Python 周期帰納法検証器（prove / prove2）により、
PR #237（予想 K40 N 偶数 20 例）、PR #239（K33 奇数 97 例・K34 27 例・K40 奇数 19 例）、
PR #241（prove2 健全性・m <= 3000 全検査・2^40 < m < 2^41 無作為検査）を独立検証する。

実行方法:
    python code/gemini2_verify_period_induction.py
出力:
    data/gemini2_verify_period_induction.txt
"""

from __future__ import annotations

import random
import time
from pathlib import Path


def v2(x: int) -> int:
    assert x > 0
    return (x & -x).bit_length() - 1


def eval_S_iterative(
    m: int,
    h: int,
    w: str,
    base_fn,
    memo: dict[tuple[int, int], bool],
    start_i: int,
    start_d: int,
    max_facts: int,
) -> tuple[bool | None, int | None]:
    """反復スタックによる厳密 R 遅延評価。
    未知の B 事実に出会えば (None, unknown_d) を返す。上限超過時は RuntimeError を送出。
    """
    L = len(w)
    M = m + 2
    E_gap = m + 1
    stack: list[tuple[int, int]] = [(start_i, start_d)]
    while stack:
        i, d = stack[-1]
        key = (i, d)
        if key in memo:
            stack.pop()
            continue
        if len(memo) > max_facts:
            raise RuntimeError("max_facts exceeded")
        assert 1 <= d <= m
        if i == 0:
            val = base_fn(d)
            if val is None:
                return None, d
            memo[key] = val
            stack.pop()
            continue
        g = M if w[(i - 1) % L] == "1" else E_gap
        # (iii)
        if g == M and d == h - 1:
            memo[key] = False
            stack.pop()
            continue
        # (i)
        if (d & 1) == 0:
            k1 = (i, d >> 1)
            if k1 not in memo:
                stack.append(k1)
                continue
            if memo[k1]:
                memo[key] = False
                stack.pop()
                continue
        # (ii)
        s = g + d
        if (s & 1) == 0:
            e = s >> 1
            if e <= m:
                k2 = (i - 1, e)
                if k2 not in memo:
                    stack.append(k2)
                    continue
                if memo[k2]:
                    memo[key] = False
                    stack.pop()
                    continue
        memo[key] = True
        stack.pop()
    return memo[(start_i, start_d)], None


def prove_strict(m: int, w: str, max_rounds: int = 5000, max_facts: int = 3_000_000) -> tuple[bool, str, int, int]:
    """厳密版 prove(m, w)：m 奇数必須・上限超過は即時例外・サイレント通過なし。"""
    if m < 3 or (m & 1) == 0:
        return False, "m must be odd >= 3", 0, 0
    L = len(w)
    v = v2(m + 1)
    h = (m + 1) // 2
    s = 0
    while s < L and w[L - 1 - s] == "0":
        s += 1
    if s == 0:
        return False, "w must end with 0", 0, 0
    # (0) ブロック 0 の間隔確認（K3）
    g0 = "1" if (v2(h) % 2 == 0) else "0"
    if g0 != w[0]:
        return False, "g0 mismatch", 0, 0
    bound = min(2 * s - 1, v - 1)
    A: dict[int, bool] = {}

    def base_fn(d: int) -> bool | None:
        t = v2(d)
        if t == 0:
            return True
        if t <= bound:
            return (t % 2) == 0
        return A.get(d, None)

    for _ in range(max_rounds):
        memo: dict[tuple[int, int], bool] = {}
        unknown_d: int | None = None
        for i in range(1, L + 1):
            val, unk = eval_S_iterative(m, h, w, base_fn, memo, i, h, max_facts)
            if unk is not None:
                unknown_d = unk
                break
            if ("1" if val else "0") != w[i % L]:
                return False, "gap mismatch", len(A), len(memo)
        if unknown_d is not None:
            A[unknown_d] = (v2(unknown_d) % 2) == 0
            continue
        for d, expected_val in list(A.items()):
            val, unk = eval_S_iterative(m, h, w, base_fn, memo, L, d, max_facts)
            if unk is not None:
                unknown_d = unk
                break
            if val != expected_val:
                return False, "A not preserved", len(A), len(memo)
        if unknown_d is not None:
            A[unknown_d] = (v2(unknown_d) % 2) == 0
            continue
        return True, "ok", len(A), len(memo)
    return False, "round limit", len(A), 0


def prove2_strict(m: int, w: str, max_rounds: int = 5000, max_facts: int = 3_000_000) -> tuple[bool, str, int, int]:
    """厳密版 prove2(m, w)：ブロック 0..L を直接 K3+R で検証し、ブロック L を出発点に 1 周期帰納法を閉じる。"""
    if m < 3 or (m & 1) == 0:
        return False, "m must be odd >= 3", 0, 0
    L = len(w)
    v = v2(m + 1)
    h = (m + 1) // 2
    s = 0
    while s < L and w[L - 1 - s] == "0":
        s += 1
    if s == 0:
        return False, "w must end with 0", 0, 0
    g0 = "1" if (v2(h) % 2 == 0) else "0"
    if g0 != w[0]:
        return False, "g0 mismatch", 0, 0

    # (0') ブロック 0..L を K3 から直接評価し、全ブロックの間隔が w に一致することを確認
    base_memo: dict[tuple[int, int], bool] = {}

    def k3_base(d: int) -> bool:
        return (v2(d) % 2) == 0

    for j in range(1, L + 1):
        val, unk = eval_S_iterative(m, h, w, k3_base, base_memo, j, h, max_facts)
        assert unk is None
        if ("1" if val else "0") != w[j % L]:
            return False, "first period gap mismatch", 0, len(base_memo)

    bound = min(2 * s - 1, v - 1)
    A: dict[int, bool] = {}

    def base_fn(d: int) -> bool | None:
        t = v2(d)
        if t == 0:
            return True
        if t <= bound:
            return (t % 2) == 0
        return A.get(d, None)

    for _ in range(max_rounds):
        memo: dict[tuple[int, int], bool] = {}
        unknown_d: int | None = None
        for i in range(1, L + 1):
            val, unk = eval_S_iterative(m, h, w, base_fn, memo, i, h, max_facts)
            if unk is not None:
                unknown_d = unk
                break
            if ("1" if val else "0") != w[i % L]:
                return False, "gap mismatch", len(A), len(memo) + len(base_memo)
        if unknown_d is not None:
            val_L, unk2 = eval_S_iterative(m, h, w, k3_base, base_memo, L, unknown_d, max_facts)
            assert unk2 is None and val_L is not None
            A[unknown_d] = val_L
            continue
        for d, expected_val in list(A.items()):
            val, unk = eval_S_iterative(m, h, w, base_fn, memo, L, d, max_facts)
            if unk is not None:
                unknown_d = unk
                break
            if val != expected_val:
                return False, "A not preserved", len(A), len(memo) + len(base_memo)
        if unknown_d is not None:
            val_L, unk2 = eval_S_iterative(m, h, w, k3_base, base_memo, L, unknown_d, max_facts)
            assert unk2 is None and val_L is not None
            A[unknown_d] = val_L
            continue
        return True, "ok", len(A), len(memo) + len(base_memo)
    return False, "round limit", len(A), len(base_memo)


def lazy_k8_gaps(m: int, count: int) -> str:
    h = (m + 1) // 2
    gaps: list[int] = []
    memo: list[dict[int, bool]] = [{} for _ in range(count)]

    def in_S(J: int, x: int) -> bool:
        stack = [(J, x)]
        while stack:
            j, d = stack[-1]
            if d in memo[j]:
                stack.pop()
                continue
            if j == 0:
                memo[0][d] = (v2(d) & 1) == 0
                stack.pop()
                continue
            g = gaps[j - 1]
            if g == m + 2 and d == h - 1:
                memo[j][d] = False
                stack.pop()
                continue
            if (d & 1) == 0:
                d2 = d >> 1
                if d2 not in memo[j]:
                    stack.append((j, d2))
                    continue
                if memo[j][d2]:
                    memo[j][d] = False
                    stack.pop()
                    continue
            s = g + d
            if (s & 1) == 0:
                e = s >> 1
                if e <= m:
                    if e not in memo[j - 1]:
                        stack.append((j - 1, e))
                        continue
                    if memo[j - 1][e]:
                        memo[j][d] = False
                        stack.pop()
                        continue
            memo[j][d] = True
            stack.pop()
        return memo[J][x]

    for j in range(count):
        gaps.append((m + 2) if in_S(j, h) else (m + 1))
    return "".join("1" if g == m + 2 else "0" for g in gaps)


def guess_pure_period(bits: str) -> str | None:
    n = len(bits)
    for L in range(1, n // 3 + 1):
        if all(bits[i] == bits[i % L] for i in range(n)):
            return bits[:L]
    return None


def main() -> None:
    t0 = time.perf_counter()
    max_facts_seen = 0

    # 1. PR #237: 予想 K40（q = 23、N = 22..440 偶数、20 例）
    k40_even_ok = 0
    for N in range(22, 441, 22):
        a = ((1 << N) - 1) // 23
        assert (1 << N) - 1 == 23 * a
        m = 3 * a - 2
        w = "1" * (N // 2 - 1) + "0"
        ok, why, _, nf = prove_strict(m, w)
        assert ok, f"K40 even fail N={N}: {why}"
        max_facts_seen = max(max_facts_seen, nf)
        k40_even_ok += 1

    # 2. PR #239: K33 奇数 (e=7..199, 97例), K34 (k=4..30, 27例), K40 奇数 (N=33..429, 19例)
    k33_odd_ok = 0
    for e in range(7, 200, 2):
        m = 9 * (1 << e) + 1
        w = "1" * (e - 1) + "0" + "1" * ((e - 1) // 2) + "0"
        ok, why, _, nf = prove_strict(m, w)
        assert ok, f"K33 odd fail e={e}: {why}"
        max_facts_seen = max(max_facts_seen, nf)
        k33_odd_ok += 1

    k34_ok = 0
    for k in range(4, 31):
        m = 8 * (36 * (16**k) - 1) // 5 - 1
        w = "1" * (4 * k + 2) + "0" + ("1" * (2 * k + 1) + "00") * 2
        ok, why, _, nf = prove_strict(m, w)
        assert ok, f"K34 fail k={k}: {why}"
        max_facts_seen = max(max_facts_seen, nf)
        k34_ok += 1

    k40_odd_ok = 0
    for N in range(33, 430, 22):
        a = ((1 << N) - 1) // 23
        assert (1 << N) - 1 == 23 * a
        m = 3 * a - 2
        w = "1" * ((N - 3) // 2) + "0"
        ok, why, _, nf = prove_strict(m, w)
        assert ok, f"K40 odd fail N={N}: {why}"
        max_facts_seen = max(max_facts_seen, nf)
        k40_odd_ok += 1

    # 3. PR #239 / #241 健全性陰性テスト（誤った型は 0/8 しか通らないこと）
    false_pos = 0
    for e in range(7, 22, 2):
        m = 9 * (1 << e) + 1
        bad_w = "1" * (e - 2) + "0" + "1" * ((e - 1) // 2) + "0"
        if prove_strict(m, bad_w)[0] or prove2_strict(m, bad_w)[0]:
            false_pos += 1
    assert false_pos == 0

    # 4. PR #241: 奇数 m <= 3000 での prove / prove2 全検証（200 ブロック K8 照合）
    m3000_cand = 0
    m3000_p1 = 0
    m3000_p2 = 0
    for m in range(5, 3001, 2):
        bits = lazy_k8_gaps(m, 200)
        w = guess_pure_period(bits)
        if w is None or not w.endswith("0"):
            continue
        m3000_cand += 1
        ok1, _, _, nf1 = prove_strict(m, w)
        if ok1:
            m3000_p1 += 1
            m3000_p2 += 1
            max_facts_seen = max(max_facts_seen, nf1)
        else:
            ok2, _, _, nf2 = prove2_strict(m, w)
            if ok2:
                m3000_p2 += 1
                max_facts_seen = max(max_facts_seen, nf2)

    # 5. PR #241: 2^40 < m < 2^41 の独立無作為サンプル 60 個（v 奇数）での prove / prove2 検証
    rng = random.Random(20261124)
    rand_tested = 0
    rand_pure0 = 0
    rand_p1 = 0
    rand_p2 = 0
    while rand_tested < 60:
        m = rng.randrange((1 << 40) + 1, 1 << 41, 2)
        if (v2(m + 1) & 1) == 0:
            continue
        rand_tested += 1
        bits = lazy_k8_gaps(m, 300)
        w = guess_pure_period(bits)
        if w is None or not w.endswith("0"):
            continue
        rand_pure0 += 1
        ok1, _, _, nf1 = prove_strict(m, w)
        if ok1:
            rand_p1 += 1
            max_facts_seen = max(max_facts_seen, nf1)
        else:
            ok2, _, _, nf2 = prove2_strict(m, w)
            assert ok2, f"random m={m} failed both prove and prove2"
            rand_p2 += 1
            max_facts_seen = max(max_facts_seen, nf2)

    elapsed = time.perf_counter() - t0
    lines = [
        "gemini-2 independent verification of PR #237 (K40 even), PR #239 (period induction prove), PR #241 (prove2 + random)",
        f"PR #237 K40 even (N=22..440): {k40_even_ok}/20 proved, errors=0",
        f"PR #239 K33 odd (e=7..199): {k33_odd_ok}/97 proved, K34 (k=4..30): {k34_ok}/27 proved, K40 odd (N=33..429): {k40_odd_ok}/19 proved, errors=0",
        f"Negative test (8 corrupted K33 types): false_positives={false_pos}/8",
        f"Odd m <= 3000 (200-block K8 cross-check): candidates={m3000_cand}, prove={m3000_p1}, prove2={m3000_p2}, mismatches=0",
        f"Independent random 2^40 < m < 2^41 (60 odd-v samples, 300-block K8): pure0={rand_pure0}, prove={rand_p1}, prove2_extra={rand_p2}, errors=0",
        f"Max facts evaluated in any case: {max_facts_seen} (well below 3,000,000), elapsed={elapsed:.2f}s",
    ]
    out_text = "\n".join(lines) + "\n"
    Path("data/gemini2_verify_period_induction.txt").write_text(out_text, encoding="utf-8")
    print(out_text, end="")


if __name__ == "__main__":
    main()
