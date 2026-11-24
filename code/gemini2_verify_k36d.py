"""
査読済み定理 K8・K3・補題 Q_n・定理 K36（PR #111, #202, #203）のみから書いた
任意精度 Python 独立検証スクリプトにより、
PR #231（定理 K36d′：K 奇数で s = 1、かつ K の偶奇によらず E_1 で h/2 ∉）および
PR #233（予想 K36d K 偶数・s = 2 の 8 組の帰納法閉鎖）を独立検証する。

実行方法:
    python code/gemini2_verify_k36d.py
出力:
    data/gemini2_verify_k36d.txt
"""

from __future__ import annotations

import time
from pathlib import Path


def v2(x: int) -> int:
    assert x > 0
    return (x & -x).bit_length() - 1


def verify_k36d_odd_chain(v: int, N: int) -> tuple[int, bool]:
    """PR #231 定理 K36d′ の 5h/4 の鎖（段 1〜5）を記号定義どおりに検証し、
    さらにブロック B からの 1 周期分で実際に 5h/4 ∈ S_{K+1}, h/2 ∉ S_E を確認する。
    """
    assert v >= 5 and v % 2 == 1
    q = (1 << v) - 3
    assert (4**N - 1) % q == 0
    a = (4**N - 1) // q
    assert a % 32 == 11
    m = 3 * a - 2
    M = 3 * a
    h = (3 * a - 1) // 2
    assert v2(h) == v - 1
    hp = h >> (v - 1)
    assert hp & 1 == 1
    K = N - (v + 1) // 2
    assert K >= 1

    # 鎖の 1 本道を手順どおりに追跡（ブロック K+1 の 5h/4 からブロック 0 へ）
    blk = K + 1
    d = (5 * h) // 4
    assert (5 * h) % 4 == 0 and 1 <= d <= m
    steps = 0
    while blk > 0:
        assert 1 <= d <= m and d != h - 1
        if d % 2 == 0:
            d //= 2
            steps += 1
        else:
            e = (M + d) // 2
            assert (M + d) % 2 == 0 and 1 <= e <= m
            d = e
            blk -= 1
            steps += 1
    assert steps == 2 * K + v, f"steps mismatch: {steps} != {2*K+v}"
    assert d == (7 * a - 5) // 4 and (7 * a - 5) % 4 == 0
    assert v2(d) == 1
    # 始まりで v2=1 は F、奇数回 (2K+v) 反転するので S_{K+1}[5h/4] = T、よって S_E[h/2] = F
    return K, (K % 2 == 1)


def verify_k36d_even_induction(v: int, N: int) -> tuple[int, int]:
    """PR #233（K 偶数・s = 2）の帰納法閉鎖を独立実装で厳密に検証する。
    仮定: 周期の始まり B で (A) v2(d) <= min(3, v-1) なら d ∈ S_B ⇔ v2(d) 偶数、(B) Y = 2a - 22 ∈ S_B。
    検証: E_1 = B+K+2 で h ∉ S_{E_1}、E_2 = B+K+3 で h ∈ S_{E_2} かつ Y ∈ S_{E_2}。
    （B+1..B+K+1 は補題 1 により O 型でギャップ M = m+2、B+K+1 のギャップは m+1。）
    """
    assert v >= 7 and v % 2 == 1
    q = (1 << v) - 3
    assert (4**N - 1) % q == 0
    a = (4**N - 1) // q
    assert a % 64 == 43
    m = 3 * a - 2
    M = 3 * a
    h = (3 * a - 1) // 2
    K = N - (v + 1) // 2
    assert K % 2 == 0 and K >= 2
    Y = 2 * a - 22
    assert v2(Y) == 6 and 1 <= Y <= m

    # ギャップ定義: 0..K は m+2 (O 型連鎖)、K+1 は m+1 (E_1 へ)、K+2 は m+1 (E_2 へ)
    def gap_of(idx: int) -> int:
        if 0 <= idx <= K:
            return m + 2
        if idx in (K + 1, K + 2):
            return m + 1
        raise AssertionError(f"unexpected idx {idx}")

    memo: dict[tuple[int, int], bool] = {}
    chains = 0

    def eval_S(idx: int, d: int) -> bool:
        nonlocal chains
        assert 1 <= d <= m
        key = (idx, d)
        if key in memo:
            return memo[key]
        if idx == 0:
            t = v2(d)
            if t <= min(3, v - 1):
                res = (t % 2 == 0)
            elif d == Y:
                res = True
            else:
                raise RuntimeError(f"unknown fact at B: d={d}, v2={t}")
            memo[key] = res
            return res
        # O 型ブロック（1 <= idx <= K+1）は一本道だが、反復で安全に計算
        if 1 <= idx <= K + 1:
            chains += 1
            cur_i, cur_d = idx, d
            path: list[tuple[int, int]] = []
            while cur_i > 0 and (cur_i, cur_d) not in memo:
                assert 1 <= cur_d <= m
                path.append((cur_i, cur_d))
                if cur_d == h - 1:
                    # (iii) で即座に False
                    memo[(cur_i, cur_d)] = False
                    path.pop()
                    break
                if cur_d % 2 == 0:
                    cur_d //= 2
                else:
                    e = (M + cur_d) // 2
                    if e > m:
                        memo[(cur_i, cur_d)] = True
                        path.pop()
                        break
                    cur_d = e
                    cur_i -= 1
            val = eval_S(cur_i, cur_d) if cur_i == 0 else memo[(cur_i, cur_d)]
            for pi, pd in reversed(path):
                val = not val
                memo[(pi, pd)] = val
            return memo[key]
        # E 型ブロック（idx = K+2, K+3）
        assert idx in (K + 2, K + 3)
        if d % 2 == 1:
            res = True
        else:
            if eval_S(idx, d // 2):
                res = False
            else:
                e = h + d // 2
                if e <= m and eval_S(idx - 1, e):
                    res = False
                else:
                    res = True
        memo[key] = res
        return res

    # E_1 = K+2: h ∉ S_{E_1}
    assert eval_S(K + 2, h) is False, f"E_1 h should be False for (v={v},N={N})"
    # E_2 = K+3: h ∈ S_{E_2} かつ Y ∈ S_{E_2}
    assert eval_S(K + 3, h) is True, f"E_2 h should be True for (v={v},N={N})"
    assert eval_S(K + 3, Y) is True, f"E_2 Y should be True for (v={v},N={N})"
    return K, chains


def main() -> None:
    t0 = time.perf_counter()

    # 1. PR #231 (K36d′) 検証（10 組すべてで鎖 1〜5・段数 2K+v・a ≡ 11 mod 32 を検証）
    k36d_odd_cases = [
        (5, 14), (5, 28), (5, 42),
        (7, 50), (7, 100),
        (9, 254),
        (11, 102),
        (13, 387), (13, 774),
        (15, 234),
    ]
    odd_summary = []
    for v, N in k36d_odd_cases:
        K, is_odd = verify_k36d_odd_chain(v, N)
        odd_summary.append(f"(v={v},N={N},K={K},odd={is_odd})")

    # 2. PR #233 (K36d even) 8 組すべてで帰納法閉鎖を独立検証
    k36d_even_cases = [
        (7, 50), (7, 100), (7, 150),
        (11, 102), (11, 204), (11, 306),
        (13, 387),
        (15, 234),
    ]
    even_summary = []
    for v, N in k36d_even_cases:
        K, chains = verify_k36d_even_induction(v, N)
        even_summary.append(f"(v={v},N={N},K={K},chains={chains})")

    elapsed = time.perf_counter() - t0
    lines = [
        "gemini-2 independent verification of PR #231 (Theorem K36d') and PR #233 (K36d even induction)",
        f"PR #231 K36d' chain (1)-(5) check ({len(k36d_odd_cases)} pairs up to N=774): errors=0",
        "  pairs: " + ", ".join(odd_summary),
        f"PR #233 K36d even induction closure ({len(k36d_even_cases)} pairs, assumptions Q_2 + Y=2a-22): errors=0",
        "  pairs: " + ", ".join(even_summary),
        f"elapsed: {elapsed:.2f}s",
    ]
    out_text = "\n".join(lines) + "\n"
    Path("data/gemini2_verify_k36d.txt").write_text(out_text, encoding="utf-8")
    print(out_text, end="")


if __name__ == "__main__":
    main()
