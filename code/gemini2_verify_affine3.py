"""
gemini-2 による厳密整数演算の独立 Python 3 値 1 次式証明書生成器・独立健全性検証器を用いて、
3 値 1 次式証明書群 6 本（PR #104, #106, #108, #109, #110, #120）の全 7,919 類を
ゼロから独立再計算・固定点検証・密度検証・K8 実測照合する。

実行方法:
    python code/gemini2_verify_affine3.py
出力:
    data/gemini2_verify_affine3.txt
"""

from __future__ import annotations

import re
import subprocess
import time
from fractions import Fraction
from pathlib import Path

T, F, U = 1, 0, 2


def not3(x: int) -> int:
    return U if x == U else (1 - x)


def and3(a: int, b: int, c: int) -> int:
    if a == F or b == F or c == F:
        return F
    if a == T and b == T and c == T:
        return T
    return U


def meet3(a: int, b: int) -> int:
    return a if a == b else U


def v2(n: int) -> int:
    assert n > 0
    return (n & -n).bit_length() - 1


def ceil_div(num: int, den: int) -> int:
    assert den > 0
    return (num + den - 1) // den


class LazyK8:
    def __init__(self, m: int) -> None:
        self.m = m
        self.h = (m + 1) // 2
        self.gaps: list[int] = []
        self.memo: list[dict[int, bool]] = []

    def in_S(self, J: int, x: int) -> bool:
        while len(self.memo) <= J:
            self.memo.append({})
        cache = self.memo[J]
        if x in cache:
            return cache[x]
        if J == 0:
            res = (v2(x) & 1) == 0
        else:
            g = self.gap(J - 1)
            res = True
            if (x & 1) == 0 and self.in_S(J, x >> 1):
                res = False
            elif ((g + x) & 1) == 0:
                half = (g + x) >> 1
                if 1 <= half <= self.m and self.in_S(J - 1, half):
                    res = False
            if res and g == self.m + 2 and x == self.h - 1:
                res = False
        cache[x] = res
        return res

    def gap(self, J: int) -> int:
        while len(self.gaps) <= J:
            idx = len(self.gaps)
            self.gaps.append(self.m + 2 if self.in_S(idx, self.h) else self.m + 1)
        return self.gaps[J]


class Affine3Certifier:
    """厳密整数演算による独立 3 値 1 次式証明書構築器・独立健全性検証器。"""

    def __init__(self, A: int, B: int, pre: str, per: str) -> None:
        self.A = A
        self.B = B
        self.p = len(pre)
        self.L = len(per)
        self.N = self.p + self.L
        self.want_bits = [int(c) for c in (pre + per)]
        self.H = (A // 2, (B + 1) // 2)
        self.HM1 = (A // 2, (B - 1) // 2)
        self.t_min = 0

    def _raise_t(self, t: int) -> None:
        if t > self.t_min:
            self.t_min = t

    def _le_m(self, xa: int, xb: int) -> bool:
        da = self.A - xa
        db = self.B - xb
        if da > 0:
            req = ceil_div(-db, da)
            if req > 0:
                self._raise_t(req)
            return True
        if da < 0:
            req = (db // (-da)) + 1
            if req > 0:
                self._raise_t(req)
            return False
        return db >= 0

    def _eq_hm1(self, xa: int, xb: int) -> bool:
        ha, hb = self.HM1
        if xa == ha:
            return xb == hb
        da = xa - ha
        db = hb - xb
        if db % da == 0:
            t0 = db // da
            if t0 >= 0:
                self._raise_t(t0 + 1)
        return False

    def _k3(self, xa: int, xb: int) -> int:
        assert xb > 0 and xa >= 0
        vb = v2(xb)
        if xa == 0 or v2(xa) > vb:
            return T if (vb & 1) == 0 else F
        return U

    def build_and_verify(self) -> tuple[int, int]:
        A, B, p, L, N = self.A, self.B, self.p, self.L, self.N
        H = self.H
        over: dict[tuple[int, int], int] = {}

        for _ in range(10000):
            memo: dict[tuple[int, int, int, int], int] = {}
            dirty = False

            def raw(node: int, xa: int, xb: int, alt: int) -> int:
                pr = (p + L - 1) if (node == p and alt == 1) else (node - 1)
                if pr < 0:
                    return self._k3(xa, xb)
                if (xa & 1) != 0:
                    return U
                if (xb & 1) == 0:
                    i_val = mem(node, xa >> 1, xb >> 1, alt)
                else:
                    i_val = F
                g2 = mem(pr, H[0], H[1], 0)
                if g2 == U:
                    return and3(not3(i_val), U, T)
                sa = A + xa
                sb = B + (2 if g2 == T else 1) + xb
                if (sa & 1) != 0:
                    ii_val = U
                elif (sb & 1) == 0:
                    ea, eb = sa >> 1, sb >> 1
                    if self._le_m(ea, eb):
                        ii_val = mem(pr, ea, eb, 0)
                    else:
                        ii_val = F
                else:
                    ii_val = F
                iii_val = T if (g2 == T and self._eq_hm1(xa, xb)) else F
                return and3(not3(i_val), not3(ii_val), not3(iii_val))

            def mem(node: int, xa: int, xb: int, alt: int) -> int:
                nonlocal dirty
                if node == p and alt == 0:
                    k = (xa, xb)
                    v = over.get(k)
                    if v is not None:
                        return v
                    r = raw(p, xa, xb, 0)
                    over[k] = r
                    dirty = True
                    return r
                key = (node, alt, xa, xb)
                v = memo.get(key)
                if v is not None:
                    return v
                r = raw(node, xa, xb, alt)
                memo[key] = r
                return r

            for n in range(N):
                g = mem(n, H[0], H[1], 0)
                if g == U:
                    raise RuntimeError(f"gap U at node {n}")
                if g != self.want_bits[n]:
                    raise RuntimeError(f"gap mismatch at node {n}: got={g} want={self.want_bits[n]}")

            done: set[tuple[int, int]] = set()
            while True:
                todo = [k for k in over if k not in done]
                if not todo:
                    break
                for k in todo:
                    done.add(k)
                    v0 = raw(p, k[0], k[1], 0)
                    v1 = mem(p, k[0], k[1], 1)
                    nv = meet3(v0, v1)
                    if nv != over[k]:
                        over[k] = nv
                        dirty = True

            if not dirty:
                # 独立健全性検証: 固定点の全確定事実が t >= t_min で K3・K8 の 3 値規則を満たすことを直接検査
                self._independent_soundness_check(over, memo)
                return A * self.t_min + B, len(memo) + len(over)

        raise RuntimeError("did not reach fixed point")

    def _independent_soundness_check(
        self, over: dict[tuple[int, int], int], memo: dict[tuple[int, int, int, int], int]
    ) -> None:
        A, B, p, L, N, tm = self.A, self.B, self.p, self.L, self.N, self.t_min
        H, HM1 = self.H, self.HM1

        def lookup(node: int, alt: int, xa: int, xb: int) -> int:
            if node == p and alt == 0:
                return over[(xa, xb)]
            return memo[(node, alt, xa, xb)]

        def eval_check(node: int, alt: int, xa: int, xb: int) -> int:
            # 1 <= x(t) <= m(t) for all t >= tm
            assert xa >= 0 and xa * tm + xb >= 1
            assert A >= xa and (A - xa) * tm + (B - xb) >= 0
            pr = (p + L - 1) if (node == p and alt == 1) else (node - 1)
            if pr < 0:
                return self._k3(xa, xb)
            if (xa & 1) != 0:
                return U
            i_val = lookup(node, alt, xa >> 1, xb >> 1) if (xb & 1) == 0 else F
            g2 = self.want_bits[pr]
            sa = A + xa
            sb = B + (2 if g2 == 1 else 1) + xb
            if (sa & 1) != 0:
                ii_val = U
            elif (sb & 1) == 0:
                ea, eb = sa >> 1, sb >> 1
                if ea < A or (ea == A and eb <= B):
                    assert (A - ea) * tm + (B - eb) >= 0
                    ii_val = lookup(pr, 0, ea, eb)
                else:
                    assert (ea - A) * tm + (eb - B) >= 1
                    ii_val = F
            else:
                ii_val = F
            if g2 == 1:
                if xa == HM1[0] and xb == HM1[1]:
                    iii_val = T
                else:
                    if xa != HM1[0] and (HM1[1] - xb) % (xa - HM1[0]) == 0:
                        assert (HM1[1] - xb) // (xa - HM1[0]) < tm
                    iii_val = F
            else:
                iii_val = F
            return and3(not3(i_val), not3(ii_val), not3(iii_val))

        # 1. 全節点のギャップが確定し期待ビットに一致
        for n in range(N):
            assert lookup(n, 0, H[0], H[1]) == self.want_bits[n]
        # 2. memo 内の全エントリが評価式と一致
        for (node, alt, xa, xb), val in memo.items():
            assert eval_check(node, alt, xa, xb) == val
        # 3. over 内の全エントリが meet(eval_check(p, 0), eval_check(p, 1)) と一致
        for (xa, xb), val in over.items():
            v0 = eval_check(p, 0, xa, xb)
            v1 = eval_check(p, 1, xa, xb)
            assert meet3(v0, v1) == val


def git_show(repo: Path, ref_path: str) -> str:
    return subprocess.check_output(["git", "-C", str(repo), "show", ref_path]).decode("utf-8")


def parse_proved(text: str) -> list[tuple[int, int, int, str, str, int]]:
    proved = []
    mode = ""
    pat_p = re.compile(r"^m ≡ (\d+) \(mod (\d+)\) \| (\d+) \| ([01-]+) \| ([01]+) \| (\d+)$")
    for raw in text.splitlines():
        line = raw.strip()
        if line.startswith("## 新しく証明できた類") or line.startswith("## 証明できた類"):
            mode = "proved"
            continue
        if line.startswith("##"):
            mode = ""
            continue
        if mode == "proved":
            m = pat_p.match(line)
            if m:
                proved.append((int(m.group(2)), int(m.group(1)), int(m.group(3)),
                               "" if m.group(4) == "-" else m.group(4), m.group(5), int(m.group(6))))
    return proved


def main() -> None:
    t0 = time.perf_counter()
    repo = Path(__file__).resolve().parent.parent
    lines = ["=== gemini-2 独立検証: 3 値 1 次式証明書群（PR #104, #106, #108, #109, #110, #120） ==="]

    jobs = [
        ("PR#104 (v=3, affine3)", 3, "origin/claude-1/affine3:data/affine3_v3_T19.txt"),
        ("PR#104 (v=5, affine3)", 5, "origin/claude-1/affine3:data/affine3_v5_T19.txt"),
        ("PR#104 (v=7, affine3)", 7, "origin/claude-1/affine3:data/affine3_v7_T19.txt"),
        ("PR#106 (v=1, affine3)", 1, "origin/claude-1/affine3-v1:data/affine3_v1_T20.txt"),
        ("PR#108 (v=7, affine3 refine)", 7, "origin/claude-1/affine3-refine:data/affine3_refine_v7.txt"),
        ("PR#109 (v=5, affine3 refine)", 5, "origin/claude-1/affine3-refine-v5:data/affine3_refine_v5.txt"),
        ("PR#110 (v=3, affine3 refine)", 3, "origin/claude-1/affine3-refine-v3:data/affine3_refine_v3.txt"),
        ("PR#120 (v=1, affine3 refine)", 1, "origin/claude-1/affine3-refine-v1:data/affine3_refine_v1.txt"),
    ]

    grand_total = 0
    grand_errs = 0
    grand_k8 = 0
    grand_k8_errs = 0
    err_samples: list[str] = []

    for label, v, ref_path in jobs:
        proved = parse_proved(git_show(repo, ref_path))
        mod_base = 1 << (v + 1)
        rem_base = (1 << v) - 1
        dens = Fraction(0)
        errs = 0
        k8_cnt = 0
        k8_errs = 0
        for idx, (A, B, m_min_claimed, pre, per, _) in enumerate(proved):
            grand_total += 1
            assert B % mod_base == rem_base and (A & (A - 1)) == 0
            dens += Fraction(mod_base, A)
            try:
                cert = Affine3Certifier(A, B, pre, per)
                m_min_indep, _ = cert.build_and_verify()
                if m_min_indep > m_min_claimed:
                    errs += 1
                    if len(err_samples) < 20:
                        err_samples.append(f"{label} m={B} mod {A}: indep={m_min_indep} > claimed={m_min_claimed}")
            except Exception as exc:
                errs += 1
                if len(err_samples) < 20:
                    err_samples.append(f"{label} m={B} mod {A}: {exc}")
                continue
            # 各ファイルから代表 15 類（先頭 10 類 + M_min 最小側 5 類）を査読済み K8 で実測照合
            if idx < 10 or (m_min_claimed <= 20000 and k8_cnt < 25):
                k8_cnt += 1
                grand_k8 += 1
                lazy = LazyK8(m_min_claimed)
                want = [int(c) for c in pre] + [int(c) for c in per] * 2
                got = [1 if lazy.gap(j) == m_min_claimed + 2 else 0 for j in range(len(want))]
                if got != want:
                    k8_errs += 1
                    grand_k8_errs += 1
        grand_errs += errs
        lines.append(
            f"[{label}] 証明 {len(proved)} 類, 増分密度={float(dens):.6f} ({dens}), "
            f"独立再計算+健全性検証エラー={errs}, K8 照合({k8_cnt}個)エラー={k8_errs}"
        )

    elapsed = time.perf_counter() - t0
    lines.append(
        f"[総括] 全 {grand_total} 類の独立 3 値証明書再計算・独立健全性検証: エラー {grand_errs} 件, "
        f"K8 実測照合 ({grand_k8} 個) エラー {grand_k8_errs} 件, 所要時間 {elapsed:.2f} 秒"
    )
    if err_samples:
        lines.append("ERROR SAMPLES:")
        lines.extend(err_samples)
    out_text = "\n".join(lines) + "\n"
    Path("data/gemini2_verify_affine3.txt").write_text(out_text, encoding="utf-8")
    print(out_text, end="")
    assert grand_errs == 0 and grand_k8_errs == 0


if __name__ == "__main__":
    main()
