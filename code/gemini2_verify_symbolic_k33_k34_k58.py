"""
gemini2_verify_symbolic_k33_k34_k58.py — PR #348（定理 K58）・PR #350（定理 K34）・PR #352（定理 K33）・PR #360（記号評価器）・PR #356（予想 K60 131 例）の完全独立 Python 検証

何を計算するか:
  1. PR #360（code/chain_symbolic.js）の完全独立 Python 再実装（厳密有理数 Fraction 使用、浮動小数点なし）:
     - 以下の 2 点の厳密化（hardening）を加えた上で、k58 / k34 / k33-1 / k33-3 の全 4 族を記号的に検証する:
       (a) 不動点区間内の中間点 K_start + m*t <= v2(c) + 1 でも d = h - 1 が生じないことを全検査。
       (b) K が R に依存する点（K.r1 > 0）でも、不動点か否かに関わらず 0 < b/r <= 3（b/r = 3 なら N - K の下限で d <= 3a - 4）を全検査。
     - すべての不等式（kst >= 1, E < Ng, v2(inner) < N, 0 < d <= 3a - 4, d != h - 1, e <= m）から、
       記号証明が厳密に成立する明示的な最小下限 R_min（および N_min / e_min）を自動算出し、
       既査読の prove3 範囲（K58: N <= 399, K34: N <= 401, K33: e <= 399）との間にギャップが 0 であることを証明する。
     - 連の中の任意の長さ n（1 <= n <= ℓ）について、b = ±1, t = 2 不動点による全 n の網羅性を確認する。
     - 各族の非自明な E 型事実の値（K58: 6 個, K34: 34 個, K33-1: 4 個, K33-3: 4 個）を、具体値（K58: N=43, K34: N=41, K33: e=21, 23）の K8/prove3 評価と全数クロスチェックする。
  2. PR #356（予想 K60: v = 5, rho = 2, 29a + 1 = s*2^N, 41 <= N <= 301 全 131 個）:
     - 表の 14 剰余類 (N mod 28) の s と周期形に対して Python 独立実装の prove3(k33d=True) を並列実行し、
       全 131/131 個が確定することを検証する。

実行方法（リポジトリのルートで）:
  uv run python code/gemini2_verify_symbolic_k33_k34_k58.py > data/gemini2_verify_symbolic_k33_k34_k58.txt
"""
from __future__ import annotations

import concurrent.futures
import math
import sys
import time
from fractions import Fraction

sys.setrecursionlimit(300000)


def v2(x: int) -> int:
    if x == 0:
        return 10**9
    if x < 0:
        x = -x
    return (x & -x).bit_length() - 1


# ---------------------------------------------------------------------------
# Affine linear expression in R: r1 * R + r0
# ---------------------------------------------------------------------------
class Lin:
    __slots__ = ("r1", "r0")

    def __init__(self, r1: int, r0: int) -> None:
        self.r1 = r1
        self.r0 = r0

    def __add__(self, other: Lin) -> Lin:
        return Lin(self.r1 + other.r1, self.r0 + other.r0)

    def __sub__(self, other: Lin) -> Lin:
        return Lin(self.r1 - other.r1, self.r0 - other.r0)

    def scale(self, k: int) -> Lin:
        return Lin(self.r1 * k, self.r0 * k)

    def eval_at(self, R: int) -> int:
        return self.r1 * R + self.r0

    def eq(self, other: Lin) -> bool:
        return self.r1 == other.r1 and self.r0 == other.r0

    def cmp_inf(self, other: Lin) -> int:
        d = self - other
        if d.r1 != 0:
            return 1 if d.r1 > 0 else -1
        if d.r0 != 0:
            return 1 if d.r0 > 0 else -1
        return 0

    def min_R_for_ge(self, rhs: int) -> int:
        """Smallest integer R such that r1*R + r0 >= rhs (assuming r1 >= 0)."""
        if self.r1 == 0:
            assert self.r0 >= rhs, f"Constant constraint {self.r0} >= {rhs} violated!"
            return 1
        assert self.r1 > 0, f"Negative slope {self.r1} in >= {rhs}"
        num = rhs - self.r0
        if num <= 0:
            return 1
        return (num + self.r1 - 1) // self.r1

    def __str__(self) -> str:
        if self.r1 == 0:
            return str(self.r0)
        coef = "" if self.r1 == 1 else ("-" if self.r1 == -1 else str(self.r1))
        if self.r0 == 0:
            return f"{coef}R"
        return f"{coef}R+{self.r0}" if self.r0 > 0 else f"{coef}R{self.r0}"


def con(k: int) -> Lin:
    return Lin(0, k)


# ---------------------------------------------------------------------------
# Independent exact-rational symbolic evaluator with explicit R_min tracking
# ---------------------------------------------------------------------------
def run_symbolic_family(F: dict) -> dict:
    q: int = F["q"]
    r: int = F["r"]
    s: int = F["s"]
    N_lin: Lin = F["N"]
    Rpar: int = F["Rpar"]
    assert r in (1, -1)

    fails: list[str] = []
    min_R_reasons: list[tuple[int, str]] = []
    min_a_req = 5  # a >= 5 ensures m = 3a - 2 >= 13

    def require_R(r_val: int, reason: str) -> None:
        if r_val > 1:
            min_R_reasons.append((r_val, reason))

    def require_a(a_val: int) -> None:
        nonlocal min_a_req
        if a_val > min_a_req:
            min_a_req = a_val

    def par_of(x: Lin) -> int:
        return ((x.r1 % 2) * Rpar + (x.r0 % 2)) % 2

    # Build E-type block graph
    E: list[dict] = [{"id": "B"}]
    for t, ln in F["segs"]:
        if t == "1":
            E.append({"pending": True, "run": {"len": ln, "from": len(E) - 1}})
        else:
            for _ in range(ln):
                last = E[-1]
                if last.get("pending"):
                    last["pending"] = False
                    last["prev"] = "O"
                else:
                    E.append({"prev": "E", "prevId": len(E) - 1})
    for idx, x in enumerate(E):
        x["id"] = "B" if idx == 0 else ("L" if idx == len(E) - 1 else f"E{idx}")

    def norm_key(al: int, c: int, K: int) -> tuple[int, int, int]:
        while K > 0 and al % 2 == 0 and c % 2 == 0:
            al //= 2
            c //= 2
            K -= 1
        return (al, c, K)

    def fmt(al: int, c: int, K: int) -> str:
        return f"({al}a{'+' + str(-c) if c < 0 else '−' + str(c)})/2^{K}"

    assume: dict[tuple[int, int, int], bool] = {
        norm_key(al, c, K): val for al, c, K, val in F["assume"]
    }

    def v2_dist(al: int, c: int, K: int) -> int:
        beta = r * al + q * c
        if beta == 0:
            return 10**9
        v = v2(beta)
        # Requires N + v2(c) > v so v2(beta*a - c*s*2^N) == v
        gam = v2(c) if c != 0 else 0
        require_R(N_lin.min_R_for_ge(v + 1 - gam), f"v2_dist({fmt(al, c, K)}): N+{gam} > {v}")
        return v - K

    def T_map(b: int) -> tuple[int, int] | None:
        x = b + 3 * r
        if x == 0:
            return None
        t = v2(x)
        return (x >> t, t)

    def check_concrete_point(b: int, c: int, K: int, label: str) -> str:
        """Exact rational check of 0 < d <= 3a - 4 and d != h - 1 at concrete K."""
        powK = 1 << K
        lam = Fraction(b * powK - c * q, r * powK)
        kap = Fraction(-c, powK)
        if lam == Fraction(3, 2) and kap == Fraction(-3, 2):
            return "H"
        # Check d > 0: lam*a + kap > 0
        if lam < 0 or (lam == 0 and kap <= 0):
            fails.append(f"d <= 0 at {label} (b={b}, c={c}, K={K}, lam={lam}, kap={kap})")
            return "bad"
        if lam > 0 and kap <= 0:
            # lam*a > -kap => a > -kap/lam
            need_a = math.floor(-kap / lam) + 1
            require_a(need_a)
        # Check d <= 3a - 4: (3 - lam)*a >= kap + 4
        if lam > 3 or (lam == 3 and kap > -4):
            fails.append(f"d > 3a-4 at {label} (b={b}, c={c}, K={K}, lam={lam}, kap={kap})")
            return "bad"
        if lam < 3 and kap + 4 > 0:
            need_a = math.ceil((kap + 4) / (3 - lam))
            require_a(need_a)
        # Check d != h - 1 = (3/2)a - 3/2: if lam != 3/2, a != (-3/2 - kap)/(lam - 3/2)
        if lam != Fraction(3, 2):
            bad_a = (Fraction(-3, 2) - kap) / (lam - Fraction(3, 2))
            if bad_a.denominator == 1 and bad_a.numerator >= 1:
                require_a(bad_a.numerator + 1)
        return "ok"

    def check_growing_K_point(b: int, c: int, K_lin: Lin, label: str) -> None:
        """Exact check when K grows with R (K.r1 > 0): both fixed-point AND non-fixed-point!"""
        # d = (b/r)*a - (c*s/r)*2^{N - K} = ((b - c*q/2^K)/r)*a - c/2^K
        lim = Fraction(b, r)
        if not (0 < lim <= 3) or lim == Fraction(3, 2):
            fails.append(f"growing-K point invalid limit {lim} at {label} (b={b}, c={c}, K={K_lin})")
            return
        if lim == 3:
            # Need (c*s/r)*2^{N - K} >= 4
            cs_r = Fraction(c * s, r)
            if cs_r <= 0:
                fails.append(f"lim=3 but cs/r <= 0 at {label}")
                return
            nk_diff = N_lin - K_lin
            # Need nk_diff >= min_nk where cs_r * 2^min_nk >= 4
            min_nk = 0
            while cs_r * (1 << min_nk) < 4:
                min_nk += 1
            require_R(nk_diff.min_R_for_ge(min_nk), f"lim=3 d<=3a-4 at {label}: N-K >= {min_nk}")
        else:
            # Ensure K large enough that 0 < lam(K) < 3 and lam(K) != 3/2
            # Specifically |c*q/2^K| < min(lim, 3 - lim, |lim - 3/2|)
            margin = min(lim, 3 - lim, abs(lim - Fraction(3, 2)))
            min_K = 0
            while abs(Fraction(c * q, 1 << min_K)) >= margin:
                min_K += 1
            require_R(K_lin.min_R_for_ge(min_K), f"growing-K margin at {label}: K >= {min_K}")

    memo: dict[tuple[int, int, int, int], bool | None] = {}
    e_facts: dict[tuple[str, str], bool | None] = {}
    chain_count = 0

    def Eval(ei: int, al: int, c: int, K: int) -> bool | None:
        nk = norm_key(al, c, K)
        kk = (ei, nk[0], nk[1], nk[2])
        if kk in memo:
            return memo[kk]
        t = v2_dist(al, c, K)
        if t < 0:
            fails.append(f"Non-integer distance {fmt(al, c, K)}")
            val = None
        elif t == 0:
            val = True
        elif t == 1:
            val = False
        elif ei == 0:
            if nk in assume:
                val = assume[nk]
            else:
                fails.append(f"Unknown distance at B: {fmt(al, c, K)} (v2={t})")
                val = None
        else:
            first = Eval(ei, al, c, K + 1)
            if first is True:
                val = False
                e_facts[(E[ei]["id"], fmt(*nk))] = val
                memo[kk] = val
                return val
            al2 = 3 * (1 << K) + al
            c2 = (1 << K) + c
            K2 = K + 1
            lam = Fraction(al2, 1 << K2)
            kap = Fraction(-c2, 1 << K2)
            # Check e <= m = 3a - 2
            le = (lam < 3) or (lam == 3 and kap <= -2)
            if lam < 3 and kap + 2 > 0:
                require_a(math.ceil((kap + 2) / (3 - lam)))
            second: bool | None = False
            if le:
                x = E[ei]
                if x["prev"] == "E":
                    second = Eval(x["prevId"], al2, c2, K2)
                else:
                    second = Chain(x["run"], al2, c2, K2, ei)
            val = None if (first is None or second is None) else (not first and not second)
            e_facts[(E[ei]["id"], fmt(*nk))] = val
        memo[kk] = val
        return val

    def Chain(run_info: dict, al: int, c: int, K0: int, from_ei: int) -> bool | None:
        nonlocal chain_count
        chain_count += 1
        n_lin: Lin = run_info["len"]
        to_ei: int = run_info["from"]
        label = f"{E[from_ei]['id'] if from_ei >= 0 else 'h-run'}->{E[to_ei]['id']}:{fmt(al, c, K0)}"

        beta = r * al + q * c
        if beta == 0:
            fails.append(f"beta == 0 at {label}")
            return None
        v = v2(beta)
        if v < K0:
            fails.append(f"v < K0 at {label}")
            return None
        gam0 = v2(c) if c != 0 else 0
        require_R(N_lin.min_R_for_ge(v + 1 - gam0), f"entry v < N+gam at {label}")

        steps = con(v - K0)
        K = con(v)
        b = beta >> v
        j = con(0)
        cc = c
        h_stop = False
        end_v2: int | None = None
        end_form: tuple[int, int, int] | None = None

        for _ in range(10000):
            if K.r1 == 0:
                chk = check_concrete_point(b, cc, K.r0, label)
                if chk == "H":
                    h_stop = True
                    break
                if chk == "bad":
                    return None
            else:
                check_growing_K_point(b, cc, K, label)

            gam = v2(cc) if cc != 0 else 0
            Ng = N_lin + con(gam)
            co = cc >> gam
            Tb = T_map(b)
            if Tb is None:
                fails.append(f"b + 3r == 0 at {label}")
                return None
            b2, t = Tb
            Eexp = K + con(t)
            is_last = (j + con(1)).eq(n_lin)
            rel = Eexp.cmp_inf(Ng)

            if rel < 0:
                # Require Eexp <= Ng - 1
                require_R((Ng - Eexp).min_R_for_ge(1), f"E < Ng at {label}")
                if b2 == b and not is_last and t in (1, 2):
                    lim1 = n_lin - con(1) - j
                    lim2 = Ng - con(1 + t) - K
                    if t == 2:
                        p_rem = par_of(lim2)
                        if lim2.r1 % 2 != 0:
                            fails.append(f"Non-integer fixed-point slope at {label}")
                            return None
                        lim2 = Lin(lim2.r1 // 2, (lim2.r0 - p_rem) // 2)
                    kst = lim1 if lim1.cmp_inf(lim2) <= 0 else lim2
                    if kst.cmp_inf(con(1)) >= 0:
                        require_R(kst.min_R_for_ge(1), f"kst >= 1 at {label}")
                        if lim1.cmp_inf(lim2) <= 0:
                            require_R((lim2 - lim1).min_R_for_ge(0), f"lim1 <= lim2 at {label}")
                        else:
                            require_R((lim1 - lim2).min_R_for_ge(0), f"lim2 <= lim1 at {label}")
                        # Hardening (a): check intermediate concrete K <= v2(cc) + 1 for d = h - 1 & bounds
                        if K.r1 == 0:
                            max_h_k = (v2(cc) if cc != 0 else 0) + 2
                            k_probe = K.r0 + t
                            while k_probe <= max_h_k:
                                chk_mid = check_concrete_point(b, cc, k_probe, label + "(mid)")
                                if chk_mid != "ok":
                                    fails.append(f"Mid-segment violation ({chk_mid}) at K={k_probe} in {label}")
                                    return None
                                k_probe += t
                        # Check segment limit & end point
                        K_end_seg = K + kst.scale(t)
                        check_growing_K_point(b, cc, K_end_seg, label + "(seg_end)")
                        K = K_end_seg
                        j = j + kst
                        steps = steps + kst.scale(t)
                        continue
                if is_last:
                    end_v2 = t - 1
                    steps = steps + con(1)
                    if end_v2 >= 2:
                        if K.r1 != 0:
                            fails.append(f"endForm depends on R at {label}")
                            return None
                        bp = (1 << K.r0) * (b + 3 * r)
                        end_form = ((bp - q * cc) // r, cc, K.r0 + t)
                    break
                steps = steps + con(t)
                K = Eexp
                b = b2
                j = j + con(1)
                continue

            # Crossing Eexp >= Ng
            NK1 = Ng - K - con(1)
            if NK1.r1 != 0 or NK1.r0 < 0:
                fails.append(f"N+gam-K-1 invalid ({NK1}) at {label}")
                return None
            nk1 = NK1.r0
            if rel == 0:
                inner = r * b2 + q * co * s
                if inner == 0:
                    fails.append(f"inner == 0 at {label}")
                    return None
                u = v2(inner)
                require_R(N_lin.min_R_for_ge(u + 1), f"u={u} < N at {label}")
                if is_last:
                    end_v2 = nk1 + u
                    steps = steps + con(1)
                    end_form = ((1 << nk1) * b2 * r, (1 << nk1) * co * s * r, 0)
                    break
                steps = steps + con(1 + nk1 + u)
                c2 = r * co * s
                bt = b2 + q * r * co * s
                cc = c2
                K = con(u)
                b = bt >> u
                j = j + con(1)
                continue
            else:
                off = Eexp - Ng
                if off.r1 != 0 or off.r0 <= 0:
                    fails.append(f"E-Ng invalid ({off}) at {label}")
                    return None
                o = off.r0
                if is_last:
                    end_v2 = nk1
                    steps = steps + con(1)
                    end_form = ((1 << (nk1 + o)) * b2 * r, (1 << nk1) * co * s * r, 0)
                    break
                steps = steps + con(1 + nk1)
                al2 = r * (1 << o) * b2
                c2 = r * co * s
                bt = r * al2 + q * c2
                if bt % 2 == 0:
                    fails.append(f"post-crossing beta even at {label}")
                    return None
                cc = c2
                K = con(0)
                b = bt
                j = j + con(1)
                continue
        else:
            fails.append(f"guard exceeded at {label}")
            return None

        if h_stop:
            end_val: bool | None = False
        elif end_v2 == 0:
            end_val = True
        elif end_v2 == 1:
            end_val = False
        else:
            assert end_form is not None
            end_val = Eval(to_ei, end_form[0], end_form[1], end_form[2])
        par = par_of(steps)
        return None if end_val is None else (end_val if par == 0 else (not end_val))

    # Evaluate h-runs, E-type h values, and assumption reproduction
    runs = [x["run"] for x in E if "run" in x]
    for ru in runs:
        ln = ru["len"]
        candidates = [
            con(1), con(2), con(3),
            ln - con(2), ln - con(1), ln,
            Lin(1, -1), Lin(1, 0), Lin(1, 1), Lin(1, 2), Lin(1, 3),
        ]
        seen: set[str] = set()
        for n_c in candidates:
            if n_c.cmp_inf(con(1)) < 0 or n_c.cmp_inf(ln) > 0:
                continue
            s_key = str(n_c)
            if s_key in seen:
                continue
            seen.add(s_key)
            val = Chain({"len": n_c, "from": ru["from"]}, 3, 1, 1, -1)
            want = False if n_c.eq(ln) else True
            if val != want:
                fails.append(f"h-run len={s_key} got {val}, want {want}")

    # Check E-type h values (must match period!)
    # E[ei] is followed by '1' if E[ei+1] has prev=='O', else '0' (for ei == len(E)-1, followed by w[0] == '1')
    for ei in range(1, len(E)):
        got_h = Eval(ei, 3, 1, 1)
        if ei == len(E) - 1:
            want_h = True  # w[0] == '1' in all 4 families
        else:
            want_h = (E[ei + 1].get("prev") == "O")
        if got_h != want_h:
            fails.append(f"E-type h mismatch at {E[ei]['id']}: got {got_h}, want {want_h}")

    # Check assumption reproduction at L
    for al, c, K, want_v in F["assume"]:
        got_v = Eval(len(E) - 1, al, c, K)
        if got_v != want_v:
            fails.append(f"Assumption {fmt(al, c, K)} not reproduced at L: got {got_v}, want {want_v}")

    # Compute explicit R_min from both symbolic constraints and min_a_req
    r_min_sym = max((rv for rv, _ in min_R_reasons), default=1)
    # Also find smallest R with R % 2 == Rpar such that a = (s*2^N - r)/q >= min_a_req
    r_min = r_min_sym
    if r_min % 2 != Rpar:
        r_min += 1
    while True:
        N_val = N_lin.eval_at(r_min)
        if N_val >= 3 and (s * (1 << N_val) - r) % q == 0:
            a_val = (s * (1 << N_val) - r) // q
            if a_val >= min_a_req:
                break
        r_min += 2
    N_min = N_lin.eval_at(r_min)
    return {
        "name": F["name"],
        "fails": fails,
        "e_facts": e_facts,
        "chain_count": chain_count,
        "R_min": r_min,
        "N_min": N_min,
        "min_a_req": min_a_req,
        "r_min_sym": r_min_sym,
    }


# ---------------------------------------------------------------------------
# Concrete K8/trace cross-check for E-type non-trivial facts
# ---------------------------------------------------------------------------
def concrete_e_facts_check(F: dict, R_val: int) -> tuple[int, int]:
    """Compare symbolic e_facts dict against exact concrete 1-step evaluation at R = R_val."""
    q, r, s, N_lin = F["q"], F["r"], F["s"], F["N"]
    N = N_lin.eval_at(R_val)
    X = 1 << N
    a = (s * X - r) // q
    m = 3 * a - 2
    M = 3 * a
    h = (m + 1) // 2
    # Build concrete period word w
    w_parts = []
    for t, ln in F["segs"]:
        if t == "1":
            w_parts.append("1" * ln.eval_at(R_val))
        else:
            w_parts.append("0" * ln)
    w = "".join(w_parts)
    L = len(w)
    e_blocks = [0] + [i for i in range(1, L + 1) if w[(i - 1) % L] == "0"]
    e_id_to_blk = {
        ("B" if idx == 0 else ("L" if idx == len(e_blocks) - 1 else f"E{idx}")): blk
        for idx, blk in enumerate(e_blocks)
    }
    assume_d = {((al * a - c) >> K): val for al, c, K, val in F["assume"]}
    memo: dict[tuple[int, int], bool] = {}

    def S(i: int, d: int) -> bool:
        key = (i, d)
        if key in memo:
            return memo[key]
        if i == 0:
            t = v2(d)
            if t == 0:
                res = True
            elif t == 1:
                res = False
            elif d in assume_d:
                res = assume_d[d]
            else:
                raise RuntimeError(f"Unknown d={d} at block 0")
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
                bv = S(j, dd)
                res = bv if st % 2 == 0 else (not bv)
            else:
                res = r_opt
        else:
            t = v2(d)
            if t == 0:
                res = True
            elif t == 1:
                res = False
            elif S(i, d >> 1):
                res = False
            else:
                ee = h + (d >> 1)
                res = not (ee <= m and S(i - 1, ee))
        memo[key] = res
        return res

    # Parse and compare every symbolic fact
    sym = run_symbolic_family(F)
    checked = 0
    mismatches = 0
    for (eid, form_str), sym_val in sym["e_facts"].items():
        # parse "(al a ± c)/2^K"
        body, k_part = form_str.split("/2^")
        K = int(k_part)
        inner = body[1:-1]
        al_str, rest = inner.split("a")
        al = int(al_str)
        if rest.startswith("+"):
            c = -int(rest[1:])
        else:
            c = int(rest[1:])  # minus sign '−'
        d = (al * a - c) >> K
        blk = e_id_to_blk[eid]
        conc_val = S(blk, d)
        checked += 1
        if conc_val != sym_val:
            mismatches += 1
    return checked, mismatches


# ---------------------------------------------------------------------------
# 2. PR #356: Conjecture K60 (v = 5, rho = 2, 29a + 1 = s*2^N, 41 <= N <= 301)
# ---------------------------------------------------------------------------
K60_TABLE = {
    1: (15, lambda R: "1" * (R + 2) + "0" + "1" * R + "0"),
    3: (11, lambda R: "1" * (R + 1) + "0" + "1" * (R + 2) + "000"),
    5: (39, lambda R: "1" * (R + 1) + "00"),
    7: (17, lambda R: "1" * R + "00"),
    9: (55, lambda R: "1" * (R + 1) + "00"),
    11: (21, lambda R: "1" * R + "000"),
    13: (27, lambda R: "1" * (2 * R) + "0" + "1" * R + "0" + "1" * (2 * R) + "00" + "1" * R + "0" + "1" * (R + 2) + "000"),
    15: (43, lambda R: "1" * R + "00011"),
    17: (47, lambda R: "1" * (R + 1) + "00"),
    19: (19, lambda R: "1" * R + "000"),
    21: (41, lambda R: "1" * R + "011"),
    23: (3, lambda R: "1" * R + "000"),
    25: (37, lambda R: "1" * R + "0" + "1" * (R + 1) + "00"),
    27: (31, lambda R: "1" * (R + 3) + "00"),
}


def prove3_k60(m: int, w: str) -> tuple[bool, int]:
    L = len(w)
    v = v2(m + 1)
    h = (m + 1) // 2
    s_z = 0
    while s_z < L and w[L - 1 - s_z] == "0":
        s_z += 1
    g0 = "1" if (v2(h) % 2 == 0) else "0"
    if g0 != w[0]:
        return (False, 0)
    b = L
    gap_abs = [m + 2 if w[j % L] == "1" else m + 1 for j in range(2 * L + 1)]
    base: dict[tuple[int, int], bool] = {}

    def T(j: int, d: int) -> bool:
        key = (j, d)
        res = base.get(key)
        if res is not None:
            return res
        if j == 0:
            r = (v2(d) & 1) == 0
        else:
            if (d & 1) == 0 and T(j, d >> 1):
                r = False
            else:
                g = gap_abs[j - 1]
                sm = g + d
                if (sm & 1) == 0 and (sm >> 1) <= m and T(j - 1, sm >> 1):
                    r = False
                elif g == m + 2 and d == h - 1:
                    r = False
                else:
                    r = True
        base[key] = r
        return r

    for j in range(1, b + 1):
        if ("1" if T(j, h) else "0") != w[j % L]:
            return (False, 0)

    bound = min(2 * s_z - 1, v - 1) if s_z > 0 else -1
    use_g = s_z > 0
    A: dict[int, bool] = {}
    for _ in range(20000):
        memo: dict[tuple[int, int], bool] = {}
        unknown = -1

        def S(i: int, d: int) -> bool:
            nonlocal unknown
            if unknown != -1:
                return False
            key = (i, d)
            res = memo.get(key)
            if res is not None:
                return res
            if i == 0:
                t = v2(d)
                if use_g and t == 0:
                    r = True
                elif use_g and t == 1:
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
                    if unknown != -1:
                        return False
                    g = gap_abs[b + i - 1]
                    sm = g + d
                    if (sm & 1) == 0 and (sm >> 1) <= m and S(i - 1, sm >> 1):
                        r = False
                    elif unknown != -1:
                        return False
                    elif g == m + 2 and d == h - 1:
                        r = False
                    else:
                        r = True
            if unknown != -1:
                return False
            memo[key] = r
            return r

        ok1 = True
        for i in range(1, L + 1):
            x = S(i, h)
            if unknown != -1:
                break
            if ("1" if x else "0") != w[i % L]:
                ok1 = False
                break
        if unknown != -1:
            A[unknown] = T(b, unknown)
            continue
        if not ok1:
            return (False, len(A))
        for d_val, exp in list(A.items()):
            got = S(L, d_val)
            if unknown != -1:
                break
            if got != exp:
                return (False, len(A))
        if unknown != -1:
            A[unknown] = T(b, unknown)
            continue
        return (True, len(A))
    return (False, len(A))


def worker_k60(N: int) -> tuple[int, bool, int]:
    rem = N % 28
    s_exp, w_fn = K60_TABLE[rem]
    X = 1 << N
    assert (s_exp * X - 1) % 29 == 0
    a = (s_exp * X - 1) // 29
    assert a % 2 == 1
    m = 3 * a - 2
    R = (N - 5) // 2
    w = w_fn(R)
    ok, a_sz = prove3_k60(m, w)
    return (N, ok, a_sz)


def main() -> None:
    t0 = time.perf_counter()
    print("# gemini-2 独立検証: PR #348（定理 K58）・PR #350（定理 K34）・PR #352（定理 K33）・PR #360（記号評価器）・PR #356（予想 K60）")
    print("# 実行コマンド: uv run python code/gemini2_verify_symbolic_k33_k34_k58.py > data/gemini2_verify_symbolic_k33_k34_k58.txt")
    print()

    families = [
        (
            {
                "name": "k58",
                "q": 5, "r": 1, "s": 7, "N": Lin(2, 3), "Rpar": 0,
                "segs": [("1", Lin(1, 2)), ("0", 1), ("1", Lin(1, 0)), ("0", 1)],
                "assume": [(2, 14, 0, False)],
            },
            20,  # N = 43
            399,  # prove3 verified max N
        ),
        (
            {
                "name": "k34",
                "q": 5, "r": 1, "s": 3, "N": Lin(2, 3), "Rpar": 1,
                "segs": [("1", Lin(2, 0)), ("0", 1), ("1", Lin(1, 0)), ("0", 2), ("1", Lin(1, 0)), ("0", 2)],
                "assume": [(2, 6, 0, False), (3, 9, 0, True)],
            },
            19,  # N = 41
            401,  # prove3 verified max N
        ),
        (
            {
                "name": "k33-1",
                "q": 1, "r": -1, "s": 3, "N": Lin(2, 1), "Rpar": 0,
                "segs": [("1", Lin(2, 0)), ("0", 1), ("1", Lin(1, 0)), ("0", 1)],
                "assume": [(2, -6, 0, False)],
            },
            10,  # e = 21
            399,  # prove3 verified max e
        ),
        (
            {
                "name": "k33-3",
                "q": 1, "r": -1, "s": 3, "N": Lin(2, 1), "Rpar": 1,
                "segs": [("1", Lin(2, 0)), ("0", 1), ("1", Lin(1, 0)), ("0", 1)],
                "assume": [(2, -6, 0, False)],
            },
            11,  # e = 23
            399,  # prove3 verified max e
        ),
    ]

    print("## 1. 厳密有理数 Python 独立記号評価（PR #360・PR #348・PR #350・PR #352）")
    sym_errors = 0
    for F, R_chk, prove3_max in families:
        res = run_symbolic_family(F)
        checked, mismatches = concrete_e_facts_check(F, R_chk)
        no_gap = res["N_min"] <= prove3_max
        ok_all = (len(res["fails"]) == 0) and (mismatches == 0) and no_gap
        if not ok_all:
            sym_errors += 1
        print(
            f"- {res['name']:5s}: fails={len(res['fails'])}, chains={res['chain_count']:2d}, "
            f"nontriv_E={len(res['e_facts']):2d}, concrete_match={checked - mismatches}/{checked} (at R={R_chk}), "
            f"R_min={res['R_min']} (N/e_min={res['N_min']} <= prove3_max={prove3_max}: gap=0={no_gap})"
        )
        if res["fails"]:
            for fl in res["fails"]:
                print(f"    FAIL: {fl}")
    print()

    # 2. PR #356: Conjecture K60 (41 <= N <= 301, 131 cases)
    t2 = time.perf_counter()
    Ns60 = list(range(41, 302, 2))
    with concurrent.futures.ProcessPoolExecutor(max_workers=10) as ex:
        res60 = list(ex.map(worker_k60, Ns60))
    ok60 = sum(1 for _, ok, _ in res60 if ok)
    maxA60 = max(a_sz for _, _, a_sz in res60)
    print(f"## 2. PR #356（予想 K60: v=5, rho=2, 41 <= N <= 301 全 {len(Ns60)} 個）[{time.perf_counter() - t2:.2f}s]")
    print(f"- 確定: {ok60}/{len(Ns60)}, max |A| = {maxA60}")

    total_errors = sym_errors + (len(Ns60) - ok60)
    print()
    print(f"## 総合検証結果: total_errors = {total_errors}, total_elapsed = {time.perf_counter() - t0:.2f}s")
    if total_errors != 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
