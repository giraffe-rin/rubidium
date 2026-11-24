"""
gemini2_verify_k60_k61_k62.py — PR #362（定理 K60 全 14 類）・PR #368（命題 K61）・PR #370（命題 K62）の厳密有理数 Python 独立検証

何を計算するか:
  1. PR #362（定理 K60: v = 5, rho = 2, 29a + 1 = s·2^N, N mod 28 の全 14 類）:
     - 厳密有理数（Fraction）による完全独立 Python 記号評価器（補題 Q_z・補題 K33d・回転周期の前周期土台評価・K3 土台照合・
       isLast の K+1 修正・不動点中間点 d = h-1 検査・K.r1 > 0 非不動点検査・明示的下限 R_min / N_min 算出を含む）で、
       全 14 類（k60-1, k60-3, ..., k60-27）を検証する。
     - 全 14 類で fails = 0、土台（K3 または前周期）の失敗 0、かつ N_min <= 301（PR #365 で査読済みの 41 <= N <= 301 の prove3 範囲とギャップ 0）を確認する。
     - 各類について標本 N（61..87）での具体評価と全非自明 E 型事実の一致をクロスチェックする。
  2. PR #368（命題 K61）および PR #370（命題 K62）:
     - 奇数を分母にもつ有理数（Fraction）による越える場面の予測器を Python で独立実装し、以下を検証する:
       (a) PR #370 の実例 (497, 5, 839, 109): 実際 26、有理数規則 26、整数規則 27 を再現。
       (b) 査読で発見した命題 K61・K62 共通の仮定漏れ反例（E = N + γ での u = v2(b' + q c_o s / r) >= N）:
           - u = N 反例: (q, r, s, N) = (5, 1, 83, 5) (a = 531, m = 1591): K61/K62 予測 1、実際 > 1。
           - u > N 反例: (q, r, s, N) = (5, 1, 243, 5) (a = 1555, m = 4663): K61/K62 予測と実際が不一致（v2(inner) = 6 > 5 = N）。
       (c) 仮定「b + 3r != 0、かつ各 E = N + γ 越えで inner != 0 かつ v2(inner) < N」を加えた場合、
           無作為 500 族（r = ±1 および一般の奇数 r ≠ ±1 を含む）で 100% 実際と一致することを確認する。

実行方法（リポジトリのルートで）:
  uv run python code/gemini2_verify_k60_k61_k62.py > data/gemini2_verify_k60_k61_k62.txt
"""
from __future__ import annotations

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


def v2_frac(x: Fraction) -> int:
    assert x.denominator % 2 == 1, f"Even denominator {x}"
    return v2(x.numerator)


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
# 1. Exact-rational symbolic evaluator (supporting Q_z and preSegs base)
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
        if self.r1 == 0:
            assert self.r0 >= rhs, f"Constant constraint {self.r0} >= {rhs} violated"
            return 1
        assert self.r1 > 0, f"Negative slope {self.r1} in >= {rhs}"
        num = rhs - self.r0
        return 1 if num <= 0 else (num + self.r1 - 1) // self.r1

    def __str__(self) -> str:
        if self.r1 == 0:
            return str(self.r0)
        coef = "" if self.r1 == 1 else ("-" if self.r1 == -1 else str(self.r1))
        if self.r0 == 0:
            return f"{coef}R"
        return f"{coef}R+{self.r0}" if self.r0 > 0 else f"{coef}R{self.r0}"


def con(k: int) -> Lin:
    return Lin(0, k)


def run_symbolic(F: dict, is_base: bool = False) -> dict:
    q: int = F["q"]
    r: int = F["r"]
    s: int = F["s"]
    N_lin: Lin = F["N"]
    Rpar: int = F["Rpar"]
    segs = F["preSegs"] if is_base else F["segs"]
    assert r in (1, -1)

    fails: list[str] = []
    min_R_list: list[int] = [1]
    min_a_req = 5

    def require_R(rv: int) -> None:
        if rv > 1:
            min_R_list.append(rv)

    def require_a(av: int) -> None:
        nonlocal min_a_req
        if av > min_a_req:
            min_a_req = av

    def par_of(x: Lin) -> int:
        return ((x.r1 % 2) * Rpar + (x.r0 % 2)) % 2

    # Build E-type graph
    E: list[dict] = [{"id": "B"}]
    for t, ln in segs:
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

    zB = segs[-1][1] if segs[-1][0] == "0" else 0
    vF = v2(3 * r + q)
    q_bound = min(2 * zB - 1, vF - 1) if zB > 0 else 0

    def v2_dist(al: int, c: int, K: int) -> int:
        beta = r * al + q * c
        if beta == 0:
            return 10**9
        v = v2(beta)
        gam = v2(c) if c != 0 else 0
        require_R(N_lin.min_R_for_ge(v + 1 - gam))
        return v - K

    def T_map(b: int) -> tuple[int, int] | None:
        x = b + 3 * r
        if x == 0:
            return None
        t = v2(x)
        return (x >> t, t)

    def check_concrete_point(b: int, c: int, K: int, label: str) -> str:
        powK = 1 << K
        lam = Fraction(b * powK - c * q, r * powK)
        kap = Fraction(-c, powK)
        if lam == Fraction(3, 2) and kap == Fraction(-3, 2):
            return "H"
        if lam < 0 or (lam == 0 and kap <= 0):
            fails.append(f"d <= 0 at {label} (b={b}, c={c}, K={K})")
            return "bad"
        if lam > 0 and kap <= 0:
            require_a(math.floor(-kap / lam) + 1)
        if lam > 3 or (lam == 3 and kap > -4):
            fails.append(f"d > 3a-4 at {label} (b={b}, c={c}, K={K})")
            return "bad"
        if lam < 3 and kap + 4 > 0:
            require_a(math.ceil((kap + 4) / (3 - lam)))
        if lam != Fraction(3, 2):
            bad_a = (Fraction(-3, 2) - kap) / (lam - Fraction(3, 2))
            if bad_a.denominator == 1 and bad_a.numerator >= 1:
                require_a(bad_a.numerator + 1)
        return "ok"

    def check_growing_K_point(b: int, c: int, K_lin: Lin, label: str) -> None:
        lim = Fraction(b, r)
        if not (0 < lim <= 3) or lim == Fraction(3, 2):
            fails.append(f"growing-K invalid lim={lim} at {label} (K={K_lin})")
            return
        if lim == 3:
            cs_r = Fraction(c * s, r)
            if cs_r <= 0:
                fails.append(f"lim=3 cs/r<=0 at {label}")
                return
            nk_diff = N_lin - K_lin
            min_nk = 0
            while cs_r * (1 << min_nk) < 4:
                min_nk += 1
            require_R(nk_diff.min_R_for_ge(min_nk))
        else:
            margin = min(lim, 3 - lim, abs(lim - Fraction(3, 2)))
            min_K = 0
            while abs(Fraction(c * q, 1 << min_K)) >= margin:
                min_K += 1
            require_R(K_lin.min_R_for_ge(min_K))

    memo: dict[tuple[int, int, int, int], bool | None] = {}
    e_facts: dict[tuple[str, str], bool | None] = {}

    def Eval(ei: int, al: int, c: int, K: int) -> bool | None:
        nk = norm_key(al, c, K)
        kk = (ei, nk[0], nk[1], nk[2])
        if kk in memo:
            return memo[kk]
        t = v2_dist(al, c, K)
        if t < 0:
            fails.append(f"Non-integer {fmt(al, c, K)}")
            val = None
        elif t == 0:
            val = True
        elif t == 1:
            val = False
        elif ei == 0 and is_base:
            val = (t % 2 == 0)
        elif ei == 0 and t <= q_bound:
            val = (t % 2 == 0)
        elif ei == 0:
            if nk in assume:
                val = assume[nk]
            else:
                fails.append(f"Unknown at B: {fmt(al, c, K)} (v2={t})")
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
            le = (lam < 3) or (lam == 3 and kap <= -2)
            if lam < 3 and kap + 2 > 0:
                require_a(math.ceil((kap + 2) / (3 - lam)))
            second: bool | None = False
            if le:
                x = E[ei]
                second = Eval(x["prevId"], al2, c2, K2) if x["prev"] == "E" else Chain(x["run"], al2, c2, K2, ei)
            val = None if (first is None or second is None) else (not first and not second)
            e_facts[(E[ei]["id"], fmt(*nk))] = val
        memo[kk] = val
        return val

    def Chain(run_info: dict, al: int, c: int, K0: int, from_ei: int) -> bool | None:
        n_lin: Lin = run_info["len"]
        to_ei: int = run_info["from"]
        label = f"{E[from_ei]['id'] if from_ei >= 0 else 'h'}->{E[to_ei]['id']}:{fmt(al, c, K0)}"
        beta = r * al + q * c
        if beta == 0:
            fails.append(f"beta==0 at {label}")
            return None
        v = v2(beta)
        if v < K0:
            fails.append(f"v<K0 at {label}")
            return None
        gam0 = v2(c) if c != 0 else 0
        require_R(N_lin.min_R_for_ge(v + 1 - gam0))

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
                fails.append(f"b+3r==0 at {label}")
                return None
            b2, t = Tb
            Eexp = K + con(t)
            is_last = (j + con(1)).eq(n_lin)
            rel = Eexp.cmp_inf(Ng)

            if rel < 0:
                require_R((Ng - Eexp).min_R_for_ge(1))
                if b2 == b and not is_last and t in (1, 2) and (K.r1 != 0 or K.r0 > gam + 2):
                    lim1 = n_lin - con(1) - j
                    lim2 = Ng - con(1 + t) - K
                    if t == 2:
                        p_rem = par_of(lim2)
                        if lim2.r1 % 2 != 0:
                            fails.append(f"Non-int slope at {label}")
                            return None
                        lim2 = Lin(lim2.r1 // 2, (lim2.r0 - p_rem) // 2)
                    kst = lim1 if lim1.cmp_inf(lim2) <= 0 else lim2
                    if kst.cmp_inf(con(1)) >= 0:
                        require_R(kst.min_R_for_ge(1))
                        if lim1.cmp_inf(lim2) <= 0:
                            require_R((lim2 - lim1).min_R_for_ge(0))
                        else:
                            require_R((lim1 - lim2).min_R_for_ge(0))
                        K_end = K + kst.scale(t)
                        check_growing_K_point(b, cc, K_end, label + "(seg_end)")
                        K = K_end
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
                        # Exact fix from PR #362: exponent is K.r0 + 1 (not K.r0 + t)!
                        end_form = ((bp - q * cc) // r, cc, K.r0 + 1)
                    break
                steps = steps + con(t)
                K = Eexp
                b = b2
                j = j + con(1)
                continue

            NK1 = Ng - K - con(1)
            if NK1.r1 != 0 or NK1.r0 < 0:
                fails.append(f"NK1 invalid at {label}")
                return None
            nk1 = NK1.r0
            if rel == 0:
                inner = r * b2 + q * co * s
                if inner == 0:
                    fails.append(f"inner==0 at {label}")
                    return None
                u = v2(inner)
                require_R(N_lin.min_R_for_ge(u + 1))
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
                    fails.append(f"off invalid at {label}")
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
                    fails.append(f"post-cross beta even at {label}")
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

    # Check h-runs
    for ru in [x["run"] for x in E if "run" in x]:
        ln = ru["len"]
        cands = [con(1), con(2), con(3), ln - con(2), ln - con(1), ln, Lin(1, -1), Lin(1, 0), Lin(1, 1), Lin(1, 2), Lin(1, 3)]
        seen: set[str] = set()
        for nc in cands:
            if nc.cmp_inf(con(1)) < 0 or nc.cmp_inf(ln) > 0:
                continue
            sk = str(nc)
            if sk in seen:
                continue
            seen.add(sk)
            v_got = Chain({"len": nc, "from": ru["from"]}, 3, 1, 1, -1)
            want = False if nc.eq(ln) else True
            if v_got != want:
                fails.append(f"h-run len={sk} got {v_got}, want {want}")

    # Check E-type h values
    for ei in range(1, len(E)):
        got_h = Eval(ei, 3, 1, 1)
        want_h = True if ei == len(E) - 1 else (E[ei + 1].get("prev") == "O")
        if got_h != want_h:
            fails.append(f"E-type h mismatch at {E[ei]['id']}: got {got_h}, want {want_h}")

    # Check assumption reproduction at L
    for al, c, K, want_v in F["assume"]:
        got_v = Eval(len(E) - 1, al, c, K)
        if got_v != want_v:
            fails.append(f"Assumption {fmt(al, c, K)} mismatch at L: got {got_v}, want {want_v}")

    # K3 check when no preSegs and not is_base
    if not is_base and not F.get("preSegs"):
        for al, c, K, want_v in F["assume"]:
            t = v2_dist(al, c, K)
            if (t % 2 == 0) != want_v:
                fails.append(f"K3 base mismatch for {fmt(al, c, K)}")

    r_min = max(min_R_list)
    if r_min % 2 != Rpar:
        r_min += 1
    while True:
        N_val = N_lin.eval_at(r_min)
        if N_val >= 5 and (s * (1 << N_val) - r) % q == 0:
            a_val = (s * (1 << N_val) - r) // q
            if a_val >= min_a_req:
                break
        r_min += 2
    return {"fails": fails, "R_min": r_min, "N_min": N_lin.eval_at(r_min), "e_facts": e_facts}


def build_k60_families() -> list[dict]:
    """Explicit definitions of all 14 K60 classes (N mod 28) from PR #356/#362."""
    specs = [
        (1, 15, [("1", Lin(1, 2)), ("0", 1), ("1", Lin(1, 0)), ("0", 1)], None, [(2, 30, 0, False), (13, 15, 3, False)]),
        (3, 11, [("1", Lin(1, 1)), ("0", 1), ("1", Lin(1, 2)), ("0", 3)], None, [(2, 22, 0, False), (5, 55, 1, False)]),
        (5, 39, [("1", Lin(1, 1)), ("0", 2)], None, []),
        (7, 17, [("1", Lin(1, 0)), ("0", 2)], None, []),
        (9, 55, [("1", Lin(1, 1)), ("0", 2)], None, []),
        (11, 21, [("1", Lin(1, 0)), ("0", 3)], None, []),
        (13, 27, [("1", Lin(2, 0)), ("0", 1), ("1", Lin(1, 0)), ("0", 1), ("1", Lin(2, 0)), ("0", 2), ("1", Lin(1, 0)), ("0", 1), ("1", Lin(1, 2)), ("0", 3)], None, [(2, 54, 0, False)]),
        (15, 43, [("1", Lin(1, 2)), ("0", 3)], [("1", Lin(1, 0)), ("0", 3)], [(2, 86, 0, False)]),
        (17, 47, [("1", Lin(1, 1)), ("0", 2)], None, []),
        (19, 19, [("1", Lin(1, 0)), ("0", 3)], None, []),
        (21, 41, [("1", Lin(1, 2)), ("0", 1)], [("1", Lin(1, 0)), ("0", 1)], [(2, 82, 0, False)]),
        (23, 3, [("1", Lin(1, 0)), ("0", 3)], None, []),
        (25, 37, [("1", Lin(1, 0)), ("0", 1), ("1", Lin(1, 1)), ("0", 2)], None, []),
        (27, 31, [("1", Lin(1, 3)), ("0", 2)], None, []),
    ]
    out = []
    for rem, s_val, segs, pre, assume in specs:
        Rpar = ((rem - 5) // 2) % 2
        out.append({
            "name": f"k60-{rem}",
            "rem": rem,
            "q": 29, "r": 1, "s": s_val,
            "N": Lin(2, 5), "Rpar": Rpar,
            "segs": segs, "preSegs": pre, "assume": assume,
        })
    return out


# ---------------------------------------------------------------------------
# 2. Independent rational predictor for PR #368 (K61) and PR #370 (K62)
# ---------------------------------------------------------------------------
def predict_k62(q: int, r: int, s: int, N: int, rational: bool = True, check_u_lt_N: bool = False) -> tuple[int | str, int]:
    """Return (predicted_first_run_or_status, actual_first_run)."""
    X = 1 << N
    assert (s * X - r) % q == 0
    a = (s * X - r) // q
    m = 3 * a - 2
    M = 3 * a
    h = (m + 1) // 2
    beta0 = 3 * r + q
    if beta0 == 0 or v2(beta0) >= N:
        return ("out_of_scope", gaps_lazy_big(m, 5).index(0))
    v = v2(beta0)
    if (v - 1) % 2 != 0:
        return (0, gaps_lazy_big(m, 5).index(0))

    def h_in(i: int) -> bool | None:
        c = Fraction(1, 1)
        K = 1
        steps = v - K
        K = v
        b = Fraction(beta0 >> v, 1)
        for j in range(1, i + 1):
            e_exp = N - K
            term = c * s * (1 << e_exp) if e_exp >= 0 else c * s / (1 << (-e_exp))
            dd = (b * a - term) / r
            if dd.denominator == 1:
                d = dd.numerator
                if d == h - 1:
                    return (steps % 2 != 0)
                if (M + d) // 2 > m:
                    return (steps % 2 == 0)
            gam = v2_frac(c)
            co = c / (1 << gam)
            x = b + 3 * r
            if x == 0:
                return None
            t = v2_frac(x)
            b2 = x / (1 << t)
            E = K + t
            steps += 1
            if E < N + gam:
                if j == i:
                    ib = ((t - 1) % 2 == 0)
                    return ib if steps % 2 == 0 else (not ib)
                steps += t - 1
                K = E
                b = b2
                continue
            nk1 = N + gam - K - 1
            cs = (co * s / r) if rational else (co * s * r)
            if E == N + gam:
                inner = b2 + cs * q
                if inner == 0:
                    return None
                u = v2_frac(inner)
                if check_u_lt_N and u >= N:
                    return None  # Violates u < N!
                if j == i:
                    ib = ((nk1 + u) % 2 == 0)
                    return ib if steps % 2 == 0 else (not ib)
                steps += nk1 + u
                c = cs
                K = u
                b = inner / (1 << u)
                continue
            o = E - N - gam
            if j == i:
                ib = (nk1 % 2 == 0)
                return ib if steps % 2 == 0 else (not ib)
            steps += nk1
            c = cs
            K = 0
            b = b2 * (1 << o) + cs * q
            if v2_frac(b) != 0:
                return None
        return None

    pred: int | str = "limit"
    for i in range(1, 2 * N + 20):
        res = h_in(i)
        if res is None:
            pred = "unknown"
            break
        if res is False:
            pred = i
            break
    if isinstance(pred, int):
        g = gaps_lazy_big(m, pred + 1)
        if 0 in g:
            actual = g.index(0)
        else:
            # pred was wrong (too small): find actual first 0 up to pred + 20
            g2 = gaps_lazy_big(m, pred + 20)
            actual = g2.index(0) if 0 in g2 else -1
    else:
        actual = -1
    return (pred, actual)


def main() -> None:
    t0 = time.perf_counter()
    print("# gemini-2 独立検証: PR #362（定理 K60 全 14 類）・PR #368（命題 K61）・PR #370（命題 K62）")
    print("# 実行コマンド: uv run python code/gemini2_verify_k60_k61_k62.py > data/gemini2_verify_k60_k61_k62.txt")
    print()

    # 1. PR #362: all 14 K60 classes
    print("## 1. PR #362（定理 K60: 29a + 1 = s·2^N, 全 14 類の厳密有理数記号評価）")
    k60_errors = 0
    max_N_min = 0
    for F in build_k60_families():
        res = run_symbolic(F, is_base=False)
        base_fails = []
        base_N_min = 0
        if F["preSegs"]:
            bres = run_symbolic(F, is_base=True)
            base_fails = bres["fails"]
            base_N_min = bres["N_min"]
        eff_N_min = max(res["N_min"], base_N_min)
        eff_R_min = (eff_N_min - 5) // 2
        if eff_N_min > max_N_min:
            max_N_min = eff_N_min
        ok = (len(res["fails"]) == 0) and (len(base_fails) == 0) and (eff_N_min <= 301)
        if not ok:
            k60_errors += 1
        print(
            f"- {F['name']:6s} (s={F['s']:2d}, Rpar={F['Rpar']}): fails={len(res['fails'])}, base_fails={len(base_fails)}, "
            f"nontriv_E={len(res['e_facts']):2d}, R_min={eff_R_min:2d} (N_min={eff_N_min:2d} <= 301: gap=0={eff_N_min <= 301})"
        )
        for fl in res["fails"] + base_fails:
            print(f"    FAIL: {fl}")
    print(f"- 定理 K60 全 14 類まとめ: errors = {k60_errors}, max N_min = {max_N_min} (prove3 既査読範囲 41 <= N <= 301 と完全接続)")
    print()

    # 2. PR #368 & #370: K61 / K62 counterexamples + 500 random families with u < N guard
    print("## 2. PR #368（命題 K61）・PR #370（命題 K62）の独立検証と反例確認")
    # (a) PR #370 example (497, 5, 839, 109)
    pR_497, act_497 = predict_k62(497, 5, 839, 109, rational=True, check_u_lt_N=True)
    pI_497, _ = predict_k62(497, 5, 839, 109, rational=False, check_u_lt_N=True)
    print(f"- PR #370 実例 (497, 5, 839, 109): 有理数規則={pR_497}, 整数規則={pI_497}, 実際={act_497}")

    # (b) Counterexamples where u = v2(b' + q*c_o*s/r) >= N
    ce1_pred, ce1_act = predict_k62(5, 1, 83, 5, rational=True, check_u_lt_N=False)
    ce2_pred, ce2_act = predict_k62(5, 1, 243, 5, rational=True, check_u_lt_N=False)
    ce1_guarded, _ = predict_k62(5, 1, 83, 5, rational=True, check_u_lt_N=True)
    ce2_guarded, _ = predict_k62(5, 1, 243, 5, rational=True, check_u_lt_N=True)
    print("- 査読で発見した命題 K61・K62 の仮定漏れ反例（E = N + γ で u = v2(b' + q c_o s / r) >= N）:")
    print(f"  [u = N 反例] (5, 1, 83, 5)  [a=531, m=1591, inner=416, u=5=N, 実v2(a-s)=6]: 現行K61/K62予測={ce1_pred}, 実際={ce1_act} (不一致!), u<Nガード時={ce1_guarded}")
    print(f"  [u > N 反例] (5, 1, 243, 5) [a=1555, m=4663, inner=1216, u=6>N, 実v2(a-s)=5]: 現行K61/K62予測={ce2_pred}, 実際={ce2_act} (不一致!), u<Nガード時={ce2_guarded}")
    ce_confirmed = (ce1_pred != ce1_act) and (ce2_pred != ce2_act) and (ce1_guarded == "unknown") and (ce2_guarded == "unknown")

    # (c) 500 random families (both r = ±1 and general odd r) WITH u < N guard
    seed = 20261124

    def rnd(n: int) -> int:
        nonlocal seed
        seed = (seed * 1103515245 + 12345) % 2147483648
        return seed % n

    rand_tot = rand_ok = rand_unk = 0
    for mode in ("pm1", "general_r"):
        cnt = 0
        while cnt < 250:
            q = 2 * rnd(127) + 3
            r = (1 if rnd(2) else -1) if mode == "pm1" else ((2 * rnd(500) + 1) * (1 if rnd(2) else -1))
            s = 2 * rnd(32) + 1
            N = 25 + rnd(70)
            X = 1 << N
            if (s * X - r) % q != 0:
                continue
            a = (s * X - r) // q
            if a <= 0 or a % 2 == 0:
                continue
            beta0 = 3 * r + q
            if beta0 == 0 or v2(beta0) >= N or (v2(beta0) - 1) % 2 != 0:
                continue
            p_val, act_val = predict_k62(q, r, s, N, rational=True, check_u_lt_N=True)
            cnt += 1
            if p_val == "unknown":
                rand_unk += 1
            else:
                rand_tot += 1
                if p_val == act_val:
                    rand_ok += 1
    print(f"- u < N ガード付き独立ランダム検証（r=±1 250 族 + 一般奇数 r 250 族）: 判定内 {rand_ok}/{rand_tot} 一致（ガード停止 {rand_unk} 族）")

    total_errors = k60_errors + (0 if (pR_497 == 26 and pI_497 == 27 and act_497 == 26) else 1) + (0 if ce_confirmed else 1) + (rand_tot - rand_ok)
    print()
    print(f"## 総合検証結果: total_errors = {total_errors}, elapsed = {time.perf_counter() - t0:.2f}s")
    if total_errors != 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
