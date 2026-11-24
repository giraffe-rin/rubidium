/*
 * k50_general.js — 定理 K47 の族（偶数 ρ ≤ v − 1）で、m+2 の連の直後に m+1 が ρ/2 個以上続く R の剰余類を、E 型ブロックの評価木の記号的な評価で求める（定理 K50）
 *
 * 族：q = 2^v − 2^ρ + 1、r = (2^ρ − 1)/3、q·a + r = s·2^N（s 奇数、N 偶数）、m = 3a − 2、h = (3a − 1)/2、R = ⌈(N − v)/ρ⌉、z = ρ/2。
 *     連 g_B..g_{B+R−1} = m+2、g_{B+R} = m+1 で、ブロック B は 0 か、直前に m+1 が z 個以上続く位置（補題 K48）。
 *
 * 何を計算するか:
 *   (1) E 型ブロック B+R+j（j = 1..z−1）での h を、距離を h の有理数倍 c·(3a−1)/2^k（記号的には (Pa+Q)/2^K）として、E 型の規則で評価する。
 *       偶奇は a ≡ −r/q (mod 2^40)（N ≥ 40 で成り立つ）で決め、e ≤ m の判定は a のすべての大きさで同じになることを確かめる。
 *   (2) 1 つ前が O 型ブロック B+R のときは、入口 c(3a−1)/2^k から B までの一本道の鎖を、奇数の点での b（T(b) = (b + 3r)/2^{v2(b+3r)}）の軌道を
 *       R 段たどって求める（定理 K47 の記述の一般化）。c = 1 の入口は h の鎖の途中なので、h ∉ S_{B+R}（定理 K47、補題 K48）から決める。
 *       鎖の条件を満たさない（v2(β) が N に近づく）ときは値を「不明」とし、評価は 3 値（入る・入らない・不明）で行う（e の項を先に評価する）。
 *       鎖の条件を確かめる：各 b < 3r（または軌道がそこに入る）、各奇数の点で v2(β) + v + 2 < v + ρ(R − 1) + 1 ≤ N、終点の v2 ≤ ρ − 1（ブロック B で分かる範囲）。
 *   (3) R = R0..R0 + 2P − 1（P は現れた軌道の周期の最小公倍数の 2 倍）で、h ∉ S_{B+R+j}（j = 1..z−1）となる R を求め、R mod P の剰余類として出す。
 *       鎖の結果（段数の偶奇と終点の b）は R について周期 P をもつ（軌道に入った後）ので、これで R ≥ R0 のすべてが決まる。2 周期分で一致することも確かめる。
 * 実行方法（リポジトリのルートで）:
 *   node code/k50_general.js 5:4 7:4 9:4 11:4 13:4 7:6 9:6 11:6 13:6 9:8 11:8 13:8 11:10 13:10 13:12 > data/k50_general.txt
 */
'use strict';
const out = ['# 定理 K50：m+2 の連の直後に m+1 が ρ/2 個以上続く R の剰余類', '# 生成: node code/k50_general.js ' + process.argv.slice(2).join(' ')];
const fail = msg => { throw new Error(msg); };
for (const arg of process.argv.slice(2)) {
  const [v, rho] = arg.split(':').map(Number), z = rho / 2;
  const q = 2n ** BigInt(v) - 2n ** BigInt(rho) + 1n, r = (2n ** BigInt(rho) - 1n) / 3n, R3 = 3n * r;
  const MOD = 2n ** 40n; const inv = (x => { let y = 1n; for (let i = 0; i < 7; i++) y = (y * (2n - x * y)) % MOD; return ((y % MOD) + MOD) % MOD; })(((q % MOD) + MOD) % MOD);   // ニュートン法による 2 進の逆元
  if ((((q % MOD) + MOD) % MOD) * inv % MOD !== 1n) fail('逆元の計算に失敗');
  const A = ((-r * inv) % MOD + MOD) % MOD;   // a mod 2^40
  const T = b => { let x = b + R3, k = 0; while (x % 2n === 0n) { x /= 2n; k++; } return [x, k]; };
  const norm = x => { let { P, Q, K } = x; while (K > 0n && P % 2n === 0n && Q % 2n === 0n) { P /= 2n; Q /= 2n; K--; } return { P, Q, K }; };
  const show = x => `(${x.P}a${x.Q < 0n ? '−' + (-x.Q) : '+' + x.Q})/2^${x.K}`;
  const bit = x => { if (x.K + 1n > 40n) fail('K が大きすぎる'); const M2 = 2n ** (x.K + 1n); const t = ((x.P * A + x.Q) % M2 + M2) % M2; if (t % (2n ** x.K) !== 0n) fail('整数でない ' + show(x)); return t / 2n ** x.K; };
  const leM = x => { const co = x.P - 3n * 2n ** x.K, rhs = -x.Q - 2n ** (x.K + 1n); if (co < 0n) return true; if (co > 0n) return false; return 0n <= rhs; };   // a は十分大きい
  const H = { P: 3n, Q: -1n, K: 1n };
  const cycLens = new Set();
  // 鎖：ブロック B+R に入口 c(3a−1)/2^k で入り、B まで R 回の奇数の段。戻り値はブロック B+R で入るか
  function chain(c, k, R) {
    if (c === 1n) { // h の鎖の途中：(3a−1)/2^k は h を k−1 回半分にしたもの（k ≤ v のとき偶数の段だけ）
      if (k < 1n || k > BigInt(v)) fail('c = 1 で k が範囲外'); const hIn = false; return (k - 1n) % 2n === 0n ? hIn : !hIn; }
    if (c < 0n || c % 2n === 0n || k > BigInt(v)) fail('入口が範囲外 c = ' + c + ', k = ' + k);
    let s = Number(BigInt(v) - k), b = c, Kodd = v, seen = new Map();
    for (let i = 1; i <= R; i++) {
      if (b >= R3) return null;   // (M+d)/2 ≤ m を保証できない：値は不明とする
      if (Kodd + v + 2 >= v + rho * (R - 1) + 1) return null;   // 鎖の条件を満たさない：値は不明とする
      const [nb, t] = T(b); s += 1;
      if (i < R) { s += t - 1; Kodd += t; b = nb; }
      else { const vend = t - 1; if (vend > rho - 1) fail('終点の v2 が大きい'); const inB = vend % 2 === 0; return s % 2 === 0 ? inB : !inB; }
    }
  }
  function orbitLen(c) { const pos = new Map(); let b = c, i = 0; while (!pos.has(b)) { pos.set(b, i++); b = T(b)[0]; } return i - pos.get(b); }
  function zerosAfter(R) {   // h ∉ S_{B+R+j}（j = 1..z−1）か
    const memo = new Map();
    const E = (j, x0) => {
      const x = norm(x0), key = j + ':' + show(x); if (memo.has(key)) return memo.get(key); let res;
      if (bit(x) === 1n) res = true;
      else {   // 3 値：true / false / null（不明）。e の項を先に評価し、どちらかが true なら false
        const e = norm({ P: 3n * 2n ** x.K + x.P, Q: -(2n ** x.K) + x.Q, K: x.K + 1n });
        let bb = false;
        if (leM(e)) {
          if (j === 1) { if (e.P % 3n !== 0n || e.P / 3n !== -e.Q) fail('入口の形が c(3a−1)/2^k でない ' + show(e)); const c = e.P / 3n; if (c !== 1n) cycLens.add(orbitLen(c)); bb = chain(c, e.K, R); }
          else bb = E(j - 1, e);
        }
        if (bb === true) res = false;
        else { const aa = E(j, { P: x.P, Q: x.Q, K: x.K + 1n }); res = aa === true ? false : (aa === null || bb === null) ? null : true; }
      }
      memo.set(key, res); return res;
    };
    for (let j = 1; j <= z - 1; j++) if (E(j, H) !== false) return false;   // 不明も「示せない」とする
    return true;
  }
  try {
    const R0 = 3 * v;   // 十分大きい R から
    const g = (x, y) => (y ? g(y, x % y) : x); const lcmOf = () => { let l = 1; for (const L of cycLens) l = l / g(l, L) * L; return 2 * l; };
    zerosAfter(R0); let P = lcmOf(), res;
    for (;;) { res = []; for (let R = R0; R < R0 + 2 * P; R++) res.push(zerosAfter(R)); const P2 = lcmOf(); if (P2 === P) break; P = P2; }   // 現れた軌道の周期が増えなくなるまで
    let per = true; for (let i = 0; i < P; i++) if (res[i] !== res[i + P]) per = false;
    for (const L of cycLens) if (P % L !== 0) per = false;
    const good = []; for (let i = 0; i < P; i++) if (res[i]) good.push((R0 + i) % P);
    good.sort((x, y) => x - y);
    out.push(`v = ${v}、ρ = ${rho}（q = ${q}、r = ${r}、z = ${z}）：軌道の周期 {${[...cycLens].join(', ')}}、P = ${P}、2 周期で一致: ${per ? 'はい' : 'いいえ'}、`
      + `m+1 が z 個以上続く R mod ${P}（R ≥ ${R0}）: ${good.length ? '{' + good.join(', ') + '}' : 'なし'}`);
  } catch (e) { out.push(`v = ${v}、ρ = ${rho}：${e.message}`); }
}
console.log(out.join('\n'));
