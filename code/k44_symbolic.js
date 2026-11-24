/*
 * k44_symbolic.js — 予想 K44 の帰納法の 1 段（周期の終わりの E 型ブロックの評価）を、N によらない形で確かめる（定理 K44 の証明の計算部分）
 *
 * 族：N ≡ 6 (mod 8)、N ≥ 30、a = (3·2^N − 5)/17、m = 3a − 2、M = m + 2 = 3a、h = (m+1)/2、n = (N−2)/4、
 *     周期 w = 1^n 0^z（z = 3（N ≡ 6 (mod 24)）、z = 2（それ以外））。周期の始まりのブロック B から数えて、
 *     ブロック B+1..B+n は O 型（直前の間隔が m+2）、B+n+1..B+n+z は E 型（直前の間隔が m+1）。
 *
 * 何を計算するか:
 *   (1) E 型ブロック B+n+j（j = 1..z）での h の評価を、距離を (P a + Q)/2^K（P, Q, K は N によらない整数）で表して記号的に行う。
 *       偶奇は a ≡ −5/17 (mod 2^30)（N ≥ 30 で成り立つ）から、e ≤ m の判定は a ≥ (3·2^30 − 5)/17 のすべてで同じになることを確かめて決める。
 *       E 型の規則：奇数 d は入る。偶数 d は「d/2 が同じブロックで入らず、かつ e = h + d/2（≤ m のとき）が 1 つ前のブロックで入らない」とき入る。
 *   (2) 1 つ前のブロックが O 型ブロック B+n のときは、e は c(3a−1)/2^k の形（c は 3 以上の奇数）でなければならない（確かめる）。
 *       そこから B までの一本道の鎖の結果を、ログの補題 K44.2 の式で求める：
 *         奇数の点での b（β = 5α + 17c = 2^K b、d = (αa − c)/2^K）は T(b) = (b+15)/2^{r(b)}、r(b) = v2(b+15) で動き、
 *         段数 s = (5 − k) + n + Σ_{i<n} (r(b_i) − 1)、終点の v2 = r(b_n) − 1。結果は「終点の v2 が偶数」と「s が偶数」の一致。
 *       これは n mod 6 だけで決まる（補題 K44.2）。ここでは n ≡ n₀ (mod 6) の代表 n₀ ∈ {7..12} で計算する。
 *       あわせて、補題 K44.2 の条件（b の軌道が周期的で、b ≤ 13、r の平均が 2 以下）を確かめる。
 *   (3) N mod 24 ∈ {6, 14, 22} の 3 つの類のそれぞれで、h の値が w[n+1..n+z−1] = 0、w[n+z] = w[0] = 1 と一致するかを出す。
 *   (4) 照合：引数で与えた N のそれぞれで、同じ評価木の各距離を実際の a で数値的に評価し（O 型ブロックの鎖は一本道の規則を 1 段ずつ）、記号的な値と一致するかを調べる。
 * 実行方法（リポジトリのルートで）:
 *   node code/k44_symbolic.js 30 38 46 54 62 70 > data/k44_symbolic.txt
 */
'use strict';
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const MOD = 2n ** 30n;
const inv17 = (() => { for (let x = 1n; ; x += 2n) if (17n * x % MOD === 1n) return x; })();
const A = ((-5n * inv17) % MOD + MOD) % MOD;   // a mod 2^30
const AMIN = (3n * 2n ** 30n - 5n) / 17n;        // N ≥ 30 での a の最小値
const T = b => { let x = b + 15n, r = 0; while (x % 2n === 0n) { x /= 2n; r++; } return [x, r]; };
const out = ['# 定理 K44 の証明の計算部分（E 型ブロックの評価木と鎖の補題）', '# 生成: node code/k44_symbolic.js ' + process.argv.slice(2).join(' ')];
const fail = msg => { throw new Error(msg); };

// 記号的な数 (P a + Q)/2^K
const norm = x => { let { P, Q, K } = x; while (K > 0n && P % 2n === 0n && Q % 2n === 0n) { P /= 2n; Q /= 2n; K--; } return { P, Q, K }; };
const show = x => `(${x.P}a${x.Q < 0n ? '−' + (-x.Q) : '+' + x.Q})/2^${x.K}`;
function bit(x) {   // 偶奇（1 = 奇数）。2^K で割り切れることも確かめる
  if (x.K + 1n > 30n) fail('K が大きすぎる: ' + show(x));
  const t = ((x.P * A + x.Q) % (2n ** (x.K + 1n)) + 2n ** (x.K + 1n)) % (2n ** (x.K + 1n));
  if (t % (2n ** x.K) !== 0n) fail('整数でない: ' + show(x)); return t / 2n ** x.K;
}
function leM(x) {   // (P a + Q)/2^K ≤ 3a − 2 が a ≥ AMIN のすべてで同じ答えになることを確かめて返す
  const co = x.P - 3n * 2n ** x.K, rhs = -x.Q - 2n ** (x.K + 1n);   // co·a ≤ rhs
  if (co < 0n) { if (co * AMIN <= rhs) return true; fail('比較が a による'); }
  if (co > 0n) { if (co * AMIN > rhs) return false; fail('比較が a による'); }
  return 0n <= rhs;
}
const H = { P: 3n, Q: -1n, K: 1n };

// 補題 K44.2：O 型ブロック B+n に入口 c(3a−1)/2^k で入る鎖の結果（n ≡ n0 (mod 6)）
function chain(c, k, n0, check) {
  if (c < 3n || c % 2n === 0n || c > 13n) fail('c が範囲外: ' + c); if (k > 5n) fail('k > 5');
  // 軌道が周期的であること、b ≤ 13、周期での r の平均 ≤ 2
  const orb = [c]; for (;;) { const [nb] = T(orb[orb.length - 1]); if (nb === c) break; if (orb.includes(nb) || nb > 13n) fail('軌道が c に戻らない: ' + c); orb.push(nb); }
  const rs = orb.map(b => T(b)[1]); if (rs.reduce((x, y) => x + y, 0) > 2 * orb.length) fail('r の平均が 2 を超える');
  let s = Number(5n - k), b = c;
  for (let i = 1; i <= n0; i++) { s += 1; const [nb, r] = T(b); if (i < n0) { s += r - 1; b = nb; } else { const t = r - 1; const g = t % 2 === 0; check.push(`c = ${c}, k = ${k}：軌道 {${orb.join(', ')}}、r = (${rs.join(', ')})、段数の偶奇 ${s % 2}、終点の v2 = ${t}`); return s % 2 === 0 ? g : !g; } }
}

function evalTree(z, n0, numeric) {   // numeric = { a, N } なら数値でも評価して比べる
  const memo = new Map(), notes = [], rows = [];
  let num = null;
  if (numeric) {
    const { a } = numeric, m = 3n * a - 2n, M = 3n * a, h = (m + 1n) / 2n, n = (numeric.N - 2) / 4, bound = Math.min(2 * z - 1, 4);
    const G = d => { const t = v2(d); if (t === 0) return true; if (t <= bound) return t % 2 === 0; fail('G で決まらない'); };
    const Onum = d => { let j = n, s = 0; while (j > 0) { if (d % 2n === 0n) d /= 2n; else { if (d === h - 1n) fail('h − 1'); if ((M + d) / 2n > m) fail('> m'); d = (M + d) / 2n; j--; } s++; } const g = G(d); return s % 2 === 0 ? g : !g; };
    const mm = new Map();
    const En = (j, d) => { const key = j + ':' + d; if (mm.has(key)) return mm.get(key); let r; if (d % 2n === 1n) r = true; else if (En(j, d / 2n)) r = false; else { const e = h + d / 2n; let b = false; if (e <= m) b = j === 1 ? Onum(e) : En(j - 1, e); r = !b; } mm.set(key, r); return r; };
    num = (j, x) => En(j, (x.P * a + x.Q) / 2n ** x.K);
  }
  const E = (j, x0) => {
    const x = norm(x0), key = j + ':' + show(x); if (memo.has(key)) return memo.get(key); let r;
    if (bit(x) === 1n) r = true;
    else if (E(j, { P: x.P, Q: x.Q, K: x.K + 1n })) r = false;
    else {
      const e = norm({ P: 3n * 2n ** x.K + x.P, Q: -(2n ** x.K) + x.Q, K: x.K + 1n });   // h + x/2
      let b = false;
      if (leM(e)) {
        if (j === 1) { // e = c(3a−1)/2^k であること
          if (e.P % 3n !== 0n || e.P / 3n !== -e.Q) fail('入口の形が c(3a−1)/2^k でない: ' + show(e));
          b = chain(e.P / 3n, e.K, n0, notes);
        } else b = E(j - 1, e);
      }
      r = !b;
    }
    memo.set(key, r); rows.push(`ブロック n+${j}、${show(x)}：${r ? '入る' : '入らない'}`);
    if (num && num(j, x) !== r) fail('数値と食い違う: ' + key);
    return r;
  };
  const hs = []; for (let j = 1; j <= z; j++) hs.push(E(j, H) ? 1 : 0);
  return { hs, rows, notes, size: memo.size };
}

let allOk = true;
for (const [res, z, n0] of [[6, 3, 7], [14, 2, 9], [22, 2, 11]]) {
  const r = evalTree(z, n0, null); const want = '0'.repeat(z - 1) + '1'; const ok = r.hs.join('') === want; if (!ok) allOk = false;
  out.push('', `## N ≡ ${res} (mod 24)：z = ${z}、n ≡ ${n0 % 6} (mod 6)`, `E 型ブロック n+1..n+${z} での h：${r.hs.join('')}（w の値は ${want}）→ ${ok ? '一致' : '不一致'}`, `評価木の事実の数：${r.size}`, '鎖（ブロック B+n への入口）：', ...r.notes.map(x => '  ' + x), '評価木：', ...r.rows.map(x => '  ' + x));
}
out.push('', '## 数値との照合');
for (const Ns of process.argv.slice(2)) {
  const N = +Ns; if (N % 8 !== 6 || N < 30) { out.push(`N = ${N}：対象外`); continue; }
  const a = (3n * 2n ** BigInt(N) - 5n) / 17n, z = N % 24 === 6 ? 3 : 2, n = (N - 2) / 4;
  try { const r = evalTree(z, 7 + ((n - 7) % 6 + 6) % 6, { a, N }); out.push(`N = ${N}：評価木の ${r.size} 個の事実がすべて数値と一致、h の列 ${r.hs.join('')}`); }
  catch (e) { allOk = false; out.push(`N = ${N}：${e.message}`); }
}
out.push('', allOk ? 'すべて一致' : '一致しないものがある');
console.log(out.join('\n'));
