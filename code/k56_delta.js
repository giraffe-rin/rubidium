/*
 * k56_delta.js — 定理 K56 の補題（補題 K54.1 の範囲の入口 c では δ(c) = L + (L/ℓ)(d − ℓ) が偶数）を全数で確かめる
 *
 * 何を計算するか:
 *   偶数 ρ = 4..RMAX、z = ρ/2、L = lcm(1, …, z) について、c < 2^{ρ−1} の奇数 c ≥ 3 で 1 の個数 ≤ z のすべてについて、
 *   c の ρ 桁の 2 進の語の基本周期 d、その中の 1 の個数 ℓ（閉路の長さ、補題 K53）を求め、δ(c) = L + (L/ℓ)(d − ℓ) の偶奇を調べる。
 *   あわせて ℓ | L（閉路の長さが L を割る）も確かめる。
 * 実行方法（リポジトリのルートで）:
 *   node code/k56_delta.js 24 > data/k56_delta.txt
 */
'use strict';
const RMAX = +(process.argv[2] || 24);
const out = ['# 定理 K56 の補題：補題 K54.1 の範囲の入口で δ(c) が偶数', '# 生成: node code/k56_delta.js ' + RMAX, 'ρ | L | 入口の個数 | δ が奇数 | ℓ が L を割らない | 周期的な語の個数'];
let allOk = true;
for (let rho = 4; rho <= RMAX; rho += 2) {
  const z = rho / 2; const g = (x, y) => (y ? g(y, x % y) : x); let L = 1; for (let i = 1; i <= z; i++) L = L / g(L, i) * i;
  const mask = 2 ** rho - 1, rot = (x, t) => ((x >>> t) | (x << (rho - t))) & mask;
  let n = 0, odd = 0, nd = 0, per = 0;
  for (let c = 3; c < 2 ** (rho - 1); c += 2) {
    let p = 0; for (let x = c; x > 0; x >>>= 1) p += x & 1; if (p > z) continue; n++;
    let d = rho; for (let dd = 1; dd < rho; dd++) if (rho % dd === 0 && rot(c, dd) === c) { d = dd; break; }
    if (d < rho) per++;
    let l = 0; for (let i = 0; i < d; i++) l += (c >>> i) & 1;
    if (L % l !== 0) nd++;
    else if ((L + (L / l) * (d - l)) % 2 !== 0) odd++;
  }
  if (odd || nd) allOk = false;
  out.push(`${rho} | ${L} | ${n} | ${odd} | ${nd} | ${per}`);
}
out.push('', allOk ? 'すべての入口で δ は偶数、ℓ は L を割る' : '成り立たない入口がある');
console.log(out.join('\n'));
