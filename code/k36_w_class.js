/*
 * k36_w_class.js — 定理 K36 の族 m = 3(4^N − 1)/(2^v − 3) − 2 が、w := v2(u+1)（u = (m+1)/2^v）= 2 の類に入ることを確かめる
 *
 * 何を計算するか:
 *   奇数 v = 3, 5, …, VMAX と、q = 2^v − 3 で 4^N ≡ 1 (mod q) となる N（4 の位数の 1〜3 倍、N ≥ (v+3)/2）について、
 *   m の v2(m+1) と w = v2(u+1) を求める。あわせて u mod 8 を出す。
 * 実行方法（リポジトリのルートで）:
 *   node code/k36_w_class.js 15 > data/k36_w_class.txt
 */
'use strict';
const VMAX = +(process.argv[2] || 15);
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const out = ['# 定理 K36 の族の w = v2(u+1)', `# 生成: node code/k36_w_class.js ${VMAX}`, 'v | N | v2(m+1) | w = v2(u+1) | u mod 8'];
let all = true;
for (let v = 3; v <= VMAX; v += 2) {
  const q = 2n ** BigInt(v) - 3n; let o = 1, x = 4n % q; while (x !== 1n) { x = x * 4n % q; o++; }
  for (let N = o; N <= 3 * o; N += o) { if (N < (v + 3) / 2) continue; const a = (4n ** BigInt(N) - 1n) / q, m = 3n * a - 2n, u = (m + 1n) / 2n ** BigInt(v);
    const vv = v2(m + 1n), w = v2(u + 1n); if (vv !== v || w !== 2) all = false; out.push(`${v} | ${N} | ${vv} | ${w} | ${u % 8n}`); }
}
out.push('', all ? 'すべてで v2(m+1) = v、w = 2' : '成り立たないものがある');
console.log(out.join(String.fromCharCode(10)));
