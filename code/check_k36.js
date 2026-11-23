/*
 * check_k36.js — 定理 K36（奇数 v ≥ 3、m = 3(4^N − 1)/(2^v − 3) − 2 では、m+2 の間隔の極大な連はどれも長さ N − (v−1)/2）を確かめる
 *
 * 何を計算するか:
 *   奇数 v = 3, 5, …, VMAX について q = 2^v − 3、4 の q を法とする位数 o とし、N = o, 2o, 3o（N ≤ NMAX、N ≥ (v+3)/2）で
 *   m = 3(4^N − 1)/q − 2 を作る。lazy_bigint.js の gapsBig で J = 4N + 40 ブロックの間隔を求め、次を調べる。
 *     - v2(m+1) = v
 *     - 間隔の列の m+2 の極大な連（最後の、途中で切れている連を除く）がすべて長さ N − (v−1)/2 で、最初の連はブロック 0 から始まる
 *     - m+1 の連はすべて長さ 1 以上 (v+1)/2 以下（定理 K32）
 *   あわせて、v = 3, 5 の小さい N では block_rule.js の nextBlock で、証明の性質 (Z)（m+1 の連の直後で間隔が m+2 のブロック B で、
 *   y_i = 2a − 4^i ∉ S_B（1 ≤ i ≤ K）、y_0 ∈ S_B、K = N − (v+1)/2）を確かめる。
 * 実行方法（リポジトリのルートで）:
 *   node code/check_k36.js 13 400 > data/k36_check.txt
 */
'use strict';
const { gapsBig } = require('./lazy_bigint');
const { nextBlock } = require('./block_rule');
const VMAX = +(process.argv[2] || 13), NMAX = +(process.argv[3] || 400);
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const out = ['# 定理 K36 の確認', `# 生成: node code/check_k36.js ${VMAX} ${NMAX}`,
  'v | N | m の桁数 | v2(m+1) | 調べたブロック数 | m+2 の連の長さ（N − (v−1)/2 と比べる）| m+1 の連の長さ | 判定'];
let ok = 0, ng = 0;
for (let v = 3; v <= VMAX; v += 2) {
  const q = 2n ** BigInt(v) - 3n; let o = 1, x = 4n % q; while (x !== 1n) { x = x * 4n % q; o++; }
  for (let N = o; N <= NMAX && N <= 3 * o; N += o) {
    if (N < (v + 3) / 2) continue;
    const a = (4n ** BigInt(N) - 1n) / q, m = 3n * a - 2n, J = 4 * N + 40;
    const g = gapsBig(m, J, 20000000).gaps; const runs = g.match(/1+|0+/g);
    const ones = runs.filter((r, i) => r[0] === '1' && i < runs.length - 1).map(r => r.length);
    const zeros = runs.filter((r, i) => r[0] === '0' && i < runs.length - 1).map(r => r.length);
    const want = N - (v - 1) / 2;
    const good = v2(m + 1n) === v && g[0] === '1' && ones.length > 0 && ones.every(l => l === want) && zeros.every(l => l >= 1 && l <= (v + 1) / 2);
    good ? ok++ : ng++;
    out.push(`${v} | ${N} | ${m.toString().length} | ${v2(m + 1n)} | ${J} | ${[...new Set(ones)].join(',')}（${want}）| ${[...new Set(zeros)].join(',')} | ${good ? '成り立つ' : '成り立たない'}`);
  }
}
out.push('', `判定：成り立つ ${ok}、成り立たない ${ng}`, '', '## 性質 (Z) の確認（nextBlock）', 'v | N | m | 調べた始まりのブロックの数 | 違反');
for (const [v, N] of [[3, 2], [3, 4], [3, 6], [5, 14]]) {
  const q = 2 ** v - 3, a = (4 ** N - 1) / q, m = 3 * a - 2, K = N - (v + 1) / 2, h = (m + 1) / 2;
  let pv = null, prevG = null, nb = 0, bad = 0;
  for (let j = 0; j < 6 * N + 10; j++) {
    const cur = nextBlock(m, pv);
    const isStart = cur.g === m + 2 && (j === 0 || prevG === m + 1);
    if (isStart) { nb++; for (let i = 1; i <= K; i++) if (cur.S[2 * a - 4 ** i] === 1) bad++; if (cur.S[2 * a - 1] !== 1) bad++; }
    prevG = cur.g; pv = cur;
  }
  out.push(`${v} | ${N} | ${m} | ${nb} | ${bad}`);
}
console.log(out.join(String.fromCharCode(10)));
