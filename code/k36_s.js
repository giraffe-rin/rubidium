/*
 * k36_s.js — 定理 K36 の族 m = 3(4^N − 1)/(2^v − 3) − 2 で、m+1 の間隔の連の長さ s を K = N − (v+1)/2 の偶奇と比べる
 *
 * 何を計算するか:
 *   指定した (v, N) について、lazy_bigint.js の gapsBig で 2N + 10 ブロックの間隔を求め、
 *   m+1 の極大な連の長さの集合と、m+2 の極大な連の長さの集合を出す。予想 K36d（K 奇数なら s = 1、K 偶数なら s = 2）と比べる。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k36_s.js 3:4 3:6 3:8 5:14 5:28 5:42 7:50 7:100 9:254 11:102 11:204 13:387 13:774 15:234 > data/k36_s.txt
 */
'use strict';
const { gapsBig } = require('./lazy_bigint');
const out = ['# 定理 K36 の族の m+1 の連の長さ s', `# 生成: node --stack-size=65500 code/k36_s.js ${process.argv.slice(2).join(' ')}`,
  'v | N | K = N − (v+1)/2 | K の偶奇 | m+2 の連 | m+1 の連（s）| 予想 K36d と'];
let ok = 0, ng = 0;
for (const arg of process.argv.slice(2)) {
  const [v, N] = arg.split(':').map(Number); const q = 2n ** BigInt(v) - 3n;
  const a = (4n ** BigInt(N) - 1n) / q, m = 3n * a - 2n, K = N - (v + 1) / 2;
  const g = gapsBig(m, 2 * N + 10, 80000000).gaps; const runs = g.match(/1+|0+/g);
  const ones = [...new Set(runs.filter((r, i) => r[0] === '1' && i < runs.length - 1).map(r => r.length))];
  const zeros = [...new Set(runs.filter((r, i) => r[0] === '0' && i < runs.length - 1).map(r => r.length))];
  const pred = K % 2 === 1 ? 1 : 2, good = zeros.length === 1 && zeros[0] === pred; good ? ok++ : ng++;
  out.push(`${v} | ${N} | ${K} | ${K % 2 ? '奇数' : '偶数'} | ${ones.join(',')} | ${zeros.join(',')} | ${good ? '一致' : '不一致'}`);
}
out.push('', `一致 ${ok}、不一致 ${ng}`);
console.log(out.join(String.fromCharCode(10)));
