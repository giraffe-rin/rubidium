/*
 * k59_first_run.js — 定理 K59（v = 3、ρ = 2、N 奇数の族の間隔の列の先頭：s = 3 で 1^{2R} 0、s = 7 で 1^{R+2} 0）を数値で確かめる
 *
 * 何を計算するか:
 *   奇数 N = 9..NMAX について、s（N ≡ 1 (mod 4) で 3、N ≡ 3 (mod 4) で 7）、a = (s·2^N − 1)/5、m = 3a − 2、R = (N − 3)/2 とし、
 *   gapsBig（lazy_bigint.js）で求めた間隔の列の先頭の m+2 の連の長さが、定理 K59 の 2R（s = 3）、R + 2（s = 7）に一致するかを調べる。
 *   あわせて、証明で使う v2(a − s)（s = 3 で 4、s = 7 で 2）を確かめる。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k59_first_run.js 401 > data/k59_first_run.txt
 */
'use strict';
const { gapsBig } = require('./lazy_bigint');
const NMAX = +(process.argv[2] || 401);
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const out = ['# 定理 K59：v = 3、ρ = 2、N 奇数の族の間隔の列の先頭', '# 生成: node --stack-size=65500 code/k59_first_run.js ' + NMAX, 'N | s | R | 先頭の連（実際） | 定理の値 | v2(a − s) | 一致'];
let ok = 0, n = 0;
for (let N = 9; N <= NMAX; N += 2) {
  let s = 1n; while ((s * 2n ** BigInt(N) - 1n) % 5n !== 0n) s += 2n;
  const a = (s * 2n ** BigInt(N) - 1n) / 5n, m = 3n * a - 2n, R = (N - 3) / 2;
  const want = s === 3n ? 2 * R : R + 2, g = gapsBig(m, want + 3, 5e7).gaps, run = g.indexOf('0');
  const u = v2(a - s), good = run === want && u === (s === 3n ? 4 : 2);
  n++; if (good) ok++;
  out.push(`${N} | ${s} | ${R} | ${run} | ${want} | ${u} | ${good ? 'はい' : 'いいえ'}`);
}
out.push('', `${n} 個中 ${ok} 個で一致`);
console.log(out.join('\n'));
