/*
 * k51_check.js — 予想 K51 の剰余類（R ≡ 1, P/2 + 1 (mod P)、P = 2·lcm(1, …, (v+1)/2)）の大きい R で、定理 K47b の族のすべての m+2 の連の長さが R かを確かめる
 *
 * 何を計算するか:
 *   引数の各組 v:R:e について、ρ = v + 1、Q = 2^v − 1、r = (2^{v+1} − 1)/3、N = v + ρ(R − 1) + e、σ は Q | σ·2^N + r となる最小の奇数、
 *   a = (σ·2^N + r)/Q、m = 3a − 2 とし、gapsBig（lazy_bigint.js）で J = 4(R + v) + 60 ブロックの間隔を求め、中で完結する m+2 の連がすべて長さ R か、
 *   m+1 の連の長さの範囲を出す。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k51_check.js 9:121:1 9:121:5 9:121:9 11:61:3 11:61:7 11:61:11 > data/k51_check.txt
 */
'use strict';
const { gapsBig } = require('./lazy_bigint');
const out = ['# 予想 K51 の大きい R での照合', '# 生成: node --stack-size=65500 code/k51_check.js ' + process.argv.slice(2).join(' '), 'v | R | e | N | m+2 の連（個数、すべて R か） | m+1 の連の長さの範囲'];
for (const arg of process.argv.slice(2)) {
  const [v, R, e] = arg.split(':').map(Number), rho = v + 1, Q = 2n ** BigInt(v) - 1n, r = (2n ** BigInt(rho) - 1n) / 3n, N = v + rho * (R - 1) + e;
  let sg = 1n; while ((sg * 2n ** BigInt(N) + r) % Q !== 0n) sg += 2n;
  const a = (sg * 2n ** BigInt(N) + r) / Q, m = 3n * a - 2n, J = 4 * (R + v) + 60, g = gapsBig(m, J, 1e8).gaps;
  const ones = [], zeros = []; let i = 0; while (i < J) { let j = i; while (j < J && g[j] === g[i]) j++; if (j < J) (g[i] === '1' ? ones : zeros).push(j - i); i = j; }
  out.push(`${v} | ${R} | ${e} | ${N} | ${ones.length}、${ones.length >= 2 && ones.every(x => x === R) ? 'はい' : 'いいえ'} | ${Math.min(...zeros)}..${Math.max(...zeros)}`);
}
console.log(out.join('\n'));
