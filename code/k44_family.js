/*
 * k44_family.js — 予想 K44（v = 5、w = 4 の類の族）を照合する
 *
 * 何を計算するか:
 *   N ≡ 6 (mod 8)、30 ≤ N ≤ NMAX で a = (3·2^N − 5)/17、m = 3a − 2 とし、
 *   v2(m+1)、w = v2(u+1)（u = (m+1)/2^5）と、BigInt 版の遅延評価 gapsBig（lazy_bigint.js）で求めた最初の J ブロックの間隔を出す。
 *   予想 K44 の型（前周期なし、周期 1^{(N−2)/4} 0^z、z = 3（N ≡ 6 (mod 24)）、z = 2（それ以外））の 3 回分以上と、間隔の列が一致するかを調べる。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k44_family.js 398 > data/k44_family.txt
 */
'use strict';
const { gapsBig } = require('./lazy_bigint');
const NMAX = +(process.argv[2] || 398);
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const out = ['# 予想 K44：a = (3·2^N − 5)/17、m = 3a − 2（N ≡ 6 (mod 8)）', '# 生成: node --stack-size=65500 code/k44_family.js ' + NMAX,
  'N | v2(m+1) | w | 予想の周期 | 照合したブロック数 | 一致'];
let bad = 0, cnt = 0;
for (let N = 30; N <= NMAX; N += 8) {
  const a = (3n * 2n ** BigInt(N) - 5n) / 17n, m = 3n * a - 2n, u = (m + 1n) / 32n;
  const z = N % 24 === 6 ? 3 : 2, per = '1'.repeat((N - 2) / 4) + '0'.repeat(z);
  const J = 3 * per.length + 20, g = gapsBig(m, J).gaps, want = per.repeat(Math.ceil(J / per.length)).slice(0, J);
  const ok = v2(m + 1n) === 5 && v2(u + 1n) === 4 && g === want; cnt++; if (!ok) bad++;
  out.push(`${N} | ${v2(m + 1n)} | ${v2(u + 1n)} | 1^${(N - 2) / 4} 0^${z} | ${J} | ${ok ? 'はい' : 'いいえ'}`);
}
out.push('', `${cnt} 個中 ${cnt - bad} 個で一致`);
console.log(out.join('\n'));
