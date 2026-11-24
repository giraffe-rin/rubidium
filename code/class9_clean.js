/*
 * class9_clean.js — m ≡ 9 (mod 32) で前周期のない族 m = 3a − 2、a = (2^N − 1)/q（q = 23, 119）の型を求め、予想 K40 と照合する
 *
 * 何を計算するか:
 *   q = 23（N は 11 の倍数、N ≥ 22）と q = 119（N は 24 の倍数）について、a = (2^N − 1)/q、m = 3a − 2 とし、
 *   lazy_bigint.js の gapsBig で 3N + 30 ブロックの間隔を求め、次の予想 K40 の型の 3 回分と一致するかを調べる。
 *     q = 23：前周期なし、周期 1^{⌊N/2⌋−1} 0
 *     q = 119：前周期なし、周期 1^{N/2−2} 0
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/class9_clean.js 242 240 > data/class9_clean.txt
 */
'use strict';
const { gapsBig } = require('./lazy_bigint');
const [N23, N119] = process.argv.slice(2).map(Number);
const out = ['# m ≡ 9 (mod 32) の前周期のない族と予想 K40 の照合', `# 生成: node --stack-size=65500 code/class9_clean.js ${N23} ${N119}`, 'q | N | m の桁数 | m mod 32 | 一致'];
let ok = 0, ng = 0;
for (const [q, o, Nmax, ones] of [[23, 11, N23, N => Math.floor(N / 2) - 1], [119, 24, N119, N => N / 2 - 2]]) {
  for (let N = 2 * o > 22 ? o : 2 * o; N <= Nmax; N += o) {
    if (q === 23 && N < 22) continue;
    const a = (2n ** BigInt(N) - 1n) / BigInt(q), m = 3n * a - 2n, per = '1'.repeat(ones(N)) + '0';
    const g = gapsBig(m, 3 * per.length, 50000000).gaps; const good = g === per.repeat(3) && m % 32n === 9n; good ? ok++ : ng++;
    out.push(`${q} | ${N} | ${m.toString().length} | ${m % 32n} | ${good ? '一致' : '不一致'}`);
  }
}
out.push('', `一致 ${ok}、不一致 ${ng}`);
console.log(out.join(String.fromCharCode(10)));
