/*
 * u_w_table.js — v2(m+1) = v（奇数）の m を w := v2(u+1)（u = (m+1)/2^v）で分け、型の分布を数える
 *
 * 何を計算するか:
 *   v = VMIN, VMIN+2, …, VMAX と奇数 u < UMAX について、m = 2^v u − 1 の型を type_vs_t.js の typeOf（300 ブロック、m < 2^53 の範囲）で求め、
 *   w = v2(u+1) ごとに、型が 1 0^{(v−1)/2}、1 0^{(v+1)/2}、その他の個数を出す。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/u_w_table.js 5 15 4096 > data/u_w_table.txt
 */
'use strict';
const { typeOf } = require('./type_vs_t');
const [VMIN, VMAX, UMAX] = process.argv.slice(2).map(Number);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const out = ['# w = v2(u+1) ごとの型の分布', `# 生成: node --stack-size=65500 code/u_w_table.js ${VMIN} ${VMAX} ${UMAX}`, 'v | w | u の個数 | 1 0^{(v−1)/2} | 1 0^{(v+1)/2} | その他'];
for (let v = VMIN; v <= VMAX; v += 2) {
  const t1 = '-|1' + '0'.repeat((v - 1) / 2), t2 = '-|1' + '0'.repeat((v + 1) / 2); const st = {};
  for (let u = 1; u < UMAX; u += 2) { const m = 2 ** v * u - 1; if (m < 3 || m >= 2 ** 53 / 400) continue; const w = v2(u + 1); const t = typeOf(m, 300);
    const s = (st[w] = st[w] || [0, 0, 0, 0]); s[0]++; if (t === t1) s[1]++; else if (t === t2) s[2]++; else s[3]++; }
  for (const w of Object.keys(st).sort((a, b) => a - b)) out.push(`${v} | ${w} | ${st[w].join(' | ')}`);
}
console.log(out.join(String.fromCharCode(10)));
