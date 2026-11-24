/*
 * deep_classes.js — 型が簡単な規則で決まらない類の調査
 *
 * 何を計算するか:
 *   (1) v2(m+1) = v（v = 9, 11）、u ≡ 3 (mod 8)（w = v2(u+1) = 2）の u < UMAX について、型（type_vs_t.js の typeOf、300 ブロック）を求め、
 *       K = 4..12 ごとに、u mod 2^K の類のうち型が 1 つだけの類の個数を出す。
 *   (2) v2(m+1) = 1 で x = v2(h−1) が偶数の m < 2·HMAX について、x と y = v2(s+1)（s = (h−1)/2^x）の組ごとに、m の個数、型の種類の数、多い型を出す。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/deep_classes.js 16384 200000 > data/deep_classes.txt
 */
'use strict';
const { typeOf } = require('./type_vs_t');
const [UMAX, HMAX] = process.argv.slice(2).map(Number);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const out = ['# 型が簡単な規則で決まらない類の調査', `# 生成: node --stack-size=65500 code/deep_classes.js ${UMAX} ${HMAX}`, '', '## (1) w = 2：u mod 2^K の類のうち型が 1 つだけの類'];
for (const v of [9, 11]) {
  const ty = {}; for (let u = 3; u < UMAX; u += 8) ty[u] = typeOf(2 ** v * u - 1, 300);
  const line = []; for (let K = 4; K <= 12; K++) { const M = 2 ** K; let det = 0, tot = 0; for (let r = 3; r < M; r += 8) { const s = new Set(); for (let u = r; u < UMAX; u += M) s.add(ty[u]); tot++; if (s.size === 1) det++; } line.push(`K=${K}: ${det}/${tot}`); }
  out.push(`v=${v}（u < ${UMAX}）: ${line.join('、')}`);
}
out.push('', '## (2) v2(m+1) = 1、x = v2(h−1) 偶数：x, y = v2(s+1) | m の個数 | 型の種類 | 多い型（3 つまで）');
const st = {};
for (let h = 3; h < HMAX; h += 2) { if (v2(h - 1) % 2 === 1) continue; const x = v2(h - 1), s = (h - 1) / 2 ** x, key = `x=${x}, y=${v2(s + 1)}`; const t = typeOf(2 * h - 1, 300); (st[key] = st[key] || {}); st[key][t] = (st[key][t] || 0) + 1; }
for (const k of Object.keys(st).sort((a, b) => { const p = s => s.match(/\d+/g).map(Number); const [a1, a2] = p(a), [b1, b2] = p(b); return a1 - b1 || a2 - b2; })) {
  const e = Object.entries(st[k]).sort((a, b) => b[1] - a[1]); out.push(`${k} | ${e.reduce((a, b) => a + b[1], 0)} | ${e.length} | ${e.slice(0, 3).map(([t, c]) => `${t}: ${c}`).join('、')}`);
}
console.log(out.join(String.fromCharCode(10)));
