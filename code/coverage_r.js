/*
 * coverage_r.js — coverage2.js の集計で型が決まらなかった m について、漸化式 R の状態の繰り返しまで計算して型を決める
 *
 * 何を計算するか:
 *   5 ≤ m ≤ MMAX の各 m について、coverage2.js と同じ規則（K4、K27/K28、K19、K20、K26、K29、K38、K33a、K35、K16）で型が決まるかを調べ、
 *   決まらない m について block_rule.js の periods（R の状態 (S_j, g_j) が初めて繰り返すまで計算）で前周期と周期を求める。
 *   R は決定的なので、状態が繰り返せば以後の間隔の列は周期的で、型が確定する（主張 H(j)、定理 K3 を前提にした計算による証明）。
 *   出力: v2(m+1) ごとの、規則で決まった個数、R の繰り返しで決まった個数、合計。R で決めた m の前周期・周期のブロック数の最大。
 * 実行方法（リポジトリのルートで）:
 *   node code/coverage_r.js 20000 > data/coverage_r_20000.txt
 */
'use strict';
const fs = require('fs');
const v2 = x => { if (x === 0) return 99; let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const MMAX = +(process.argv[2] || 20000);
const { periods } = require('./block_rule');
const byA = new Map(); let ncls = 0;
for (const f of fs.readdirSync('data').filter(f => /^(affine_certificates_v\d+_T\d+|affine_refine_v\d+_T\d+|affine3_v\d+_T\d+|affine3_refine_v\d+)\.txt$/.test(f))) {
  let sec = '';
  for (const l of fs.readFileSync('data/' + f, 'utf8').split(/\r?\n/)) {
    if (/^## (証明できた類|新しく証明できた類)/.test(l)) { sec = 'ok'; continue; }
    if (l.startsWith('##')) { sec = ''; continue; }
    const mm = l.match(/^m ≡ (\d+) \(mod (\d+)\) \| (\d+) \|/);
    if (sec === 'ok' && mm) { const A = +mm[2], B = +mm[1] % A, Mmin = +mm[3]; if (!byA.has(A)) byA.set(A, new Map()); const t = byA.get(A); if (!t.has(B) || t.get(B) > Mmin) t.set(B, Mmin); ncls++; }
  }
}
const k16 = m => { for (const [A, t] of byA) { const Mmin = t.get(m % A); if (Mmin !== undefined && m >= Mmin) return true; } return false; };
function k26(m) {
  if (v2(m + 1) !== 3) return false; const u = (m + 1) / 8; if (v2(5 * u + 1) !== 1) return false;
  const p = v2((11 * u + 1) / 2); if (p === 1) return m >= 71; return p % 2 === 0 && p <= 30;
}
const fam33 = new Set(), fam35 = new Set();
for (let e = 2; 9 * 2 ** e + 1 <= MMAX; e += 2) fam33.add(9 * 2 ** e + 1);
for (let k = 2; (3 * 16 ** k - 13) / 5 <= MMAX; k++) fam35.add((3 * 16 ** k - 13) / 5);
const by = {}; const uncovered = {}; let maxPre = 0, maxPer = 0;
for (let m = 5; m <= MMAX; m++) {
  const v = v2(m + 1); let why = null;
  if (v % 2 === 0) why = 'K4';
  else if (m === 7 || m === 9) why = 'K27/K28';
  else if (v === 1 && v2((m + 1) / 2 - 1) % 2 === 1) why = 'K19';
  else if (v === 3 && v2(5 * m + 13) >= 6 && v2(5 * m + 13) % 2 === 0) why = 'K20';
  else if (k26(m)) why = 'K26';
  else if (v >= 5 && ((m + 1) / 2 ** v) % 4 === 1) why = 'K29';
  else if (v >= 5) { const w = v2((m + 1) / 2 ** v + 1); if ((w % 2 === 1 && w >= 3 && w <= v - 2) || w >= v + 1) why = 'K38'; }
  if (!why && fam33.has(m)) why = 'K33a';
  if (!why && fam35.has(m)) why = 'K35';
  if (!why && k16(m)) why = 'K16';
  const k = v % 2 === 0 ? '偶数' : String(v);
  by[k] = by[k] || { n: 0, ok: 0, src: {} }; by[k].n++;
  if (why) { by[k].ok++; by[k].src[why] = (by[k].src[why] || 0) + 1; }
  else { const r = periods(m); why = 'R'; by[k].ok++; by[k].src[why] = (by[k].src[why] || 0) + 1; (uncovered[k] = uncovered[k] || []).push(m); if (r.preBlocks > maxPre) maxPre = r.preBlocks; if (r.periodBlocks > maxPer) maxPer = r.periodBlocks; }
}
let tot = 0, totok = 0; for (const s of Object.values(by)) { tot += s.n; totok += s.ok; }
const out = ['# 既存の定理と R の状態の繰り返しで型が決まる m の集計', `# 生成: node code/coverage_r.js ${MMAX}`, `# K16 の類（3 値の証明書を含む）: ${ncls} 個`, `全体：${tot} 個のうち ${totok} 個（${(totok / tot).toFixed(4)}）`, '', '## v2(m+1) ごと: 区分 | m の個数 | 決まっている個数（割合）| 内訳'];
for (const k of Object.keys(by).sort((a, b) => (a === '偶数' ? -1 : b === '偶数' ? 1 : a - b))) {
  const s = by[k]; out.push(`v2(m+1) = ${k} | ${s.n} | ${s.ok}（${(s.ok / s.n).toFixed(4)}）| ${Object.entries(s.src).map(([w, c]) => `${w}: ${c}`).join('、')}`);
}
out.push('', `R の繰り返しで決めた m の、前周期のブロック数の最大: ${maxPre}、周期のブロック数の最大: ${maxPer}`, '', '## R の繰り返しで決めた m（v2(m+1) ごとに小さい順に最大 30 個）');
for (const k of Object.keys(uncovered).sort((a, b) => a - b)) out.push(`v2(m+1) = ${k}（${uncovered[k].length} 個）: ${uncovered[k].slice(0, 30).join(', ')}`);
console.log(out.join(String.fromCharCode(10)));
