/*
 * type_runs.js — 型の周期の列を 1 の連と 0 の連に分け、v2(m+1) ごとに連の長さの分布を数える
 *
 * 何を計算するか:
 *   v2(m+1) が奇数の 2 ≤ m ≤ 2^KMAX について、type_vs_t.js の typeOf（300 ブロックから推測）で型を求め、周期の列を取り出す。
 *   周期の列を巡回の輪として見て、1 の連の長さと 0 の連の長さの組を集める（すべて 1 の周期は「1 だけ」として別に数える）。
 *   v = v2(m+1) ごとに、次を出す。
 *     - m の個数、1 の連の長さの分布、0 の連の長さの分布
 *     - 0 の連の長さの最大と (v+1)/2 の比較（前周期の列の 0 の連も別に調べる）
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/type_runs.js 20 > data/type_runs_20.txt
 */
'use strict';
const { typeOf } = require('./type_vs_t');
const KMAX = +(process.argv[2] || 20);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const st = {};
for (let m = 2; m <= 2 ** KMAX; m++) {
  const v = v2(m + 1); if (v % 2 === 0) continue; const key = String(v);
  const s = (st[key] = st[key] || { n: 0, allOne: 0, unk: 0, ones: {}, zeros: {}, maxZ: 0, maxZpre: 0, ex: null }); s.n++;
  const ty = typeOf(m); if (ty === '?') { s.unk++; continue; }
  const [pre, per] = ty.split('|');
  for (const r of ((pre === '-' ? '' : pre) + per + per).match(/0+/g) || []) if (r.length > s.maxZpre) s.maxZpre = r.length; if (!per.includes('0')) { s.allOne++; continue; }
  if (!per.includes('1')) { s.zeros['全部 0'] = (s.zeros['全部 0'] || 0) + 1; continue; }
  const i0 = per.indexOf('0'); let j = i0; while (per[j % per.length] === '0') j++;
  const rot = per.slice(j % per.length) + per.slice(0, j % per.length);   // 1 の連から始め、0 の連で終わる
  for (const r of rot.match(/1+|0+/g)) { const tab = r[0] === '1' ? s.ones : s.zeros; if (r[0] === '0' && r.length > s.maxZ) { s.maxZ = r.length; s.ex = m; } tab[r.length] = (tab[r.length] || 0) + 1; }
}
const fmt = tab => Object.entries(tab).sort((a, b) => +a[0] - +b[0]).map(([k, c]) => `${k}:${c}`).join(' ');
const out = ['# 型の周期の列の連の長さ（v2(m+1) が奇数）', `# 生成: node --stack-size=65500 code/type_runs.js ${KMAX}`,
  '# 「長さ:回数」は、すべての m の周期の列（1 周期分）に現れた連の回数の合計'];
for (const key of Object.keys(st).sort((a, b) => a - b)) { const s = st[key]; if (!s) continue;
  out.push('', `## v2(m+1) = ${key}`, `m の個数: ${s.n}、周期がすべて 1: ${s.allOne}、推測できない: ${s.unk}`, `1 の連: ${fmt(s.ones)}`, `0 の連: ${fmt(s.zeros)}`, `0 の連の最大（周期）: ${s.maxZ}（例 m = ${s.ex}）、前周期から周期 2 回分までの列での最大: ${s.maxZpre}、(v+1)/2 = ${(+key + 1) / 2}`); }
console.log(out.join('\n'));
