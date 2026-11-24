/*
 * gap_types.js — 開始局面の P の間隔の周期の「型」を集計する（実装 C を使う）
 *
 * 何を計算するか:
 *   v2(m+1) が奇数の各 m（3 ≤ m ≤ M）について、A 行（開始局面 (n,0) が P になる n）の間隔の列 g_j − (m+1)（0 か 1）を、
 *   n ≤ min(NMAX, F·(m+2)) の範囲で求める。
 *   その列が前周期 p ≤ 40、周期 L ≤ 60 で周期的になる最小の (p, L) を探し、周期ブロック（0/1 の列）を「型」とする。
 *   型ごとに m の個数と例を出す。さらに v2(m+1) = 1 の m を v2(3h+1) ごとに分けて出す（h = (m+1)/2）。
 *   周期の判定は範囲内で確かめただけ（[予想] の根拠データ）。
 *
 * 実行方法（リポジトリのルートで）:
 *   node code/gap_types.js 2000 300 3000000 > data/gap_types_m2000.txt
 */
'use strict';

const C = require('./solver_rowtype');
const M = +(process.argv[2] || 2000);
const F = +(process.argv[3] || 300);
const NMAX = +(process.argv[4] || 3000000);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };

const types = {}, byA = {};
for (let m = 3; m <= M; m += 2) {
  const v = v2(m + 1);
  if (v % 2 === 0) continue;
  const N = Math.min(NMAX, F * (m + 2));
  const ty = C.types(m, N);
  const A = []; for (let n = 1; n <= N; n++) if (ty[n] === 0) A.push(n);
  const g = A.map((x, i) => x - (i ? A[i - 1] : 0) - (m + 1));
  let res = null;
  for (let L = 1; L <= 60 && !res; L++) for (let p = 0; p <= 40 && !res; p++) {
    if (g.length - p < 4 * L) break;
    let ok = true; for (let i = p; i + L < g.length; i++) if (g[i] !== g[i + L]) { ok = false; break; }
    if (ok) res = [p, L];
  }
  const key = res ? g.slice(res[0], res[0] + res[1]).join('') + (res[0] ? `（前周期 ${res[0]}）` : '') : '範囲内で周期なし';
  (types[key] = types[key] || []).push(m);
  if (v === 1) { const a = v2(3 * (m + 1) / 2 + 1); const k = `v2(3h+1)=${a} 型 ${key}`; (byA[k] = byA[k] || []).push(m); }
}
const out = ['# 開始局面の P の間隔の周期の型（v2(m+1) が奇数の m）', `# 生成: node code/gap_types.js ${M} ${F} ${NMAX}`,
  '# 型は「g_j − (m+1)」の周期ブロック。10 は交互型。', '', '## 型ごと（多い順）: 個数 | 型 | m の例'];
for (const [k, v] of Object.entries(types).sort((a, b) => b[1].length - a[1].length)) out.push(`${v.length} | ${k} | ${v.slice(0, 12).join(', ')}`);
out.push('', '## v2(m+1) = 1 の m を v2(3h+1) ごとに: 個数 | 分類 | m の例');
for (const k of Object.keys(byA).sort()) out.push(`${byA[k].length} | ${k} | ${byA[k].slice(0, 12).join(', ')}`);
process.stdout.write(out.join('\n') + '\n');
