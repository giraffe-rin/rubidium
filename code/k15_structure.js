/*
 * k15_structure.js — 定理 K15（v2(m+1) = 1、v2(3h+1) = 2k、Q = (m+2+w)/2 奇数 ⇒ 1(10)^k 型）の証明の構造を調べる
 *
 * 何を計算するか（直接の DP、(r, p) が P ⇔ A_r ⊆ {p}）:
 *   (1) 主張の確認：m ≤ MMAX の対象で、n ≤ 2L まで (n, 0) の P の集合が 1(10)^k 型と一致するか（k ごとに数える）。
 *   (2) 各ブロック（1 周期分）で「v2(d) ≤ t なら (r + d, d) が P ⇔ v2(d) が偶数」が成り立つ最大の t。
 *   (3) 各ブロックでの 2^t·w と h + 2^t·w の所属（k = 3 の例）。
 * 実行方法（リポジトリのルートで）: node code/k15_structure.js 8000 > data/k15_structure.txt
 */
'use strict';
const MMAX = +process.argv[2];
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const out = ['# 定理 K15 の証明の構造（直接の DP、m ≤ ' + MMAX + '）', '# 生成: node code/k15_structure.js ' + MMAX];
const st = {}; const blk = []; let shown3 = false; const ex = [];
for (let m = 5; m <= MMAX; m += 4) {
  const h = (m + 1) / 2, t = v2(3 * h + 1); if (t % 2) continue;
  const k = t / 2, w = (3 * h + 1) / 4 ** k, Q = (m + 2 + w) / 2; if (Q % 2 !== 1) continue;
  const L = (2 * k + 1) * (m + 1) + (k + 1), N = 2 * L;
  const typ = new Int32Array(N + 1); typ[0] = -1; const isP = (r, p) => typ[r] === -1 || typ[r] === p;
  for (let r = 1; r <= N; r++) { let c = 0, kk = 0; for (let x = 1; x <= Math.min(m, r) && c < 2; x++) if (isP(r - x, x)) { c++; kk = x; } typ[r] = c === 0 ? -1 : c === 1 ? kk : -2; }
  const Pset = new Set([0]); let x = 0; for (const g of [m + 2, ...Array.from({ length: k }, () => [m + 2, m + 1]).flat()]) { x += g; Pset.add(x); }
  let ok = true; for (let n = 0; n <= N; n++) if (isP(n, 0) !== Pset.has(n % L)) { ok = false; break; }
  st[k] = st[k] || [0, 0]; st[k][0]++; if (ok) st[k][1]++;
  const rows = [0]; for (let n = 1; n <= N; n++) if (typ[n] === -1) rows.push(n);
  if (blk.length < 8) { const T = []; for (let i = 0; i <= 2 * k + 1; i++) { const r = rows[i]; let tt = 99; for (let d = 1; d <= m; d++) if (isP(r + d, d) !== (v2(d) % 2 === 0)) tt = Math.min(tt, v2(d) - 1); T.push((i === 0 ? '' : rows[i] - rows[i - 1] === m + 2 ? 'O' : 'E') + tt); } blk.push(`m=${m} k=${k}：` + T.join(' ')); }
  if (k === 3 && !shown3) { shown3 = true; ex.push(`m=${m} k=3 w=${w}（各行：ブロック、2^t·w（t = 0..5）の所属、h + 2^t·w（t = 0..4）の所属）`);
    for (let i = 0; i <= 2 * k + 1; i++) { const r = rows[i]; let s1 = '', s2 = ''; for (let tt = 0; tt <= 5; tt++) { const d = 2 ** tt * w; s1 += isP(r + d, d) ? 'P' : 'N'; } for (let tt = 0; tt <= 4; tt++) { const d = h + 2 ** tt * w; s2 += d <= m ? (isP(r + d, d) ? 'P' : 'N') : '-'; } ex.push(`  ブロック${i}${i === 0 ? '' : rows[i] - rows[i - 1] === m + 2 ? '(O)' : '(E)'} ${s1}  ${s2}`); } }
}
out.push('', '## (1) 主張の確認（k：対象の数、1(10)^k 型と一致した数）', ...Object.entries(st).map(([k, [n, c]]) => `k=${k}：${n} 個中 ${c} 個`));
out.push('', '## (2) 各ブロックの Blk の範囲 t（O/E は 1 つ前の間隔が m+2/m+1、99 は全範囲、−1 は奇数でも崩れる）', ...blk);
out.push('', '## (3) 2^t·w と h + 2^t·w の所属', ...ex);
console.log(out.join('\n'));
