/*
 * v5_odd_N.js — 定理 K47 の族の v = 5、ρ = 2（q = 29、r = 1）で N が奇数のときの型を、N mod 28（s が一定になる類）ごとに調べ、prove3 で確定させる（予想 K60）
 *
 * 何を計算するか:
 *   奇数 N = N0..N1 について、s は 29 | s·2^N − 1 となる最小の正の奇数（N mod 28 で決まる）、a = (s·2^N − 1)/29（a が奇数のものだけ）、m = 3a − 2、R = (N − 5)/2。
 *   gapsBig（lazy_bigint.js）で J = max(800, 16N) ブロックまで計算して型（前周期、周期）を推測し（前周期は列の半分以下、周期が 4 回以上見えるもの）、
 *   prove3（period_induction.js、補題 K33d の選択肢つき）で確定させる。
 *   型の周期を、m+2 の連の長さを R + δ（δ は整数）で書いた形にして、類ごとに、すべての N で形（δ の列と m+1 の連）が同じかを調べる。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/v5_odd_N.js 41 301 > data/v5_odd_N.txt
 */
'use strict';
const { gapsBig } = require('./lazy_bigint');
const { prove3 } = require('./period_induction');
const [N0, N1] = process.argv.slice(2).map(Number);
function guess(g) {
  for (let L = 1; 3 * L <= g.length; L++) for (let p = 0; 2 * p <= g.length && p + 3 * L <= g.length; p++) {
    let ok = true; for (let i = p; i + L < g.length; i++) if (g[i] !== g[i + L]) { ok = false; break; }
    if (ok && p + 4 * L <= g.length) return [p, L];
  }
  return null;
}
const q = 29n, byClass = new Map();
for (let N = N0 % 2 ? N0 : N0 + 1; N <= N1; N += 2) {
  let s = 1n; while ((s * 2n ** BigInt(N) - 1n) % q !== 0n) s += 2n;
  const a = (s * 2n ** BigInt(N) - 1n) / q; const c = N % 28;
  if (!byClass.has(c)) byClass.set(c, []);
  if (a % 2n === 0n) { byClass.get(c).push({ N, s, note: 'a が偶数（対象外）' }); continue; }
  const m = 3n * a - 2n, R = (N - 5) / 2, J = Math.max(800, 16 * N), g = gapsBig(m, J, 1e8).gaps, pl = guess(g);
  if (!pl) { byClass.get(c).push({ N, s, note: '型を推測できない' }); continue; }
  const pre = g.slice(0, pl[0]), w = g.slice(pl[0], pl[0] + pl[1]);
  const r = prove3(m, pre, w, 20000, 50000000, { k33d: true });
  const shape = (pre ? pre + '|' : '') + w;
  const sym = shape.replace(/1+/g, x => { if (x.length < 6) return x; const c = x.length > 1.5 * R ? 2 : 1, d = x.length - c * R; return '1^{' + (c === 2 ? '2R' : 'R') + (d >= 0 ? '+' : '') + d + '}'; });
  byClass.get(c).push({ N, s, ok: r.ok, A: r.A, sym, p: pl[0], L: pl[1] });
}
const out = ['# 定理 K47 の族の v = 5、ρ = 2、N 奇数の型（N mod 28 の類ごと）', '# 生成: node --stack-size=65500 code/v5_odd_N.js ' + N0 + ' ' + N1, '# R = (N − 5)/2。周期の m+2 の連（長さ 6 以上）を 1^{R+δ} または 1^{2R+δ}（長さが 1.5R を超えるとき）で書く。'];
let total = 0, okc = 0;
for (const c of [...byClass.keys()].sort((x, y) => x - y)) {
  const rows = byClass.get(c), syms = new Set(rows.filter(x => x.sym).map(x => x.sym));
  out.push('', `## N ≡ ${c} (mod 28)（s = ${rows[0].s}）：形 ${syms.size === 1 ? [...syms][0] : syms.size + ' 通り'}`);
  for (const x of rows) { total++; if (x.ok) okc++; out.push(`  N = ${x.N}：${x.note || (x.ok ? '確定' : '確定せず') + '（仮定 ' + x.A + '）、前周期 ' + x.p + '、周期 ' + x.L + '、' + x.sym}`); }
}
out.push('', `${total} 個中 ${okc} 個で確定`);
console.log(out.join('\n'));
