/*
 * k33_odd_cone.js — m = 9·2^e + 1（e 奇数）で、最初の周期の間隔を決めるのに参照される距離を、o* の倍数からのずれで分類する
 *
 * 何を計算するか:
 *   奇数 e について m = 9·2^e + 1、o* = 3·2^e + 1、周期 P = (3e+1)/2 とし、ブロック 0〜P の間隔を
 *   h から必要な (j, d) だけ遅延評価する（規則は block_rule.js と同じ）。参照した距離 d を、
 *   d = (q/4)·o* + r（q = 0..8、|r| 最小）と書き、q ごとに r の一覧を出す。あわせて事実の数、異なる距離の数を出す。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k33_odd_cone.js 9 11 13 15 > data/k33_odd_cone.txt
 */
'use strict';
const es = process.argv.slice(2).map(Number);
const out = ['# m = 9·2^e + 1（e 奇数）の最初の周期で参照される距離の分類', `# 生成: node --stack-size=65500 code/k33_odd_cone.js ${es.join(' ')}`];
for (const e of es) {
  const m = 9 * 2 ** e + 1, h = (m + 1) / 2, os = 3 * 2 ** e + 1, P = (3 * e + 1) / 2;
  const memo = new Map(), gm = new Map(); let facts = 0; const ds = new Set();
  const gap = j => { if (gm.has(j)) return gm.get(j); const r = S(j, h) ? m + 2 : m + 1; gm.set(j, r); return r; };
  function S(j, d) {
    const k = j * (m + 2) + d; if (memo.has(k)) return memo.get(k); let r;
    if (j === 0) { let c = 0, x = d; while (x % 2 === 0) { x /= 2; c++; } r = c % 2 === 0; }
    else { r = !(d % 2 === 0 && S(j, d / 2)); if (r) { const g = gap(j - 1), s = g + d; if (s % 2 === 0 && s / 2 <= m && S(j - 1, s / 2)) r = false; if (r && g === m + 2 && d === h - 1) r = false; } }
    memo.set(k, r); facts++; ds.add(d); return r;
  }
  const gs = []; for (let j = 0; j <= P; j++) gs.push(gap(j) === m + 2 ? 1 : 0);
  out.push('', `## e = ${e}`, `間隔（ブロック 0〜${P}）: ${gs.join('')}`, `事実の数: ${facts}、異なる距離: ${ds.size}`);
  const cls = {};
  for (const d of ds) { let best = null; for (let q = 0; q <= 8; q++) { const r = d - q * os / 4; if (best === null || Math.abs(r) < Math.abs(best[1])) best = [q, r]; } (cls[best[0]] = cls[best[0]] || []).push(best[1]); }
  for (const q of Object.keys(cls).sort((a, b) => a - b)) out.push(`  (${q}/4)·o* + r： r = ${cls[q].sort((a, b) => a - b).join(' ')}`);
}
console.log(out.join(String.fromCharCode(10)));
