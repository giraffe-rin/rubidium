/*
 * renormalize.js — m ≡ 9 (mod 32)（v2(m+1) = 1）の m の型が、より小さい m' = f(m) の型だけで決まるかを調べる
 *
 * 何を計算するか:
 *   9 ≤ m < MMAX、m ≡ 9 (mod 32) の m について、型 T(m)（type_vs_t.js の typeOf、300 ブロック）を求める。
 *   候補の写像 f（(m − 9)/(32/d) + c、d ∈ {2, 4, …, 64}、|c| ≤ 12、と (m + c)/d、d ∈ {2, 4, 8, 16}、|c| ≤ 6）について、
 *   f(m) が 2 以上の整数になる m で「T(f(m)) が同じなら T(m) も同じ」が成り立つか（T(m) が T(f(m)) の関数か）を調べる。
 *   出力：成り立った写像と、使った m の個数、T(f(m)) の種類の数。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/renormalize.js 120000 > data/renormalize.txt
 */
'use strict';
const { typeOf } = require('./type_vs_t');
const MMAX = +(process.argv[2] || 120000);
const memo = new Map(); const ty = m => { if (!memo.has(m)) memo.set(m, typeOf(m, 300)); return memo.get(m); };
const ms = []; for (let m = 9; m < MMAX; m += 32) ms.push(m);
const cands = [];
for (const d of [2, 4, 8, 16, 32, 64]) for (let c = -12; c <= 12; c++) cands.push([`(m − 9)/${32 / d} ${c >= 0 ? '+' : '−'} ${Math.abs(c)}`, m => (m - 9) / (32 / d) + c]);
for (const d of [2, 4, 8, 16]) for (let c = -6; c <= 6; c++) cands.push([`(m ${c >= 0 ? '+' : '−'} ${Math.abs(c)})/${d}`, m => (m + c) / d]);
const out = ['# m ≡ 9 (mod 32) の型が m\x27 = f(m) の型の関数になるか', `# 生成: node --stack-size=65500 code/renormalize.js ${MMAX}`, `類の m の個数: ${ms.length}、型の種類: ${new Set(ms.map(ty)).size}`, `調べた写像: ${cands.length} 個`, '', '## 成り立った写像 | 使った m | T(f(m)) の種類'];
for (const [name, f] of cands) {
  const map = new Map(); let ok = true, n = 0;
  for (const m of ms) { const x = f(m); if (!Number.isInteger(x) || x < 2) continue; n++; const k = ty(x), t = ty(m); if (map.has(k) && map.get(k) !== t) { ok = false; break; } map.set(k, t); }
  if (ok && n > 100) out.push(`${name} | ${n} | ${map.size}`);
}
console.log(out.join(String.fromCharCode(10)));
