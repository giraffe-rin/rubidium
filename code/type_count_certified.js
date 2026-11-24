/*
 * type_count_certified.js — 5 ≤ m ≤ 2^KMAX の確定した型（coverage_pi.js と同じ推測と prove3 による確定）の種類を、2^k ごとに数える
 *
 * 何を計算するか:
 *   v2(m+1) が奇数の m：gapsLazy で 400 ブロックから前周期と周期を推測し、coverage_pi.js と同じく prove3 で確定させる（確定しなければ数えない）。
 *   v2(m+1) が偶数の m：K4 により型は「前周期なし、周期 0」。
 *   型は「前周期の列 | 周期の列」で、周期の列は巡回させて辞書順最小にそろえる（type_growth.js と同じ数え方）。
 *   出力：k ごとに、m ≤ 2^k での型の種類の数（確定したもの）、確定しなかった m の数。type_growth.js の推測による数（data/type_growth_22.txt）と比べる。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/type_count_certified.js 22 > data/type_count_certified.txt
 */
'use strict';
const fs = require('fs');
const { prove3 } = require('./period_induction'); const { gapsLazy } = require('./type_vs_t');
const KMAX = +(process.argv[2] || 22);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const per = g => { for (let L = 1; L <= 130; L++) for (let p = 0; p <= 130; p++) { if (g.length - p < 3 * L) break; let ok = true; for (let i = p; i + L < g.length; i++) if (g[i] !== g[i + L]) { ok = false; break; } if (ok) return [p, L]; } return null; };
const canon = (pre, w) => { let best = w; for (let i = 1; i < w.length; i++) { const r = w.slice(i) + w.slice(0, i); if (r < best) best = r; } return (pre || '-') + '|' + best; };
const prev = {}; try { for (const l of fs.readFileSync('data/type_growth_22.txt', 'utf8').split(/\r?\n/)) { const mm = l.match(/^(\d+) \| (\d+) \|/); if (mm) prev[+mm[1]] = +mm[2]; } } catch (e) {}
const types = new Set(); let unproved = 0; const out = ['# 確定した型の種類の数', `# 生成: node --stack-size=65500 code/type_count_certified.js ${KMAX}`, 'k | m ≤ 2^k の確定した型の種類 | 確定しなかった m（累計）| 推測による数（type_growth_22.txt）'];
let m = 2;
for (let k = 2; k <= KMAX; k++) {
  for (; m <= 2 ** k; m++) {
    if (m < 5) { if (v2(m + 1) % 2 === 0) types.add('-|0'); continue; }
    if (v2(m + 1) % 2 === 0) { types.add('-|0'); continue; }
    const g = gapsLazy(m, 400).join(''); const pl = per(g); if (!pl) { unproved++; continue; }
    const pre = g.slice(0, pl[0]), w = g.slice(pl[0], pl[0] + pl[1]); let ok = false;
    for (const c of [1, 2, 4, 8, 16, 32]) { for (let kk = 1; kk <= 4 && !ok; kk++) ok = prove3(BigInt(m), pre + w.repeat(c - 1), w.repeat(kk)).ok; if (ok) break; }
    if (ok) types.add(canon(pre, w)); else unproved++;
  }
  if (k >= 4) out.push(`${k} | ${types.size} | ${unproved} | ${prev[k] !== undefined ? prev[k] : '−'}`);
}
console.log(out.join(String.fromCharCode(10)));
