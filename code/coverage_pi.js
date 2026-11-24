/*
 * coverage_pi.js — M0 < m ≤ M1 で v2(m+1) が奇数のすべての m の型を、周期についての帰納法（period_induction.js の prove3）で確定させる
 *
 * 何を計算するか:
 *   各 m について、type_vs_t.js の gapsLazy で 400 ブロックの間隔の列を求めて前周期 p と周期 L を推測し（L ≤ 130、p ≤ 130）、
 *   prove3(m, 前周期 + 周期を c−1 回, 周期を k 回くり返したもの)（c = 1, 2, 4, …, 32、k = 1..4）で確定させる
 *   （状態の前周期が型の前周期より長いことがあるので、出発点を c 周期遅らせる）。
 *   出力：v2(m+1) ごとの個数、確定した個数、推測できなかった個数、確定しなかった m（最大 20 個）、前周期と周期の最大。
 *   v2(m+1) が偶数の m は、定理 K4・K42（間隔はいつも m+1）で型が決まるので、ここでは扱わない。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/coverage_pi.js 200000 1048576 > data/coverage_pi.txt
 */
'use strict';
const { prove3 } = require('./period_induction'); const { gapsLazy } = require('./type_vs_t');
const [M0, M1] = process.argv.slice(2).map(Number);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const per = g => { for (let L = 1; L <= 130; L++) for (let p = 0; p <= 130; p++) { if (g.length - p < 3 * L) break; let ok = true; for (let i = p; i + L < g.length; i++) if (g[i] !== g[i + L]) { ok = false; break; } if (ok) return [p, L]; } return null; };
const st = {}; const fail = []; let maxP = 0, maxL = 0;
for (let m = M0 + 1; m <= M1; m++) {
  if (m % 2 === 0) continue; const v = v2(m + 1); if (v % 2 === 0) continue;
  const key = v >= 5 ? '≥5' : String(v); const s = (st[key] = st[key] || { n: 0, ok: 0, noguess: 0 }); s.n++;
  const g = gapsLazy(m, 400).join(''); const pl = per(g); if (!pl) { s.noguess++; if (fail.length < 20) fail.push(m + '（推測できない）'); continue; }
  const pre = g.slice(0, pl[0]), w = g.slice(pl[0], pl[0] + pl[1]); let ok = false;
  // 状態の前周期が型の前周期より長いことがあるので、出発点を c 周期遅らせる（前周期の列の後ろに w を c−1 回つなぐ）
  for (const c of [1, 2, 4, 8, 16, 32]) { for (let k = 1; k <= 4 && !ok; k++) ok = prove3(BigInt(m), pre + w.repeat(c - 1), w.repeat(k)).ok; if (ok) break; }
  if (ok) { s.ok++; if (pl[0] > maxP) maxP = pl[0]; if (pl[1] > maxL) maxL = pl[1]; } else if (fail.length < 20) fail.push(String(m));
}
const out = ['# 周期についての帰納法による型の確定（全数）', `# 生成: node --stack-size=65500 code/coverage_pi.js ${M0} ${M1}`, `範囲：${M0} < m ≤ ${M1}、v2(m+1) が奇数`, 'v2(m+1) | m の個数 | 確定 | 型を推測できない'];
for (const [k, s] of Object.entries(st)) out.push(`${k} | ${s.n} | ${s.ok} | ${s.noguess}`);
out.push(`確定した型の前周期の最大: ${maxP}、周期の最大: ${maxL}`, fail.length ? '確定しなかった m（最大 20 個）: ' + fail.join(', ') : '確定しなかった m: なし');
console.log(out.join(String.fromCharCode(10)));
