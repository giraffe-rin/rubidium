/*
 * cross_check_pi.js — coverage_pi.js（prove3）で確定した型を、R の状態の繰り返し（block_rule.js の periods）による型と照合する
 *
 * 何を計算するか:
 *   擬似乱数（種 SEED）で、M0 < m ≤ M1、v2(m+1) が奇数の m を COUNT 個選ぶ。各 m について、
 *     (a) coverage_pi.js と同じ方法（gapsLazy 400 ブロックからの推測と prove3）で確定した型（前周期の列と周期の列）
 *     (b) periods で状態が初めて繰り返すまで計算し、そこまでの間隔の列（nextBlock）から求めた型（前周期・周期の最小のもの）
 *   が一致するかを調べる。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/cross_check_pi.js 2097152 4194304 30 7 > data/cross_check_pi.txt
 */
'use strict';
const { prove3 } = require('./period_induction'); const { gapsLazy } = require('./type_vs_t'); const { periods, nextBlock } = require('./block_rule');
const [M0, M1, COUNT, SEED] = process.argv.slice(2).map(Number);
let st = SEED >>> 0; const rnd = () => { st = (Math.imul(st, 1664525) + 1013904223) >>> 0; return st / 4294967296; };
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const per = (g, LM, PM) => { for (let L = 1; L <= LM; L++) for (let p = 0; p <= PM; p++) { if (g.length - p < 3 * L) break; let ok = true; for (let i = p; i + L < g.length; i++) if (g[i] !== g[i + L]) { ok = false; break; } if (ok) return [p, L]; } return null; };
const out = ['# prove3 で確定した型と、R の状態の繰り返しによる型の照合', `# 生成: node --stack-size=65500 code/cross_check_pi.js ${M0} ${M1} ${COUNT} ${SEED}`, 'm | v2(m+1) | prove3 の型（前周期の長さ, 周期の長さ）| 状態の繰り返し（状態の前周期, 状態の周期）| 型が一致'];
let n = 0, agree = 0;
while (n < COUNT) {
  const m = M0 + 1 + Math.floor(rnd() * (M1 - M0)); if (m % 2 === 0 || v2(m + 1) % 2 === 0) continue; n++;
  const g = gapsLazy(m, 400).join(''); const pl = per(g, 130, 130); let ok = false, pre = '', w = '';
  if (pl) { pre = g.slice(0, pl[0]); w = g.slice(pl[0], pl[0] + pl[1]); for (const c of [1, 2, 4, 8, 16, 32]) { for (let k = 1; k <= 4 && !ok; k++) ok = prove3(BigInt(m), pre + w.repeat(c - 1), w.repeat(k)).ok; if (ok) break; } }
  const r = periods(m); let pv = null, s = ''; const len = r.preBlocks + 2 * r.periodBlocks + 1; for (let j = 0; j < len; j++) { pv = nextBlock(m, pv); s += pv.g === m + 2 ? 1 : 0; }
  // 状態の繰り返しの後は間隔の列も繰り返すので、s から最小の前周期と周期を求める（周期は状態の周期の約数）
  let best = null; for (let L = 1; L <= r.periodBlocks && !best; L++) { if (r.periodBlocks % L) continue; for (let p = 0; p <= r.preBlocks + 1; p++) { let okk = true; for (let i = p; i + L < len; i++) if (s[i] !== s[i + L]) { okk = false; break; } if (okk) { best = [p, L]; break; } } }
  const same = ok && best && best[0] === pre.length && best[1] === w.length && s.slice(0, best[0] + best[1]) === pre + w; if (same) agree++;
  out.push(`${m} | ${v2(m + 1)} | ${ok ? '(' + pre.length + ', ' + w.length + ')' : '確定せず'} | (${r.preBlocks}, ${r.periodBlocks}) → 型 (${best ? best.join(', ') : '?'}) | ${same ? 'はい' : 'いいえ'}`);
}
out.push('', `一致 ${agree} / ${COUNT}`);
console.log(out.join(String.fromCharCode(10)));
