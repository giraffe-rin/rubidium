/*
 * period_induction_random.js — 大きい m を無作為に選び、遅延評価で推測した型を period_induction.js で確定させる
 *
 * 何を計算するか:
 *   乱数の種 SEED から決まる擬似乱数で、2^K < m < 2^{K+1}、v2(m+1) が奇数の m を COUNT 個選ぶ。
 *   lazy_bigint.js の gapsBig で 400 ブロックの間隔の列を求め、前周期 p と周期 L を推測する。
 *   p = 0 で周期の列 w の末尾が 0 なら、period_induction.js の prove(m, w) で確定させる。prove が失敗したら、
 *   出発点をブロック L にとる prove2(m, w) を試す。
 *   出力：v2(m+1) ごとの、選んだ個数、p = 0 かつ末尾 0 の個数、確定した個数、失敗の理由の内訳。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/period_induction_random.js 40 200 1 > data/period_induction_random.txt
 */
'use strict';
const { prove, prove2 } = require('./period_induction'); const { gapsBig } = require('./lazy_bigint');
const [K, COUNT, SEED] = process.argv.slice(2).map(Number);
let st = BigInt(SEED) * 6364136223846793005n + 1442695040888963407n; const MASK = (1n << 64n) - 1n;
const rnd = () => { st = (st * 6364136223846793005n + 1442695040888963407n) & MASK; return st; };
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const per = g => { for (let L = 1; L <= g.length / 3; L++) for (let p = 0; p <= 100; p++) { if (g.length - p < 3 * L) break; let ok = true; for (let i = p; i + L < g.length; i++) if (g[i] !== g[i + L]) { ok = false; break; } if (ok) return [p, L]; } return null; };
const stat = {}; let n = 0;
while (n < COUNT) {
  const m = (1n << BigInt(K)) + (rnd() % (1n << BigInt(K))); if (m % 2n === 0n) continue; const v = v2(m + 1n); if (v % 2 === 0) continue; n++;
  const key = v >= 5 ? '≥5' : String(v); const s = (stat[key] = stat[key] || { n: 0, pure: 0, ok: 0, why: {} }); s.n++;
  let g; try { g = gapsBig(m, 400, 3000000).gaps; } catch (e) { s.why['事実が多すぎる（推測）'] = (s.why['事実が多すぎる（推測）'] || 0) + 1; continue; }
  const pl = per(g); if (!pl) { s.why['周期を推測できない'] = (s.why['周期を推測できない'] || 0) + 1; continue; }
  if (pl[0] !== 0) { s.why['前周期あり'] = (s.why['前周期あり'] || 0) + 1; continue; }
  const w = g.slice(0, pl[1]); if (w[w.length - 1] !== '0') { s.why['末尾が 1'] = (s.why['末尾が 1'] || 0) + 1; continue; }
  s.pure++; let r = prove(m, w); if (r.ok) s.ok++; else { const r2 = prove2(m, w); if (r2.ok) { s.ok++; s.ok2 = (s.ok2 || 0) + 1; } else s.why[r.why + ' / ' + r2.why] = (s.why[r.why + ' / ' + r2.why] || 0) + 1; }
}
const out = ['# 大きい m の型の、周期についての帰納法による確定（無作為抽出）', `# 生成: node --stack-size=65500 code/period_induction_random.js ${K} ${COUNT} ${SEED}`, `範囲：2^${K} < m < 2^${K + 1}、v2(m+1) が奇数`, 'v2(m+1) | 選んだ個数 | 前周期なし・末尾 0 | 確定（うち prove2 で）| それ以外の内訳'];
for (const [k, s] of Object.entries(stat)) out.push(`${k} | ${s.n} | ${s.pure} | ${s.ok}（${s.ok2 || 0}）| ${Object.entries(s.why).map(([w, c]) => w + ' ' + c).join('、') || '−'}`);
console.log(out.join(String.fromCharCode(10)));
