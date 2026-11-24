/*
 * k45_induction.js — 予想 K45 の族を、N ごとに周期についての帰納法（period_induction.js の prove3）で確定させる
 *
 * 何を計算するか:
 *   N ≡ 0 (mod 28)、56 ≤ N ≤ NMAX で a = (2^N − 4641)/29、m = 3a − 2 とし、
 *   gapsBig（lazy_bigint.js）で J = 400, 800, 1600, 3200 ブロックまで計算して型（前周期 pre、周期 w）を推測する
 *   （前周期は列の半分以下、周期が 4 回以上見えるもの。w_class_v7_family.js と同じ）。
 *   prove3(m, pre + 周期を c−1 回, 周期を k 回くり返したもの)（c = 1, 2, 4, …, 32、k = 1..4、coverage_pi.js と同じ試し方）が成功するかを調べる。
 *   成功すれば、その m の型は確定し、周期の中の m+2 の間隔（1）の連の最大（巡回して数える）も確定する。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k45_induction.js 616 > data/k45_induction.txt
 */
'use strict';
const { prove3 } = require('./period_induction');
const { gapsBig } = require('./lazy_bigint');
const NMAX = +(process.argv[2] || 616);
function guess(g) {
  for (let L = 1; 3 * L <= g.length; L++) for (let p = 0; 2 * p <= g.length && p + 3 * L <= g.length; p++) {
    let ok = true; for (let i = p; i + L < g.length; i++) if (g[i] !== g[i + L]) { ok = false; break; }
    if (ok) return [p, L];
  }
  return null;
}
const out = ['# 予想 K45 の族の周期についての帰納法', '# 生成: node --stack-size=65500 code/k45_induction.js ' + NMAX,
  'N | p | L | 周期の中の 1 の連の最大 | 成功した (c, k) | 仮定の事実の数 | 失敗の理由'];
let okc = 0, cnt = 0;
for (let N = 56; N <= NMAX; N += 28) {
  const m = 3n * ((2n ** BigInt(N) - 4641n) / 29n) - 2n;
  let ty = null;
  for (const J of [400, 800, 1600, 3200]) { const g = gapsBig(m, J, 5e7).gaps; const pl = guess(g); if (pl && pl[0] + 4 * pl[1] <= J) { ty = [g.slice(0, pl[0]), g.slice(pl[0], pl[0] + pl[1])]; break; } }
  cnt++;
  if (!ty) { out.push(`${N} | ? | ? | ? | - | - | 型を推測できない`); continue; }
  const [pre, w] = ty; const k0 = w.indexOf('0'), rot = w.slice(k0) + w.slice(0, k0);
  const mx = Math.max(...rot.split('0').map(x => x.length));
  let hit = null, last = null;
  for (const c of [1, 2, 4, 8, 16, 32]) { for (let k = 1; k <= 4 && !hit; k++) { const r = prove3(m, pre + w.repeat(c - 1), w.repeat(k)); if (r.ok) hit = [c, k, r]; else last = r.why; } if (hit) break; }
  if (hit) okc++;
  out.push(`${N} | ${pre.length} | ${w.length} | ${mx} | ${hit ? '(' + hit[0] + ', ' + hit[1] + ')' : '-'} | ${hit ? hit[2].A : '-'} | ${hit ? '' : last}`);
}
out.push('', `${cnt} 個中 ${okc} 個で帰納法が閉じた`);
console.log(out.join('\n'));
