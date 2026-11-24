/*
 * k44_induction.js — 予想 K44 の族を、N ごとに周期についての帰納法（period_induction.js の prove3）で確定させる
 *
 * 何を計算するか:
 *   N ≡ 6 (mod 8)、30 ≤ N ≤ NMAX で a = (3·2^N − 5)/17、m = 3a − 2 とし、
 *   予想 K44 の周期 w = 1^{(N−2)/4} 0^z（z = 3（N ≡ 6 (mod 24)）、z = 2（それ以外））について、
 *   prove3(m, 周期を c−1 回, 周期を k 回くり返したもの)（c = 1, 2, 4, …, 32、k = 1..4、coverage_pi.js と同じ試し方）が成功するかを調べる。
 *   成功すれば、その m の型は前周期なし・周期 w に確定する（前提は prove3 と同じく H(j)、K3、Q_n）。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k44_induction.js 398 > data/k44_induction.txt
 */
'use strict';
const { prove3 } = require('./period_induction');
const NMAX = +(process.argv[2] || 398);
const out = ['# 予想 K44 の族の周期についての帰納法', '# 生成: node --stack-size=65500 code/k44_induction.js ' + NMAX, 'N | 周期 | 成功した (c, k) | 仮定の事実の数 | 失敗の理由'];
let okc = 0, cnt = 0;
for (let N = 30; N <= NMAX; N += 8) {
  const m = 3n * ((3n * 2n ** BigInt(N) - 5n) / 17n) - 2n;
  const z = N % 24 === 6 ? 3 : 2, w = '1'.repeat((N - 2) / 4) + '0'.repeat(z);
  let hit = null, last = null;
  for (const c of [1, 2, 4, 8, 16, 32]) { for (let k = 1; k <= 4 && !hit; k++) { const r = prove3(m, w.repeat(c - 1), w.repeat(k)); if (r.ok) hit = [c, k, r]; else last = r.why; } if (hit) break; }
  cnt++; if (hit) okc++;
  out.push(`${N} | 1^${(N - 2) / 4} 0^${z} | ${hit ? '(' + hit[0] + ', ' + hit[1] + ')' : '-'} | ${hit ? (hit[2].A) : '-'} | ${hit ? '' : last}`);
}
out.push('', `${cnt} 個中 ${okc} 個で帰納法が閉じた`);
console.log(out.join('\n'));
