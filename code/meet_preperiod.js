/*
 * meet_preperiod.js — 3 値の証明書で原因が meet の類について、前周期 p と周期 L が t によってどう変わるかを調べる
 *
 * 何を計算するか:
 *   <類の一覧> の「まだ決まらない類」から先頭 NCLS 個を取り、affine3_diag.js と同じ診断で原因が meet の類を選ぶ。
 *   選んだ類 m ≡ B (mod A) について、t = 0, 1, …, TMAX の m = A t + B の (p, L) を、ブロック漸化式で 600 ブロック計算して推測する（guess）。
 *   出力：類ごとの (p, L) の列と、p が t とともに増えた類の個数。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/meet_preperiod.js data/affine3_refine_v7.txt 60 3 > data/meet_preperiod_v7.txt
 */
'use strict';
const fs = require('fs');
const { certify3, Fail } = require('./affine3_diag');
const { guess } = require('./affine_certificate');
const [file, nc, tm] = process.argv.slice(2); const NCLS = +(nc || 60), TMAX = +(tm || 3);
const open = []; let sec = '';
for (const l of fs.readFileSync(file, 'utf8').split(/\r?\n/)) {
  if (/^## (証明できなかった類|まだ決まらない類)/.test(l)) { sec = 'ng'; continue; }
  if (l.startsWith('##')) { sec = ''; continue; }
  const mm = l.match(/^m ≡ (\d+) \(mod (\d+)\)/); if (sec === 'ng' && mm) open.push([+mm[2], +mm[1]]);
}
const out = ['# 原因が meet の類の前周期と周期（' + file + '）', `# 生成: node --stack-size=65500 code/meet_preperiod.js ${file} ${NCLS} ${TMAX}`,
  '類 | 診断に使った (p, L) | t = 0, 1, … の (p, L)'];
let n = 0, grow = 0, same = 0, other = 0;
for (const [A, B] of open.slice(0, NCLS)) {
  const t0 = Math.max(0, Math.ceil((3000 - B) / A)), pl = guess(A * t0 + B, 300) || guess(A * t0 + B, 600); if (!pl) continue;
  let why = null; try { certify3(A, B, pl[0], pl[1], 300000); } catch (e) { if (!(e instanceof Fail)) throw e; why = e.why && e.why[0]; }
  if (why !== 'meet') continue; n++;
  const seq = []; for (let t = 0; t <= TMAX; t++) { const g = guess(A * t + B, 600); seq.push(g ? `(${g[0]}, ${g[1]})` : '?'); }
  const ps = seq.map(s => +(s.match(/\((\d+)/) || [0, NaN])[1]), Ls = seq.map(s => +(s.match(/, (\d+)/) || [0, NaN])[1]);
  if (Ls.every(L => L === Ls[0]) && ps.every((p, i) => i === 0 || p > ps[i - 1])) grow++;
  else if (seq.every(s => s === seq[0])) same++; else other++;
  out.push(`m ≡ ${B} (mod ${A}) | (${pl[0]}, ${pl[1]}) | ${seq.join(' ')}`);
}
out.push('', `原因が meet の類: ${n} 個。L が一定で p が t とともに増える: ${grow}、(p, L) が t によらない: ${same}、その他: ${other}`);
console.log(out.join('\n'));
