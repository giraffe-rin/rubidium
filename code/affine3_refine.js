/*
 * affine3_refine.js — 3 値の証明書（affine3.js）で決まらなかった類を、法を大きくして分けて当て直す
 *
 * 何を計算するか:
 *   <再分割の一覧のファイル> の「証明できなかった類」から、<affine3 の出力> で証明できた類を除いたものを「残りの類」とする。
 *   残りの類 m ≡ B (mod A) を、A' = A·2^s（s = 1, …, S）の 2^s 個の類に分け、各類で p, L を推測して certify3 を試す。
 *   s 段目で証明できなかった類だけを、次の段でさらに分ける。
 *   出力：段ごとの証明できた類の個数と密度、最後まで残った類の個数、証明できた類の一覧。
 *   健全性は affine3.js と同じ（各類の証明書は独立）。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/affine3_refine.js <再分割の一覧> <affine3 の出力> <v> <S> > data/affine3_refine_<名前>.txt
 */
'use strict';
const fs = require('fs');
const { certify3, Fail } = require('./affine3');
const { guess } = require('./affine_certificate');
const [file, done3, vs, Ss] = process.argv.slice(2); const v = +vs, S = +(Ss || 2);
const readSec = (f, re) => { const r = []; let sec = '';
  for (const l of fs.readFileSync(f, 'utf8').split(/\r?\n/)) {
    if (re.test(l)) { sec = 'x'; continue; } if (l.startsWith('##')) { sec = ''; continue; }
    const mm = l.match(/^m ≡ (\d+) \(mod (\d+)\)/); if (sec && mm) r.push([+mm[2], +mm[1]]);
  } return r; };
const open = readSec(file, /^## (証明できなかった類|まだ決まらない類)/);
const got = new Set(readSec(done3, /^## 新しく証明できた類/).map(([A, B]) => A + ',' + B));
let rest = open.filter(([A, B]) => !got.has(A + ',' + B));
const dens = cls => cls.reduce((s, [A]) => s + 2 ** (v + 1) / A, 0);
function tryClass(A, B) {
  const t = Math.max(0, Math.ceil((3000 - B) / A)), m = A * t + B;
  const pl = guess(m, 300) || guess(m, 600); if (!pl) return null;
  for (const mult of [1, 2, 3, 4]) for (const extra of [0, 1, 2, 4, 8]) {
    try { const r = certify3(A, B, pl[0] + extra * pl[1], mult * pl[1], 300000); r.p = pl[0] + extra * pl[1]; r.L = mult * pl[1]; return r; }
    catch (e) { if (!(e instanceof Fail)) throw e; }
  }
  return null;
}
const out = [`# 3 値の証明書で決まらなかった類の再分割（${file}、v2(m+1) = ${v}）`,
  `# 生成: node --stack-size=65500 code/affine3_refine.js ${file} ${done3} ${v} ${S}`,
  `残りの類: ${rest.length} 個（密度 ${dens(rest).toFixed(6)}）`];
const proved = [];
for (let s = 1; s <= S; s++) {
  const next = [], now = [];
  for (const [A, B] of rest) for (const B2 of [B, B + A]) {
    const r = tryClass(2 * A, B2);
    if (r) now.push({ A: 2 * A, B: B2, ...r }); else next.push([2 * A, B2]);
  }
  proved.push(...now);
  out.push(`段 ${s}（法 ×${2 ** s}）: 証明できた類 ${now.length} 個（密度 ${dens(now.map(c => [c.A])).toFixed(6)}）、残り ${next.length} 個（密度 ${dens(next).toFixed(6)}）`);
  rest = next;
}
out.push(`証明できた類の合計の密度: ${dens(proved.map(c => [c.A])).toFixed(6)}`, '', '## 新しく証明できた類: m ≡ B (mod A) | M_min | 型 | 事実の個数');
proved.sort((x, y) => x.A - y.A || x.B - y.B);
for (const c of proved) { const g = c.gaps.join(''); out.push(`m ≡ ${c.B} (mod ${c.A}) | ${c.A * c.tmin + c.B} | ${g.slice(0, c.p) || '-'} | ${g.slice(c.p)} | ${c.n}`); }
out.push('', '## まだ決まらない類'); for (const [A, B] of rest) out.push(`m ≡ ${B} (mod ${A})`);
console.log(out.join('\n'));
