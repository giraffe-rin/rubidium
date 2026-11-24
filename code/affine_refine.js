/*
 * affine_refine.js — 証明書で決まらなかった類だけを、さらに細かく分けて証明書を作り直す
 *
 * 何を計算するか:
 *   affine_certificate.js の出力ファイルの「証明できなかった類」（m ≡ B (mod A)）だけを読み、
 *   各類を t の偶奇で 2^d 個（A·2^d ≤ 2^T となるまで）に分けながら、affine_certificate.js と同じ手順
 *   （代表の m で (p, L) を推測し、certify を試す。失敗の扱いも同じ）で証明書を作る。
 *   証明できた類は、元のファイルの「証明できた類」と合わせて使う（類は互いに重ならない）。
 *   出力: 新しく証明できた類と、まだ決まらない類、密度（v2(m+1) = v の m の中）。進み具合は 1 行ずつ標準エラーに出す。
 *
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/affine_refine.js data/affine_certificates_v1_T18.txt 1 20 > data/affine_refine_v1_T20.txt
 *   （第 1 引数 元のファイル、第 2 引数 v、第 3 引数 T）
 */
'use strict';
const fs = require('fs');
const { certify, guess, Split, Fail } = require('./affine_certificate');
const [file, vs, Ts, lim] = process.argv.slice(2);
const v = +vs, T = +Ts, LIMIT = lim ? +lim : Infinity;
const MAXF = 200000, MREP = 3000;
const open0 = [];
let sec = '';
for (const l of fs.readFileSync(file, 'utf8').split(/\r?\n/)) {
  if (l.startsWith('## 証明できなかった類')) { sec = 'ng'; continue; }
  if (l.startsWith('##')) { sec = ''; continue; }
  const mm = l.match(/^m ≡ (\d+) \(mod (\d+)\)/);
  if (sec === 'ng' && mm) open0.push([+mm[2], +mm[1]]);
}
// (p, L) の推測を速くする工夫（証明書の正しさには関わらない）:
//   (1) 同じ m の推測は覚えておく（親の類の代表は、2 つの子の類の片方の代表にもなる）。
//   (2) まず 150 ブロックで推測し、見つからなければ 600 ブロックで推測する。
const gcache = new Map();
function guessCached(m) {
  if (gcache.has(m)) return gcache.get(m);
  const r = guess(m, 150) || guess(m, 600); gcache.set(m, r); return r;
}
const done = [], open = [];
const queue = open0.slice(0, LIMIT).flatMap(([A, B]) => [[2 * A, B], [2 * A, B + A]]);
const t0 = Date.now(); let tried = 0;
while (queue.length) {
  const [A, B] = queue.shift();
  
  const t = Math.max(0, Math.ceil((MREP - B) / A)), m = A * t + B;
  let res = null, why = '';
  const attempt = pl => {
    if (!pl) { why = '周期を推測できない'; return; }
    tries: for (const mult of [1, 2, 3, 4, 6]) for (const extra of [0, 1, 2, 4, 8]) {
      const P0 = pl[0] + extra * pl[1], L0 = mult * pl[1];
      try { res = certify(A, B, P0, L0, MAXF); res.p = P0; res.L = L0; break tries; }
      catch (e) { if (e instanceof Split) { why = '偶奇が t による'; break tries; } else if (e instanceof Fail) why = e.message; else throw e; }
    }
  };
  attempt(guessCached(m));
  // 短い推測で Split 以外の失敗をしたら、600 ブロックの推測でもう一度試す
  if (!res && why !== '偶奇が t による') { why = ''; attempt(guess(m, 600)); }
  tried++;
  if (res) { done.push({ A, B, ...res }); process.stderr.write(`ok ${B} mod ${A} (${tried}, ${((Date.now() - t0) / 1000).toFixed(0)}s)\n`); }
  else if (why === '偶奇が t による' && 2 * A <= 2 ** T) { queue.push([2 * A, B]); queue.push([2 * A, B + A]); }
  else { open.push({ A, B, why }); }
  if (tried % 200 === 0) process.stderr.write(`tried ${tried} queue ${queue.length} ${((Date.now() - t0) / 1000).toFixed(0)}s\n`);
}
const open2 = open.sort((x, y) => x.A - y.A || x.B - y.B);
const dens = cls => cls.reduce((s, c) => s + 2 ** (v + 1) / c.A, 0);
const out = [`# 証明書で決まらなかった類の再分割（${file} の未証明の類${LIMIT < Infinity ? 'の最初の ' + LIMIT + ' 個' : ''}、v2(m+1) = ${v}、A ≤ 2^${T}）`,
  `# 生成: node --stack-size=65500 code/affine_refine.js ${file} ${v} ${T}${LIMIT < Infinity ? ' ' + LIMIT : ''}`,
  `新しく証明できた類: ${done.length} 個（密度 ${dens(done).toFixed(6)}）`,
  `まだ決まらない類: ${open2.length} 個（密度 ${dens(open2).toFixed(6)}）`,
  `元の未証明の密度: ${dens(open0.slice(0, LIMIT).map(([A, B]) => ({ A, B }))).toFixed(6)}`,
  '', '## 新しく証明できた類: m ≡ B (mod A) | M_min | 型 | 事実の個数'];
done.sort((x, y) => x.A - y.A || x.B - y.B);
for (const c of done) { const g = c.gaps.join(''); out.push(`m ≡ ${c.B} (mod ${c.A}) | ${c.A * c.tmin + c.B} | ${g.slice(0, c.p) || '-'} | ${g.slice(c.p)} | ${c.n}`); }
out.push('', '## まだ決まらない類: m ≡ B (mod A) | 理由');
for (const c of open2) out.push(`m ≡ ${c.B} (mod ${c.A}) | ${c.why}`);
console.log(out.join('\n'));
