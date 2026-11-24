/*
 * check_affine_blockrule.js — 証明書の一覧の各類を、ブロック漸化式（block_rule.js）で数値的に照合する
 *
 * 何を計算するか:
 *   ファイルの「証明できた類」または「新しく証明できた類」の各行（m ≡ B (mod A) | M_min | 前周期 | 周期 | …）について、
 *   M_min 以上 MMAX 以下の元を小さい順に最大 K 個選び、block_rule.js の nextBlock で前周期 + 3 周期分の間隔を求めて照合する。
 *   証明書のコード（affine_certificate.js、affine3.js）とは独立な確認である（使うのは漸化式 R だけ）。
 * 実行方法（リポジトリのルートで）:
 *   node code/check_affine_blockrule.js <ファイル> <K> <MMAX> > data/<名前>.txt
 */
'use strict';
const fs = require('fs');
const { nextBlock } = require('./block_rule');
const [file, Ks, Ms] = process.argv.slice(2); const K = +Ks, MMAX = +Ms;
let ncls = 0, nm = 0; const bad = [];
for (const l of fs.readFileSync(file, 'utf8').split(/\r?\n/)) {
  const mm = l.match(/^m ≡ (\d+) \(mod (\d+)\) \| (\d+) \| ([-01]+) \| ([01]+) \|/); if (!mm) continue;
  const B = +mm[1], A = +mm[2], Mmin = +mm[3], pre = mm[4] === '-' ? '' : mm[4], per = mm[5];
  ncls++; let k = 0;
  for (let m = B + Math.max(0, Math.ceil((Math.max(Mmin, 5) - B) / A)) * A; m <= MMAX && k < K; m += A, k++) {
    const want = pre + per.repeat(3); let pv = null, ok = true;
    for (let j = 0; j < want.length; j++) { pv = nextBlock(m, pv); if (String(pv.g - m - 1) !== want[j]) { ok = false; break; } }
    nm++; if (!ok) bad.push(`${m}（m ≡ ${B} mod ${A}）`);
  }
}
console.log([`# ブロック漸化式による証明書の照合（${file}）`, `# 生成: node code/check_affine_blockrule.js ${file} ${K} ${MMAX}`,
  `類: ${ncls} 個、調べた m: ${nm} 個。食い違い: ${bad.length ? bad.length + ' 個（' + bad.slice(0, 20).join(', ') + '）' : 'なし'}`].join('\n'));
