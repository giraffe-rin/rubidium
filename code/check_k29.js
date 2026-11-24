/*
 * check_k29.js — 予想 K29（v2(m+1) = v ≥ 5 が奇数で ℓ = v2(m+2−3u) = 1 なら「1 0^{(v−1)/2}」型）の確認
 *
 * 何を計算するか:
 *   ℓ = 1 は u = (m+1)/2^v ≡ 1 (mod 4) と同じで、類 m ≡ 2^v − 1 (mod 2^{v+2}) になる。
 *   (1) 証明書：v = 5, 7, …, VMAX について、この類に affine_certificate.js の certify を当てる。
 *       周期 L = (v+1)/2、前周期は 0, L, 2L, 4L, 8L を試す（間隔の列が 1 0^{L−1} の繰り返しであることを確かめる）。
 *       「偶奇が t による」なら類を 2 つに分けて続け、深さ DMAX まで。
 *       証明できた類の密度と、残った類の密度（ℓ = 1 の類の中）を出す。
 *   (2) ブロック漸化式：m ≤ MMAX で v ≥ 5 が奇数、ℓ = 1 のすべての m について、
 *       block_rule.js の nextBlock で最初の 4 周期分の間隔を求め、予想と照合する。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/check_k29.js 15 14 300000 > data/k29_check.txt
 *   （引数: VMAX DMAX MMAX）
 */
'use strict';
const { certify } = require('./affine_certificate');
const { nextBlock } = require('./block_rule');
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const VMAX = +(process.argv[2] || 15), DMAX = +(process.argv[3] || 14), MMAX = +(process.argv[4] || 300000);
function prove(A, B, L, depth, st) {
  const want = '1' + '0'.repeat(L - 1); let split = false;
  for (const k of [0, 1, 2, 4, 8]) {
    try { const r = certify(A, B, k * L, L, 3e5); const g = r.gaps.join('');
      if (g !== want.repeat(k + 1)) { st.wrong.push(`${B} mod ${A}（${g}）`); return; }
      st.ok += 1 / A; st.n++; st.Mmax = Math.max(st.Mmax, A * r.tmin + B); return; }
    catch (e) { if (e.constructor.name === 'Split') { split = true; break; } }
  }
  if (!split || depth >= DMAX) { st.left += 1 / A; st.nl++; if (st.ex.length < 3) st.ex.push(`${B} mod ${A}`); return; }
  prove(2 * A, B, L, depth + 1, st); prove(2 * A, B + A, L, depth + 1, st);
}
const out = ['# 予想 K29 の確認（v2(m+1) = v ≥ 5 奇数、ℓ = 1 なら 1 0^{(v−1)/2} 型）', `# 生成: node --stack-size=65500 code/check_k29.js ${VMAX} ${DMAX} ${MMAX}`, '',
  '## (1) 証明書（類 m ≡ 2^v − 1 (mod 2^{v+2}) を深さ ' + DMAX + ' まで分割）: v | 証明できた類 | 証明できた密度（類の中）| 残りの類 | 型が違う類 | 最大の M_min'];
for (let v = 5; v <= VMAX; v += 2) {
  const A = 2 ** (v + 2), st = { ok: 0, n: 0, left: 0, nl: 0, wrong: [], Mmax: 0, ex: [] };
  prove(A, 2 ** v - 1, (v + 1) / 2, 0, st);
  out.push(`v=${v} | ${st.n} | ${(st.ok * A).toFixed(6)} | ${st.nl}（例: ${st.ex.join(', ')}）| ${st.wrong.length ? st.wrong.join(', ') : 'なし'} | ${st.Mmax}`);
}
out.push('', '## (2) ブロック漸化式による確認');
const cnt = {}; const bad = [];
for (let m = 31; m <= MMAX; m += 2) {
  const v = v2(m + 1); if (v < 5 || v % 2 === 0) continue;
  const u = (m + 1) / 2 ** v; if (u % 4 !== 1) continue;
  const L = (v + 1) / 2, want = '1' + '0'.repeat(L - 1); let pv = null, ok = true;
  for (let J = 0; J < 4 * L; J++) { pv = nextBlock(m, pv); if (String(pv.g - m - 1) !== want[J % L]) { ok = false; break; } }
  cnt[v] = (cnt[v] || 0) + 1; if (!ok) bad.push(m);
}
out.push(`調べた m（v ごと）: ${Object.entries(cnt).map(([v, c]) => `v=${v}: ${c}`).join('、')}。食い違い: ${bad.length ? bad.slice(0, 30).join(', ') : 'なし'}`);
console.log(out.join('\n'));
