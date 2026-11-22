/*
 * k9_certificate.js — K9 の十分性の、m ごとの「健全な伝播」による証明書
 *
 * 何を計算するか:
 *   v2(m+1) = 1 で v2(3h+1) が奇数の m（h = (m+1)/2、m ≤ M）について、交互型を仮定した帰納法の不変量を自動で作る。
 *   不変量は、偶数番目のブロック（E）と奇数番目のブロック（O）での、距離 d の所属の事実の集合。
 *   漸化式 R（[非形式証明] K8）の規則を、交互型の場合に当てはめて伝播させる。
 *     E（j ≥ 2、1 つ前の間隔 m+1）:
 *       奇数 d は入る。2x は「x ∉ E かつ h+x ∉ O」のとき入り、そうでないとき入らない。
 *     O（j ≥ 1、1 つ前の間隔 m+2）:
 *       奇数 d ≤ m−2 は「(m+2+d)/2 ∉ E」のとき入る。d = m は入る。
 *       偶数 d は、d = h−1 なら入らない。それ以外は「d/2 ∉ O」のとき入る。
 *   ただし E の事実は、ブロック 0 でも成り立つもの（定理 K3：d ∈ S₀ ⇔ v2(d) 偶数 と一致するもの）だけを採用する。
 *   こうして得た事実は、すべての偶数番目／奇数番目のブロックで成り立つ。
 *   根拠：j についての帰納法で、同じブロック内の依存は d/2 < d だけなので順序がつく。
 *   その事実に「h ∈ E かつ h ∉ O」が含まれれば、交互型であることの証明書になる。
 *   証明書の大きさ（h の 2 つの事実を導くのに実際に使った事実の数）も出す。
 *
 * 実行方法（リポジトリのルートで）:
 *   node code/k9_certificate.js 1000 > data/k9_certificates.txt
 */
'use strict';

const M = +(process.argv[2] || 1000);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };

function certificate(m) {
  const h = (m + 1) / 2;
  const k3 = d => (v2(d) % 2 === 0 ? 1 : 0);
  const E = new Int8Array(m + 1).fill(-1), O = new Int8Array(m + 1).fill(-1);
  const why = {};
  let changed = true;
  while (changed) {
    changed = false;
    for (let d = 1; d <= m; d++) {
      if (E[d] < 0) {
        let v = -1, dep = [];
        if (d % 2) v = 1;
        else {
          const x = d / 2;
          if (E[x] === 1) { v = 0; dep = ['E' + x]; }
          else if (h + x <= m && O[h + x] === 1) { v = 0; dep = ['O' + (h + x)]; }
          else if (E[x] === 0 && (h + x > m || O[h + x] === 0)) { v = 1; dep = ['E' + x].concat(h + x <= m ? ['O' + (h + x)] : []); }
        }
        if (v >= 0 && v === k3(d)) { E[d] = v; why['E' + d] = dep; changed = true; }
      }
      if (O[d] < 0) {
        let v = -1, dep = [];
        if (d % 2) { const e = (m + 2 + d) / 2; if (e > m) v = 1; else if (E[e] >= 0) { v = 1 - E[e]; dep = ['E' + e]; } }
        else { const x = d / 2; if (d === h - 1) v = 0; else if (O[x] >= 0) { v = 1 - O[x]; dep = ['O' + x]; } }
        if (v >= 0) { O[d] = v; why['O' + d] = dep; changed = true; }
      }
    }
  }
  const ok = E[h] === 1 && O[h] === 0;
  const need = new Set();
  if (ok) { const st = ['E' + h, 'O' + h]; while (st.length) { const k = st.pop(); if (need.has(k)) continue; need.add(k); for (const x of why[k] || []) st.push(x); } }
  return { ok, size: need.size };
}

const out = ['# K9 の十分性の、m ごとの健全な伝播による証明書', `# 生成: node code/k9_certificate.js ${M}`,
  '# 列: m | m mod 32 | 証明書が得られたか | 証明書の大きさ（使った事実の数）'];
let ok = 0, all = 0;
for (let m = 5; m <= M; m += 4) {
  if (v2(m + 1) !== 1) continue;
  const h = (m + 1) / 2;
  if (v2(3 * h + 1) % 2 !== 1) continue;
  const c = certificate(m);
  all++; if (c.ok) ok++;
  out.push(`m=${m} | ${m % 32} | ${c.ok ? 'はい' : 'いいえ'} | ${c.ok ? c.size : '—'}`);
}
out.push('');
out.push(`K9 の条件を満たす v2(m+1) = 1 の m（5 ≤ m ≤ ${M}）: ${all} 個中 ${ok} 個で証明書が得られた`);
process.stdout.write(out.join('\n') + '\n');
