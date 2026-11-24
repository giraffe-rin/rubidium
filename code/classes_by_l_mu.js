/*
 * classes_by_l_mu.js — K16 の証明書の一覧を、K22 の量 ℓ = v2(m+2−3u) と μ = v2(c) の偶奇で分類する
 *
 * 何を計算するか:
 *   affine_certificate.js の出力ファイル（v2(m+1) = V）の各類 m = A t + B について、
 *   u = (m+1)/2^V、E = m + 2 − 3u、ℓ = v2(E)、（ℓ が偶数なら）c = (m + 2 − E/2^ℓ)/3、μ = v2(c) を t の 1 次式として扱い、
 *   t によらず決まる類だけを「ℓ 奇数」「ℓ 偶数・μ 奇数」「ℓ 偶数・μ 偶数」に分ける（決まらない類は「未定」）。
 *   各区分の、証明できた類とできなかった類の自然密度（v2(m+1) = V の m の中）を出す。
 * 実行方法（リポジトリのルートで）:
 *   node code/classes_by_l_mu.js data/affine_certificates_v1_T18.txt 1 data/affine_certificates_v3_T17.txt 3 \
 *     data/affine_certificates_v5_T17.txt 5 data/affine_certificates_v7_T17.txt 7 > data/classes_by_l_mu.txt
 *   （ファイルと V の組を並べる）
 */
'use strict';
const fs = require('fs');
const v2 = x => { if (x === 0n) return 999n; if (x < 0n) x = -x; let c = 0n; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const KEYS = ['ℓ 奇数', 'ℓ 偶数・μ 奇数', 'ℓ 偶数・μ 偶数', 'ℓ 偶数・μ 未定', 'ℓ 未定'];
function run(file, V) {
  let sec = ''; const st = {};
  for (const l of fs.readFileSync(file, 'utf8').split(/\r?\n/)) {
    if (l.startsWith('## 証明できた類')) { sec = 'ok'; continue; }
    if (l.startsWith('## 証明できなかった類')) { sec = 'ng'; continue; }
    if (l.startsWith('##')) { sec = ''; continue; }
    const mm = l.match(/^m ≡ (\d+) \(mod (\d+)\)/); if (!mm || !sec) continue;
    const B = BigInt(mm[1]), A = BigInt(mm[2]);
    // 2^V·E = (2^V − 3)(m + 1) + 2^V = a t + b
    const P = 2n ** V, a = (P - 3n) * A, b = (P - 3n) * (B + 1n) + P;
    const va = v2(a) - V, vb = v2(b) - V; let key;
    if (vb < va) {
      if (vb % 2n === 1n) key = KEYS[0];
      else {
        // 3c = (m + 2) − E/2^ℓ = (A t + B + 2) − (a t + b)/2^(V+ℓ)
        const ca = A - a / 2n ** (V + vb), cb = (B + 2n) - b / 2n ** (V + vb);
        const vca = v2(ca), vcb = v2(cb);
        key = vcb < vca ? (vcb % 2n === 1n ? KEYS[1] : KEYS[2]) : KEYS[3];
      }
    } else key = KEYS[4];
    const d = Number(2n ** (V + 1n)) / Number(A);
    st[key] = st[key] || { ok: 0, ng: 0 }; st[key][sec] += d;
  }
  const out = [`## ${file}（v2(m+1) = ${V}）: 区分 | 証明できた密度 | できなかった密度 | できなかった割合`];
  for (const k of KEYS) if (st[k]) out.push(`${k} | ${st[k].ok.toFixed(6)} | ${st[k].ng.toFixed(6)} | ${(st[k].ng / (st[k].ok + st[k].ng)).toFixed(4)}`);
  return out.join('\n');
}
const a = process.argv.slice(2);
const res = ['# K16 の証明書の一覧の、ℓ・μ による分類', '# 生成: node code/classes_by_l_mu.js ' + a.join(' ')];
for (let i = 0; i < a.length; i += 2) res.push(run(a[i], BigInt(a[i + 1])));
console.log(res.join('\n\n'));
