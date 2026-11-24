/*
 * check_affine.js — affine_certificate.js が証明した類を、実装 C（行の型による、ブロック漸化式を使わない）で確かめる
 *
 * 何を計算するか:
 *   data/affine_certificates_v*.txt の「証明できた類」の各行（m ≡ B (mod A)、M_min、型）を読む。
 *   各類から、M_min 以上で 100 以上の m を小さい順に最大 C 個（m ≤ MMAX）選ぶ。
 *   code/solver_rowtype.js で n ≤ min(NMAX, (p + 6L)·(m+2)) の A 行を求め、その間隔の列が予測（前周期 + 周期の繰り返し）と一致するかを調べる。
 *   食い違いの数と、調べた m の個数を出す。
 *
 * 実行方法（リポジトリのルートで）:
 *   node code/check_affine.js data/affine_certificates_v1.txt 2 40000 2000000 > data/affine_check_v1.txt
 */
'use strict';

const fs = require('fs');
const Cimpl = require('./solver_rowtype');
const file = process.argv[2], C = +(process.argv[3] || 2), MMAX = +(process.argv[4] || 40000), NMAX = +(process.argv[5] || 2000000);
const lines = fs.readFileSync(file, 'utf8').split(/\r?\n/).filter(l => l.startsWith('m ≡') && l.split('|').length === 5);
let n = 0; const bad = [];
for (const l of lines) {
  const [cls, mmin, pre, per] = l.split('|').map(s => s.trim());
  const [, B, A] = cls.match(/m ≡ (\d+) \(mod (\d+)\)/).map(Number);
  const prefix = pre === '-' ? '' : pre;
  let m = B; while (m < Math.max(+mmin, 100)) m += A;
  for (let c = 0; c < C && m <= MMAX; c++, m += A) {
    const N = Math.min(NMAX, (prefix.length + 6 * per.length) * (m + 2));
    const ty = Cimpl.types(m, N);
    const Arows = []; for (let x = 1; x <= N; x++) if (ty[x] === 0) Arows.push(x);
    const g = Arows.map((x, i) => x - (i ? Arows[i - 1] : 0) - (m + 1));
    let ok = true;
    for (let i = 0; i < g.length; i++) {
      const want = i < prefix.length ? prefix[i] : per[(i - prefix.length) % per.length];
      if (String(g[i]) !== want) { ok = false; break; }
    }
    n++; if (!ok) bad.push(m);
  }
}
const out = [`# 1 次式の証明書の、実装 C による照合（${file}）`, `# 生成: node code/check_affine.js ${file} ${C} ${MMAX} ${NMAX}`,
  `調べた類: ${lines.length} 個、調べた m: ${n} 個。食い違い: ${bad.length === 0 ? 'なし' : bad.join(', ')}`];
process.stdout.write(out.join('\n') + '\n');
