/*
 * affine_certificate.js — m の合同類ごとに、開始局面の間隔の型を「t についての 1 次式の証明書」で示す
 *
 * 何を計算するか:
 *   m の合同類 m = A·t + B（A は 2 の累乗、B は奇数、t ≥ 0 は整数の変数）を考える。
 *   ブロック漸化式 R（notes/2026-11-23-claude-1-proof-structure.md の K8 / H(j)）の各段で出てくる距離を、
 *   t の 1 次式 a·t + b（a, b は整数）のまま扱う。
 *   - 偶奇：a が偶数なら b の偶奇で決まる。a が奇数なら t の偶奇による（→ 類を 2 つに分ける）。
 *   - 定理 K3 の v2(x) の偶奇：a = 0 か v2(a) > v2(b) なら v2(b) で決まる。そうでなければ類を分ける。
 *   - 大小（e ≤ m など）と等号（d = h−1）：t が十分大きいときの答えを使い、それが正しくなる t の下限 t_min を記録する。
 *   ブロックの番号を「前周期 p、周期 L」で 0..p+L−1 の節点にまとめ、各節点の S（必要な距離だけ）と間隔を記号で求める。
 *   周期の始まりの節点 p は、2 通りの前のブロック（p−1 と p+L−1、p = 0 なら K3 と L−1）から同じ値になることを確かめる。
 *   これが成り立てば、t ≥ t_min のすべての m（m ≥ M_min = A·t_min + B）について、
 *   間隔の列は「前周期 p の後、周期 L で繰り返す」ことが、ブロック漸化式から従う（ログの補題を参照）。
 *   (p, L) は類の代表の m（類の中で 3000 以上の最小の m）で数値から推測する（推測が誤っていれば証明書が失敗するだけ）。
 *   周期の始まりで一致しなければ、周期を推測値の 2, 3, 4, 6 倍に、前周期を推測値 + (1, 2, 4, 8)·L にして試す。
 *   それでも失敗したら類を 2 つ（t の偶奇）に分けて、A ≤ 2^T まで繰り返す。
 *
 *   出力: v2(m+1) = v ごとに、証明できた類（m ≡ B (mod A)、M_min、間隔の型）と、証明できなかった類、密度の合計。
 *   さらに、T′ ≤ T ごとに「A ≤ 2^T′ の類で証明できた割合」を出す（分け方は T によらないので、T′ で止めた場合の割合に等しい）。
 *
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/affine_certificate.js 1 14 > data/affine_certificates_v1.txt
 *   （第 1 引数 v、第 2 引数 T。v2(m+1) = v の m を、A ≤ 2^T まで分けて調べる）
 *   モジュールとして: require('./affine_certificate').certify(A, B, p, L, maxFacts)
 */
'use strict';

const { nextBlock } = require('./block_rule');
const v2n = x => { if (x === 0) return Infinity; let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
class Split extends Error {}
class Fail extends Error {}

function certify(A, B, p, L, maxFacts) {
  const M = { a: A, b: B }, H = { a: A / 2, b: (B + 1) / 2 };
  let tmin = 0;
  const raise = t => { if (t > tmin) tmin = t; };
  const le = (x, y) => {                    // x ≤ y（t が十分大きいとき）
    const a = y.a - x.a, b = y.b - x.b;
    if (a > 0) { raise(Math.ceil(-b / a)); return true; }
    if (a < 0) { raise(Math.floor(b / -a) + 1); return false; }
    return b >= 0;
  };
  const eq = (x, y) => {                    // x = y（恒等的に等しいか。1 点だけで等しい場合はその t を除く）
    if (x.a === y.a) return x.b === y.b;
    const t = (y.b - x.b) / (x.a - y.a);
    if (Number.isInteger(t) && t >= 0) raise(t + 1);
    return false;
  };
  const par = x => { if (x.a % 2 !== 0) throw new Split(); return ((x.b % 2) + 2) % 2; };
  const half = x => ({ a: x.a / 2, b: x.b / 2 });
  const k3 = x => {
    if (x.b === 0) throw new Fail('定数項 0');
    const vb = v2n(x.b);
    if (x.a === 0 || v2n(x.a) > vb) return vb % 2 === 0;
    throw new Split();
  };
  const memo = new Map(), busy = new Set();
  const prevOf = (node, alt) => (node === p && alt) ? p + L - 1 : node - 1;
  const gapIsM2 = node => mem(node, H, 0);    // g_node = m+2 ⇔ h ∈ S_node（m は奇数）
  function mem(node, x, alt) {
    const key = node + ',' + alt + ',' + x.a + ',' + x.b;
    if (memo.has(key)) return memo.get(key);
    if (busy.has(key)) throw new Fail('依存が循環');
    if (memo.size > maxFacts) throw new Fail('事実が多すぎる');
    busy.add(key);
    let res;
    const pr = prevOf(node, alt);
    if (pr < 0) res = k3(x);                  // ブロック 0（定理 K3）
    else {
      const odd = par(x) === 1;
      const i = !odd && mem(node, half(x), alt);                    // (i)
      if (i) res = false;
      else {
        const g2 = gapIsM2(pr);
        const s = { a: A + x.a, b: B + (g2 ? 2 : 1) + x.b };        // g_{j−1} + d
        let ii = false;
        if (par(s) === 0) { const e = half(s); if (le(e, M)) ii = mem(pr, e, 0); }   // (ii)
        const iii = !ii && g2 && eq(x, { a: H.a, b: H.b - 1 });    // (iii)
        res = !(ii || iii);
      }
    }
    busy.delete(key); memo.set(key, res);
    return res;
  }
  for (let n = 0; n < p + L; n++) gapIsM2(n);
  // 周期の始まり p：2 通りの導き方で同じ値になること（新しい事実が増えなくなるまで）
  for (;;) {
    const size = memo.size;
    for (const key of [...memo.keys()]) {
      const [n, , a, b] = key.split(',').map(Number);
      if (n !== p) continue;
      if (mem(p, { a, b }, 0) !== mem(p, { a, b }, 1)) throw new Fail('周期の始まりで不一致');
    }
    if (memo.size === size) break;
  }
  const gaps = []; for (let n = 0; n < p + L; n++) gaps.push(gapIsM2(n) ? 1 : 0);
  return { tmin, gaps, n: memo.size };
}

function guess(m, blocks) {
  let pv = null; const g = [];
  for (let j = 0; j < blocks; j++) { pv = nextBlock(m, pv); g.push(pv.g - m - 1); }
  for (let L = 1; L <= 120; L++) for (let p = 0; p <= 150; p++) {
    if (g.length - p < 3 * L) break;
    let ok = true; for (let i = p; i + L < g.length; i++) if (g[i] !== g[i + L]) { ok = false; break; }
    if (ok) return [p, L];
  }
  return null;
}

module.exports = { certify, guess, Split, Fail };

if (require.main === module) {
  const v = +(process.argv[2] || 1), T = +(process.argv[3] || 12);
  const MAXF = 200000, MREP = 3000;
  const done = [], open = [];
  const queue = [[2 ** (v + 1), 2 ** v - 1]];
  while (queue.length) {
    const [A, B] = queue.shift();
    const t = Math.max(0, Math.ceil((MREP - B) / A)), m = A * t + B;   // 類の中で MREP 以上の最小の m
    const pl = guess(m, 600);
    let res = null, why = '';
    if (!pl) why = '周期を推測できない';
    else {
      tries: for (const mult of [1, 2, 3, 4, 6]) for (const extra of [0, 1, 2, 4, 8]) {   // 推測した周期の倍数・長い前周期も試す
        const P0 = pl[0] + extra * pl[1], L0 = mult * pl[1];
        try { res = certify(A, B, P0, L0, MAXF); res.p = P0; res.L = L0; break tries; }
        catch (e) { if (e instanceof Split) { why = '偶奇が t による'; break tries; } else if (e instanceof Fail) why = e.message; else throw e; }
      }
    }
    if (res) done.push({ A, B, ...res });
    else if (2 * A <= 2 ** T) { queue.push([2 * A, B]); queue.push([2 * A, B + A]); }
    else open.push({ A, B, why });
  }
  const dens = cls => cls.reduce((s, c) => s + 2 ** (v + 1) / c.A, 0);
  const out = [`# 合同類ごとの 1 次式の証明書（v2(m+1) = ${v}、A ≤ 2^${T}）`,
    `# 生成: node --stack-size=65500 code/affine_certificate.js ${v} ${T}`,
    `# 型の表記: 前周期の間隔 | 周期の間隔（間隔 − (m+1)）。M_min 以上のこの類のすべての m で成り立つ。`,
    `証明できた類: ${done.length} 個（v2(m+1) = ${v} の m の中の割合 ${dens(done).toFixed(6)}）`,
    `証明できなかった類: ${open.length} 個（割合 ${dens(open).toFixed(6)}）`, '',
    '## T′ ごとの証明できた割合（A ≤ 2^T′ の類だけを数えたもの）'];
  for (let T2 = v + 1; T2 <= T; T2++) out.push(`T′=${T2}: ${dens(done.filter(c => c.A <= 2 ** T2)).toFixed(6)}`);
  out.push('', '## 証明できた類: m ≡ B (mod A) | M_min | 型 | 事実の個数');
  done.sort((x, y) => x.A - y.A || x.B - y.B);
  for (const c of done) {
    const g = c.gaps.join('');
    out.push(`m ≡ ${c.B} (mod ${c.A}) | ${c.A * c.tmin + c.B} | ${g.slice(0, c.p) || '-'} | ${g.slice(c.p)} | ${c.n}`);
  }
  out.push('', '## 証明できなかった類: m ≡ B (mod A) | 理由');
  open.sort((x, y) => x.B - y.B);
  for (const c of open) out.push(`m ≡ ${c.B} (mod ${c.A}) | ${c.why}`);
  process.stdout.write(out.join('\n') + '\n');
}
