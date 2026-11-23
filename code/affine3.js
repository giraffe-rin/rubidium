/*
 * affine3.js — 1 次式の証明書（K16、affine_certificate.js）に 3 値の論理を入れたもの
 *
 * 何を計算するか:
 *   affine_certificate.js の certify と同じく、類 m = A·t + B（t ≥ 0）で距離を t の 1 次式として扱い、
 *   節点（前周期 p、周期 L）ごとに「距離 x がブロックに入るか」を求める。違いは次の点だけ。
 *     - 偶奇や K3 の値（v2 の偶奇）が t によって決まらないとき、類を分けずに「不明」(U) として計算を続ける。
 *     - 規則 R の (i)(ii)(iii) は 3 値の論理で組み合わせる（否定：U は U。「かつ」：F があれば F、すべて T なら T、ほかは U）。
 *     - 間隔（h が入るか）が U になった節点があれば失敗。
 *     - 周期の始まりの節点 p の値は、1 つ前を p−1（p = 0 なら K3）として求めた値 r₀ と、p+L−1 として求めた値 r₁ の
 *       「共通部分」（一致すればその値、違えば U）とする。r₁ は節点 p の値に依存するので、節点 p の値を r₀ から始めて
 *       「共通部分」に置き換える計算を、値が変わらなくなるまで繰り返す（値は U の方向にしか変わらないので必ず止まる）。
 *       止まったとき、節点 p の各値は j = p（r₀ による）と j = p + qL（r₁ と帰納法による）の両方で正しい。
 *   健全性：U 以外の値は、t ≥ t_min のすべての m で正しい（K16 のログの証明で、Split の代わりに「主張しない」とするだけ）。
 *   出力（CLI）：ファイルの「証明できなかった類」（または指定した類）について、p, L を推測して certify3 を試し、証明できた類を出す。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/affine3.js <証明書の一覧のファイル> <v> > data/affine3_<名前>.txt
 *   モジュールとして: require('./affine3').certify3(A, B, p, L, maxFacts)
 */
'use strict';
const { guess } = require('./affine_certificate');
const fs = require('fs');
const T = 1, F = 0, U = 2;
const not = x => (x === U ? U : 1 - x);
const and3 = (...xs) => (xs.includes(F) ? F : xs.every(x => x === T) ? T : U);
const v2n = x => { if (x === 0) return Infinity; let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
class Fail extends Error {}

function certify3(A, B, p, L, maxFacts) {
  const M = { a: A, b: B }, H = { a: A / 2, b: (B + 1) / 2 };
  let tmin = 0;
  const raise = t => { if (t > tmin) tmin = t; };
  const le = (x, y) => { const a = y.a - x.a, b = y.b - x.b; if (a > 0) { raise(Math.ceil(-b / a)); return true; } if (a < 0) { raise(Math.floor(b / -a) + 1); return false; } return b >= 0; };
  const eq = (x, y) => { if (x.a === y.a) return x.b === y.b; const t = (y.b - x.b) / (x.a - y.a); if (Number.isInteger(t) && t >= 0) raise(t + 1); return false; };
  const par = x => (x.a % 2 !== 0 ? U : ((x.b % 2) + 2) % 2 === 1 ? T : F);   // T = 奇数、F = 偶数、U = t による
  const half = x => ({ a: x.a / 2, b: x.b / 2 });
  const k3 = x => { if (x.b === 0) throw new Fail('定数項 0'); const vb = v2n(x.b); if (x.a === 0 || v2n(x.a) > vb) return vb % 2 === 0 ? T : F; return U; };
  const over = new Map();   // 節点 p の値（共通部分）。キーは "a,b"
  let memo, busy;
  const prevOf = (node, alt) => (node === p && alt) ? p + L - 1 : node - 1;
  const gap = node => mem(node, H, 0);
  function raw(node, x, alt) {   // 節点 node の値を、1 つ前の節点（alt で選ぶ）から R で求める
    const pr = prevOf(node, alt);
    if (pr < 0) return k3(x);
    const px = par(x); if (px === U) return U;
    const i = px === F ? mem(node, half(x), alt) : F;
    const g2 = gap(pr); let ii = F, iii = F;
    if (g2 === U) ii = U;
    else {
      const sx = { a: A + x.a, b: B + (g2 === T ? 2 : 1) + x.b }; const ps = par(sx);
      if (ps === U) ii = U; else if (ps === F) { const e = half(sx); if (le(e, M)) ii = mem(pr, e, 0); }
      if (g2 === T && eq(x, { a: H.a, b: H.b - 1 })) iii = T;
    }
    return and3(not(i), not(ii), not(iii));
  }
  let dirty = false;
  function mem(node, x, alt) {
    if (node === p && alt === 0) {   // 節点 p の値は必ず表 over から読む（初めて使う距離は r₀ を入れ、もう一度計算し直す印を付ける）
      const k = x.a + ',' + x.b; if (over.has(k)) return over.get(k);
      const bk = 'raw0,' + k; if (busy.has(bk)) throw new Fail('依存が循環'); busy.add(bk);
      const r = raw(p, x, 0); busy.delete(bk); over.set(k, r); dirty = true; return r;
    }
    const key = node + ',' + alt + ',' + x.a + ',' + x.b;
    if (memo.has(key)) return memo.get(key);
    if (busy.has(key)) throw new Fail('依存が循環');
    if (memo.size + over.size > maxFacts) throw new Fail('事実が多すぎる');
    busy.add(key); const res = raw(node, x, alt); busy.delete(key); memo.set(key, res); return res;
  }
  const meet = (x, y) => (x === y ? x : U);
  let gaps;
  for (let iter = 0; iter < 10000; iter++) {
    memo = new Map(); busy = new Set(); dirty = false;
    gaps = [];
    for (let n = 0; n < p + L; n++) { const g = gap(n); if (g === U) throw new Fail('間隔が不明（節点 ' + n + '）'); gaps.push(g); }
    // 表 over のすべての距離について、r₀ と r₁ の共通部分に置き換える（途中で表が増えたら、その距離も調べる）
    const done = new Set();
    for (;;) {
      const todo = [...over.keys()].filter(k => !done.has(k)); if (!todo.length) break;
      for (const k of todo) {
        done.add(k); const [a, b] = k.split(',').map(Number); const x = { a, b };
        const v0 = raw(p, x, 0), v1 = mem(p, x, 1), nv = meet(v0, v1);
        if (nv !== over.get(k)) { over.set(k, nv); dirty = true; }
      }
    }
    if (!dirty) return { tmin, gaps, n: memo.size + over.size };
  }
  throw new Fail('固定点に達しない');
}
module.exports = { certify3, Fail };

if (require.main === module) {
  const [file, vs] = process.argv.slice(2); const v = +vs;
  const open = []; let sec = '';
  for (const l of fs.readFileSync(file, 'utf8').split(/\r?\n/)) {
    if (/^## (証明できなかった類|まだ決まらない類)/.test(l)) { sec = 'ng'; continue; }
    if (l.startsWith('##')) { sec = ''; continue; }
    const mm = l.match(/^m ≡ (\d+) \(mod (\d+)\)/); if (sec === 'ng' && mm) open.push([+mm[2], +mm[1]]);
  }
  const done = [], fail = {};
  for (const [A, B] of open) {
    const t = Math.max(0, Math.ceil((3000 - B) / A)), m = A * t + B;
    const pl = guess(m, 300) || guess(m, 600); let res = null, why = '周期を推測できない';
    if (pl) tries: for (const mult of [1, 2, 3, 4]) for (const extra of [0, 1, 2, 4, 8]) {
      try { res = certify3(A, B, pl[0] + extra * pl[1], mult * pl[1], 300000); res.p = pl[0] + extra * pl[1]; res.L = mult * pl[1]; break tries; }
      catch (e) { if (e instanceof Fail) why = e.message.replace(/（節点 \d+）/, ''); else throw e; }
    }
    if (res) done.push({ A, B, ...res }); else fail[why] = (fail[why] || 0) + 1;
  }
  const dens = cls => cls.reduce((s, c) => s + 2 ** (v + 1) / c.A, 0);
  const out = [`# 3 値の 1 次式の証明書（${file} の未証明の類、v2(m+1) = ${v}）`, `# 生成: node --stack-size=65500 code/affine3.js ${file} ${v}`,
    `未証明の類: ${open.length} 個（密度 ${dens(open.map(([A, B]) => ({ A, B }))).toFixed(6)}）`,
    `新しく証明できた類: ${done.length} 個（密度 ${dens(done).toFixed(6)}）`,
    `失敗の理由: ${Object.entries(fail).map(([w, c]) => `${w} ${c}`).join('、')}`, '', '## 新しく証明できた類: m ≡ B (mod A) | M_min | 型 | 事実の個数'];
  done.sort((x, y) => x.A - y.A || x.B - y.B);
  for (const c of done) { const g = c.gaps.join(''); out.push(`m ≡ ${c.B} (mod ${c.A}) | ${c.A * c.tmin + c.B} | ${g.slice(0, c.p) || '-'} | ${g.slice(c.p)} | ${c.n}`); }
  console.log(out.join('\n'));
}
