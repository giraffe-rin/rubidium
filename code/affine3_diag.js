/*
 * affine3_diag.js — 3 値の証明書（affine3.js）で「間隔が不明」になる原因を追跡して分類する
 *
 * 何を計算するか:
 *   certify3 と同じ計算をし、間隔（節点 n で h が入るか）が U になったとき、U の値をたどって元を探す。
 *   元の種類：
 *     par(i)  ：(i) の d の偶奇が t による
 *     par(ii) ：(ii) の g + d の偶奇が t による
 *     K3      ：ブロック 0 で v2(d) の偶奇が t による
 *     meet    ：周期の始まりの節点 p で、2 通りの導き方の値が違う
 *   入力の「まだ決まらない類」（または「証明できなかった類」）のそれぞれで、p, L の推測値（倍数 1、ずらし 0）で 1 回だけ試し、
 *   原因の種類ごとの個数と、たどった段数の分布を出す。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/affine3_diag.js <類の一覧のファイル> > data/affine3_diag_<名前>.txt
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
  function explain(node, x, alt, useRaw, depth) {
    if (depth > 5000) return ['深すぎる', depth];
    if (node === p && alt === 0 && !useRaw) { const r0 = raw(p, x, 0); if (r0 !== U) return ['meet', depth]; return explain(p, x, 0, true, depth + 1); }
    const pr = prevOf(node, alt);
    if (pr < 0) return [k3(x) === U ? 'K3' : 'その他', depth];
    const px = par(x); if (px === U) return ['par(i)', depth];
    if (px === F && mem(node, half(x), alt) === U) return explain(node, half(x), alt, false, depth + 1);
    const g2 = gap(pr); if (g2 === U) return explain(pr, H, 0, false, depth + 1);
    const sx = { a: A + x.a, b: B + (g2 === T ? 2 : 1) + x.b }; const ps = par(sx);
    if (ps === U) return ['par(ii)', depth];
    if (ps === F) { const e = half(sx); if (le(e, M) && mem(pr, e, 0) === U) return explain(pr, e, 0, false, depth + 1); }
    return ['その他', depth];
  }
  const meet = (x, y) => (x === y ? x : U);
  let gaps;
  for (let iter = 0; iter < 10000; iter++) {
    memo = new Map(); busy = new Set(); dirty = false;
    gaps = [];
    for (let n = 0; n < p + L; n++) { const g = gap(n); if (g === U) { const e = new Fail('間隔が不明'); e.why = explain(n, H, 0, false, 0); e.node = n; throw e; } gaps.push(g); }
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
  const [file] = process.argv.slice(2);
  const open = []; let sec = '';
  for (const l of fs.readFileSync(file, 'utf8').split(/\r?\n/)) {
    if (/^## (証明できなかった類|まだ決まらない類)/.test(l)) { sec = 'ng'; continue; }
    if (l.startsWith('##')) { sec = ''; continue; }
    const mm = l.match(/^m ≡ (\d+) \(mod (\d+)\)/); if (sec === 'ng' && mm) open.push([+mm[2], +mm[1]]);
  }
  const cnt = {}, depths = {};
  for (const [A, B] of open) {
    const t = Math.max(0, Math.ceil((3000 - B) / A)), m = A * t + B;
    const pl = guess(m, 300) || guess(m, 600); let why = '周期を推測できない';
    if (pl) { try { certify3(A, B, pl[0], pl[1], 300000); why = '証明できた'; }
      catch (e) { if (!(e instanceof Fail)) throw e; if (e.why) { why = e.why[0]; (depths[why] = depths[why] || []).push(e.why[1]); } else why = e.message.replace(/（節点 \d+）/, ''); } }
    cnt[why] = (cnt[why] || 0) + 1;
  }
  const med = a => { const b = [...a].sort((x, y) => x - y); return b[Math.floor(b.length / 2)]; };
  const out = ['# 3 値の証明書で間隔が不明になる原因（' + file + '）', '# 生成: node --stack-size=65500 code/affine3_diag.js ' + file,
    '類: ' + open.length + ' 個（p, L は推測値、倍数 1、ずらし 0 で 1 回だけ試す）', '', '原因 | 類の個数 | たどった段数の最小・中央値・最大'];
  for (const [w, c] of Object.entries(cnt).sort((x, y) => y[1] - x[1])) { const d = depths[w]; out.push(w + ' | ' + c + ' | ' + (d ? Math.min(...d) + ', ' + med(d) + ', ' + Math.max(...d) : '-')); }
  console.log(out.join('\n'));
}
