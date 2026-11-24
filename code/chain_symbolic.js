/*
 * chain_symbolic.js — 族 q·a + r = s·2^N（r = ±1）、m = 3a − 2 の帰納法の 1 段の、E 型ブロックの評価木と O 型ブロックの鎖を、R の 1 次式のまま記号的に評価する
 *
 * 何を計算するか:
 *   N = n1·R + n0（R は十分大きい整数で、偶奇だけを固定する）とし、周期を「m+2 の連（長さ R の 1 次式）と m+1 の個数」の並びで与える。
 *   記号：距離は (αa − c)/2^K（α, c, K は具体的な整数）。β = rα + qc とすると恒等式 r(αa − c) = βa − cs·2^N（定理 K47 の鎖の記述）。
 *   - E 型ブロックの値（E 型の規則）：奇数は入る、v2 = 1 は入らない（補題 K33d）、それ以外は「d/2 が入らず、かつ h + d/2 が 1 つ前のブロックで入らない」。
 *     周期の始まり B では、v2 ≥ 2 の距離は与えた仮定の集合で決める（なければ失敗）。
 *   - O 型ブロックの鎖：入口から、奇数の点での b = β/2^K を T(b) = (b + 3r)/2^{v2(b+3r)} で進める。K と段の数は R の 1 次式で持つ。
 *     b が不動点（T(b) = b、t = 1 または 2）にとどまる区間は、N を越えるか鎖が終わる直前まで一度に進める。
 *     奇数の段の後の E = K + t が N と等しいか越えたら、補題 K59.1（r = ±1 版）で新しい鎖に移る：
 *       E = N：u = v2(r b′ + q c s)、半分にする段 (N − K − 1) + u、新しい α = r b′、c = r c s、K = u、β = b′ + q r c s。
 *       E > N（E − N は具体的な数でなければならない）：半分にする段 N − K − 1、新しい α = r 2^{E−N} b′、c = r c s、K = 0、β = 2^{E−N} b′ + q r c s。
 *     鎖の最後の奇数の段の後の距離（終点）の v2 を求める。v2 ≥ 2 なら、終点の形 (α, c, K)（具体的な数）を求めて、行き先の E 型ブロックで評価する。
 *     c が偶数（v2(c) = γ）の入口では、csX の付値が N + γ なので、越える基準を N + γ とし、上の式の c を c/2^γ に置き換える。
 *     奇数の点で d = h − 1 ちょうど（a の係数 3/2、定数 −3/2）なら、O 型ブロックの規則でその距離は入らないので、鎖はそこで値が決まる。
 *   - 鎖の条件：各奇数の点で d = (ba − cs·2^{N−K})/r が 0 < d ≤ 3a − 4、d ≠ h − 1（a が十分大きいとき）を満たすことを、a の係数で確かめる。
 *     不動点の区間では、区間の始めの係数と、K → ∞ の極限 b/r の両方を確かめる（係数は K について単調）。
 *   出力：評価したすべての E 型の事実（ブロック、距離、値）と、すべての鎖（入口、長さ、越えた回数、終点の v2、段の数の偶奇、値）、失敗した点。
 *   族は引数で選ぶ：k58（5a + 1 = 7·2^N、N = 2R + 3、R 偶数）、k34（5a + 1 = 3·2^N、N = 2R + 3、R 奇数）、
 *   k33-1・k33-3（a = 3·2^e + 1、e = 2R + 1、e ≡ 1・3 (mod 4)）。
 * 実行方法（リポジトリのルートで）:
 *   node code/chain_symbolic.js k58 k34 k33-1 k33-3 > data/chain_symbolic.txt
 */
'use strict';
// ---- R の 1 次式 ----
const A = (r1, r0) => ({ r1, r0 });
const add = (x, y) => A(x.r1 + y.r1, x.r0 + y.r0), sub = (x, y) => A(x.r1 - y.r1, x.r0 - y.r0), scl = (x, k) => A(x.r1 * k, x.r0 * k), con = k => A(0, k);
const cmp = (x, y) => { const d = sub(x, y); if (d.r1 !== 0) return Math.sign(d.r1); return Math.sign(d.r0); };   // R → ∞ での大小
const eq = (x, y) => x.r1 === y.r1 && x.r0 === y.r0;
const show = x => (x.r1 === 0 ? String(x.r0) : (x.r1 === 1 ? '' : x.r1) + 'R' + (x.r0 === 0 ? '' : (x.r0 > 0 ? '+' : '') + x.r0));
const v2n = x => { x = x < 0n ? -x : x; if (x === 0n) return Infinity; let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const mod2 = x => x % 2 === 0 ? 0 : 1;

function family(name) {
  if (name === 'k58') return { name, q: 5n, r: 1n, s: 7n, N: A(2, 3), Rpar: 0, segs: [['1', A(1, 2)], ['0', 1], ['1', A(1, 0)], ['0', 1]], assume: [[2n, 14n, 0, false]] };
  if (name === 'k34') return { name, q: 5n, r: 1n, s: 3n, N: A(2, 3), Rpar: 1, segs: [['1', A(2, 0)], ['0', 1], ['1', A(1, 0)], ['0', 2], ['1', A(1, 0)], ['0', 2]], assume: [[2n, 6n, 0, false], [3n, 9n, 0, true]] };
  if (name === 'k33-1' || name === 'k33-3') return { name, q: 1n, r: -1n, s: 3n, N: A(2, 1), Rpar: name === 'k33-1' ? 0 : 1, segs: [['1', A(2, 0)], ['0', 1], ['1', A(1, 0)], ['0', 1]], assume: [[2n, -6n, 0, false]] };
  throw new Error('族が不明 ' + name);
}

function run(F) {
  const { q, r, s, N, Rpar } = F; const log = [], fails = [];
  const parOf = x => mod2(((x.r1 % 2) + 2) % 2 * Rpar + ((x.r0 % 2) + 2) % 2);
  // 周期のブロック：E 型ブロックの一覧。各 E 型ブロックについて「1 つ前のブロック」が E 型か、O 型の連の最後か（その連の長さと始まりの E 型ブロック）
  const E = [{ id: 'B' }]; let k = 0;   // E[0] = B
  for (let i = 0; i < F.segs.length; i++) {
    const [t, len] = F.segs[i];
    if (t === '1') { E.push({ pending: true, run: { len, from: E.length - 1 } }); }
    else for (let z = 0; z < len; z++) { const last = E[E.length - 1]; if (last.pending) { last.pending = false; last.prev = 'O'; } else E.push({ prev: 'E', prevId: E.length - 1 }); }
  }
  // 最後の E 型ブロックは次の周期の始まり L
  E.forEach((x, i) => { x.id = i === 0 ? 'B' : i === E.length - 1 ? 'L' : 'E' + i; });
  // 仮定
  const key = (al, c, K) => { while (K > 0 && al % 2n === 0n && c % 2n === 0n) { al /= 2n; c /= 2n; K--; } return al + ',' + c + ',' + K; };
  const assume = new Map(F.assume.map(([al, c, K, v]) => [key(al, c, K), v]));
  const fmt = (al, c, K) => `(${al}a${c < 0n ? '+' + (-c) : '−' + c})/2^${K}`;
  const v2dist = (al, c, K) => { const beta = r * al + q * c; const v = v2n(beta); if (v === Infinity) return Infinity; return v - K; };   // v2(β) < N のとき
  const memo = new Map();
  function Eval(ei, al, c, K) {
    const kk = ei + ':' + key(al, c, K); if (memo.has(kk)) return memo.get(kk);
    const t = v2dist(al, c, K); let val;
    if (t < 0) { fails.push(`整数でない距離 ${fmt(al, c, K)}`); val = null; }
    else if (t === 0) val = true; else if (t === 1) val = false;
    else if (ei === 0) { const k2 = key(al, c, K); if (assume.has(k2)) val = assume.get(k2); else { fails.push(`B で仮定にない距離 ${fmt(al, c, K)}（v2 ${t}）`); val = null; } }
    else {
      const first = Eval(ei, al, c, K + 1);
      // e = h + d/2 = (3a − 1)/2 + (αa − c)/2^{K+1} = ((3·2^K + α)a − (2^K + c))/2^{K+1}
      const al2 = 3n * 2n ** BigInt(K) + al, c2 = 2n ** BigInt(K) + c, K2 = K + 1;
      // e ≤ m ⇔ (al2/2^K2)·a − c2/2^K2 ≤ 3a − 2（a が十分大きい）
      const lam = Number(al2) / 2 ** K2; let le = lam < 3 || (lam === 3 && Number(c2) / 2 ** K2 >= 2);
      let second = false;
      if (first === true) { val = false; log.push(`E 型の事実：${x0(ei)}：${fmt(al, c, K)}（v2 ${t}）不（d/2 が入る）`); memo.set(kk, val); return val; }   // 第 1 項が入るなら、第 2 項は評価しない
      if (le) { const x = E[ei]; second = x.prev === 'E' ? Eval(x.prevId, al2, c2, K2) : Chain(x.run, al2, c2, K2, ei); }
      val = (first === null || second === null) ? null : (!first && !second);
      log.push(`E 型の事実：${x0(ei)}：${fmt(al, c, K)}（v2 ${t}）${val === null ? '不明' : val ? '入' : '不'}`);
    }
    memo.set(kk, val); return val;
  }
  const x0 = ei => (ei < 0 ? '連の中の h' : E[ei].id);
  function T(b) { let x = b + 3n * r, t = 0; if (x === 0n) return null; while (x % 2n === 0n) { x /= 2n; t++; } return [x, t]; }
  function checkPoint(b, c, K, label) {   // 奇数の点 d = (ba − c(qa + r)/2^K)/r の a の係数と定数（K は具体的な数）
    const lam = (Number(b) - Number(c) * Number(q) / 2 ** K) / Number(r), kap = -Number(c) / 2 ** K;
    if (lam === 1.5 && kap === -1.5) return 'H';   // d = h − 1：O 型ブロックの規則で入らない
    const ok = (lam > 0 || (lam === 0 && kap > 0)) && (lam < 3 || (lam === 3 && kap <= -4));
    if (!ok) fails.push(`鎖の条件が成り立たない（${label}、b = ${b}、c = ${c}、K = ${K}、係数 ${lam}）`);
    return 'ok';
  }
  // 不動点の区間（K は区間の始めの具体的な値から N − 1 − t まで）での鎖の条件
  //   d = (ba − cs·2^{N−K})/r。極限の係数は b/r。b/r < 3 ならよい。b/r = 3 なら d = 3a − (cs/r)·2^{N−K} で、N − K ≥ 1 + t から (cs/r)·2^{1+t} ≥ 4 を要求する。
  //   d = h − 1 = (3a − 3)/2 は、λ(K) = 3/2 となる K で定数 −c/2^K = −3/2 のときに限る（K が小さいときだけ起こりうるので、checkPoint で調べる）。
  function segCheck(b, c, t) {
    const lim = Number(b) / Number(r);
    if (!(lim > 0)) { fails.push('不動点 b = ' + b + ' の極限の係数が 0 以下'); return; }
    if (lim > 3) { fails.push('不動点 b = ' + b + ' の極限の係数が 3 を超える'); return; }
    if (lim === 3) { const k = Number(c) * Number(s) / Number(r); if (!(k > 0 && k * 2 ** (1 + t) >= 4)) fails.push('不動点 b = ' + b + '：区間の終わりで d ≤ 3a − 4 が成り立たない'); }
    if (lim === 1.5) fails.push('不動点 b = ' + b + '：極限の係数が 3/2');
  }
  function Chain(runInfo, al, c, K0, fromEi) {
    const n = runInfo.len, toEi = runInfo.from; const desc = [];
    let beta = r * al + q * c, v = v2n(beta);
    if (v === Infinity || v < K0) { fails.push(`入口の形が扱えない ${fmt(al, c, K0)}`); return null; }
    let steps = A(0, v - K0), K = A(0, v), b = beta / 2n ** BigInt(v), j = A(0, 0), cross = 0, endV2 = null, endForm = null;
    let cc = c, hStop = false;
    for (let guard = 0; guard < 10000; guard++) {
      // ここは奇数の点（j 番目の奇数の段の前）。j は済んだ奇数の段の数
      if (K.r1 === 0 && checkPoint(b, cc, K.r0, fmt(al, c, K0)) === 'H') { hStop = true; desc.push(`b=${b}（d = h − 1 で止まる）`); break; }
      const gam = v2n(cc), Ng = add(N, con(gam)), co = cc / 2n ** BigInt(gam);   // c が偶数なら、越える基準は N + v2(c)
      const Tb = T(b); if (!Tb) { fails.push('b + 3r = 0'); return null; }
      const [b2, t] = Tb; const Eexp = add(K, con(t)); const isLast = eq(add(j, con(1)), n); const rel = cmp(Eexp, Ng);
      if (rel < 0) {
        if (b2 === b && !isLast && (t === 1 || t === 2)) {   // 不動点の区間を一度に進める
          // 進める段の数 k：j + k ≤ n − 1 かつ K + k t ≤ N − 1 − t（次の段でもまだ越えない位置まで）、k ≥ 1
          const lim1 = sub(sub(n, con(1)), j);
          let lim2 = sub(sub(Ng, con(1 + t)), K); if (t === 2) { const p = parOf(lim2); lim2 = A(lim2.r1 / 2, (lim2.r0 - p) / 2); if (!Number.isInteger(lim2.r1)) { fails.push('不動点の区間の長さが整数でない'); return null; } }
          const kst = cmp(lim1, lim2) <= 0 ? lim1 : lim2;
          if (cmp(kst, con(1)) >= 0) {
            // 区間の始めと極限で鎖の条件
            segCheck(b, cc, t);
            K = add(K, scl(kst, t)); j = add(j, kst); steps = add(steps, scl(kst, t)); desc.push(`b=${b}×${show(kst)}`); continue;
          }
        }
        if (isLast) { endV2 = t - 1; steps = add(steps, con(1)); if (endV2 >= 2) { if (K.r1 !== 0) { fails.push('終点の形が R による'); return null; } const bp = 2n ** BigInt(K.r0) * (b + 3n * r); endForm = [(bp - q * cc) / r, cc, K.r0 + t]; } desc.push(`b=${b}`); break; }
        steps = add(steps, con(t)); K = Eexp; desc.push(`b=${b}`); b = b2; j = add(j, con(1)); continue;
      }
      // 越える
      cross++;
      const NK1 = sub(sub(Ng, K), con(1)); if (NK1.r1 !== 0) { fails.push('越える場面で N − K − 1 が R による'); return null; }
      const nk1 = NK1.r0;
      if (rel === 0) {
        const inner = r * b2 + q * co * s; const u = v2n(inner); if (u === Infinity) { fails.push('u = ∞'); return null; }
        if (isLast) { endV2 = nk1 + u; steps = add(steps, con(1)); endForm = [2n ** BigInt(nk1) * b2 * r, 2n ** BigInt(nk1) * co * s * r, 0]; desc.push(`b=${b}→越える(E=N+${gam},u=${u})`); break; }
        steps = add(steps, con(1 + nk1 + u)); const al2 = r * b2, c2 = r * co * s; const bt = b2 + q * r * co * s; desc.push(`b=${b}→越える(E=N+${gam},u=${u},c′=${c2})`);
        cc = c2; K = con(u); b = bt / 2n ** BigInt(u); j = add(j, con(1)); continue;
      } else {
        const off = sub(Eexp, Ng); if (off.r1 !== 0) { fails.push('E − N が R による'); return null; }
        const o = off.r0;
        if (isLast) { endV2 = nk1; steps = add(steps, con(1)); endForm = [2n ** BigInt(nk1 + o) * b2 * r, 2n ** BigInt(nk1) * co * s * r, 0]; desc.push(`b=${b}→越える(E=N+${gam}+${o})`); break; }
        steps = add(steps, con(1 + nk1)); const al2 = r * 2n ** BigInt(o) * b2, c2 = r * co * s; const bt = r * al2 + q * c2; desc.push(`b=${b}→越える(E=N+${gam}+${o},c′=${c2})`);
        cc = c2; K = con(0); b = bt; if (b % 2n === 0n) { fails.push('越えた後の β が偶数'); return null; } j = add(j, con(1)); continue;
      }
    }
    // 終点の値
    let endVal;
    if (hStop) endVal = false;
    else if (endV2 === 0) endVal = true; else if (endV2 === 1) endVal = false;
    else endVal = Eval(toEi, endForm[0], endForm[1], endForm[2]);
    const par = parOf(steps); const val = endVal === null ? null : (par === 0 ? endVal : !endVal);
    log.push(`鎖：${x0(fromEi)} の評価から（${x0(toEi)} まで、長さ ${show(n)}）：入口 ${fmt(al, c, K0)}、軌道 ${desc.join(' ')}、越えた回数 ${cross}、終点の v2 ${hStop ? '（d = h − 1）' : endV2}${endForm && endV2 >= 2 ? '（' + fmt(...endForm) + '）' : ''}、段数の偶奇 ${par}、値 ${val === null ? '不明' : val ? '入' : '不'}`);
    return val;
  }
  // 評価：各 E 型ブロック（B 以外）での h と、L での仮定の距離
  const res = [];
  // 連の中の h の鎖：各連（E 型ブロック X から長さ ℓ）について、長さ n の鎖の値（n < ℓ で入、n = ℓ で不 を期待）
  const runs = E.filter(x => x.run).map(x => x.run);
  for (const ru of runs) {
    const ns = [con(1), con(2), con(3), sub(ru.len, con(2)), sub(ru.len, con(1)), ru.len, sub(A(1, 0), con(1)), A(1, 0), A(1, 1), A(1, 2), A(1, 3)].filter(n => cmp(n, con(1)) >= 0 && cmp(n, ru.len) <= 0);
    const seen = new Set(); const vals = [];
    for (const n of ns) { const k = show(n); if (seen.has(k)) continue; seen.add(k);
      const v = Chain({ len: n, from: ru.from }, 3n, 1n, 1, -1); const want = eq(n, ru.len) ? false : true;
      vals.push(`n=${k}：${v === null ? '不明' : v ? '入' : '不'}${v === want ? '' : '（期待と違う）'}`); if (v !== want) fails.push('連の h の鎖 ' + k + ' が期待と違う'); }
    res.push(`${E[ru.from].id} からの連（長さ ${show(ru.len)}）の h：${vals.join(' ')}`);
  }
  for (let ei = 1; ei < E.length; ei++) res.push(`${E[ei].id} で h：${Eval(ei, 3n, 1n, 1) ? '入' : '不'}`);
  const rep = F.assume.map(([al, c, K, v]) => { const got = Eval(E.length - 1, al, c, K); return `L で ${fmt(al, c, K)}：${got ? '入' : '不'}（仮定 ${v ? '入' : '不'}、${got === v ? '再現' : '再現しない'}）`; });
  return { E, res, rep, log, fails };
}

const out = ['# 鎖と評価木の記号的な評価（R の 1 次式で）', '# 生成: node code/chain_symbolic.js ' + process.argv.slice(2).join(' ')];
for (const nm of process.argv.slice(2)) {
  const F = family(nm), R = run(F);
  out.push('', `## ${nm}：q = ${F.q}、r = ${F.r}、s = ${F.s}、N = ${show(F.N)}、R の偶奇 ${F.Rpar}、周期 ${F.segs.map(([t, l]) => t === '1' ? '1^{' + show(l) + '}' : '0'.repeat(l)).join(' ')}`,
    'E 型ブロックでの h：' + R.res.join('、'), '仮定の再現：' + R.rep.join('、'), ...R.log.map(x => '  ' + x), `失敗：${R.fails.length ? R.fails.join('；') : 'なし'}`);
}
console.log(out.join('\n'));
