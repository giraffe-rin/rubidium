/*
 * check_conjectures.js — notes/2026-11-23-claude-1-conjectures.md の予想 K1〜K8 を、指定した範囲で確かめる
 *
 * 何を計算するか:
 *   全探索の表（solver_dp.js と solver_retro.js が一致したもの）を使って、各予想を範囲内で確かめる。
 *   予想 K8（漸化式 R）を前提にした計算は、それとわかるように「R 経由」と書いて別に出す。
 *   （AGENTS.md 第 4 節: [予想] を前提にした結果は [予想] のまま。）
 *   1 つでも反例が見つかれば、その局面を出力する（止まらずに最後まで調べる）。
 *
 *   記号: v2(x) は x を割り切る 2 の最大べきの指数。m が奇数なら h = (m+1)/2。
 *   A 行 … すべての p で (r, p) が P になる行 r（r = 0 を含む）。
 *
 * 実行方法（リポジトリのルートで。全体で数十秒）:
 *   node code/check_conjectures.js 100 10000 1000 200 > data/conjecture_checks.txt
 *   引数: 全探索で調べる m の上限, r の上限, K3 で調べる m の上限, R 経由で調べる m の上限
 */
'use strict';

const A = require('./solver_dp');
const B = require('./solver_retro');
const R = require('./block_rule');

const MMAX = +(process.argv[2] || 100);
const N = +(process.argv[3] || 10000);
const K3MAX = +(process.argv[4] || 1000);
const RMAX = +(process.argv[5] || 200);

const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const out = [];
const log = s => out.push(s);
const fails = {};
const fail = (k, msg) => { (fails[k] = fails[k] || []).push(msg); };
const pset = row => { const s = []; for (let p = 0; p < row.length; p++) if (row[p] === 'P') s.push(p); return s; };

log('# restricted-stone-game 予想 K1〜K8 の検証');
log(`# 生成: node code/check_conjectures.js ${MMAX} ${N} ${K3MAX} ${RMAX}`);
log('');

// ---- 全探索の表で調べる（2 ≤ m ≤ MMAX, 0 ≤ r ≤ N） ----
for (let m = 2; m <= MMAX; m++) {
  const t = A.solve(m, N), tb = B.solve(m, N);
  for (let r = 0; r <= N; r++) if (t[r] !== tb[r]) { console.error(`ソルバー不一致 m=${m} r=${r}`); process.exit(1); }
  const odd = m % 2 === 1, h = (m + 1) / 2;
  const evenV = v2(m + 1) % 2 === 0;
  let a = 0, firstA = null;
  for (let r = 1; r <= N; r++) {
    const S = pset(t[r]);
    // K1: P になる p は「全部」「1 つ」「なし」のどれか
    if (!(S.length === 0 || S.length === 1 || S.length === m + 1)) fail('K1', `m=${m} r=${r} P={${S}}`);
    if (S.length === m + 1) {
      // K2(a): A 行の間隔は m+1 か m+2
      const g = r - a;
      if (g !== m + 1 && g !== m + 2) fail('K2', `m=${m} 間隔 ${g}（A 行 ${a} → ${r}）`);
      // K2(c): 間隔 m+2 なら距離 m+1 の行は {h}
      if (g === m + 2 && !(odd && pset(t[r - 1]).length === 1 && t[r - 1][h] === 'P')) fail('K2', `m=${m} r=${r - 1} 距離 m+1 の行が {h} でない`);
      if (firstA === null) firstA = r;
      a = r;
      continue;
    }
    const d = r - a;
    // K2(b): A 行でない行の P は (r, d)（d ≤ m）か、(r, h)（d = m+1）だけ
    if (S.length === 1) {
      const p = S[0];
      if (!((d <= m && p === d) || (odd && d === m + 1 && p === h))) fail('K2', `m=${m} r=${r} d=${d} P={${p}}`);
    }
    if (d > m + 1) fail('K2', `m=${m} r=${r} 距離 ${d} > m+1`);
  }
  // K4: 開始局面の P がちょうど m+1 の倍数 ⇔ v2(m+1) が偶数
  let mult = true;
  for (let n = 1; n <= N; n++) if ((t[n][0] === 'P') !== (n % (m + 1) === 0)) { mult = false; break; }
  if (mult !== evenV) fail('K4', `m=${m} v2(m+1)=${v2(m + 1)} なのに 倍数型=${mult}`);
  // K5: v2(m+1) が奇数なら最初の P 開始局面は m+2
  if (!evenV && firstA !== m + 2) fail('K5', `m=${m} 最初の P 開始局面 ${firstA}`);
  // K6: m ≡ 5 (mod 8) なら (n,0) が P ⇔ n ≡ 0 または m+2 (mod 2m+3)
  if (m % 8 === 5) {
    for (let n = 1; n <= N; n++) {
      const q = n % (2 * m + 3);
      if ((t[n][0] === 'P') !== (q === 0 || q === m + 2)) { fail('K6', `m=${m} n=${n}`); break; }
    }
  }
  // K8: 漸化式 R の表と一致
  const tr = R.table(m, N);
  for (let r = 0; r <= N; r++) if (tr[r] !== t[r]) { fail('K8', `m=${m} r=${r}`); break; }
}

// ---- K3: 最初のブロック（1 ≤ r ≤ m）。r ≤ m の行は m に依らないので、m = K3MAX の表の r ≤ K3MAX で全 m ≤ K3MAX を兼ねる ----
{
  const t = A.solve(K3MAX, K3MAX), tb = B.solve(K3MAX, K3MAX);
  for (let r = 0; r <= K3MAX; r++) if (t[r] !== tb[r]) { console.error('ソルバー不一致（K3）'); process.exit(1); }
  for (let r = 1; r <= K3MAX; r++) {
    const S = pset(t[r]);
    const expect = v2(r) % 2 === 0 ? [r] : [];
    if (S.join() !== expect.join()) fail('K3', `r=${r} P={${S}}`);
  }
  // r ≤ m の行が m に依らないことも、小さい m で直接確かめる
  for (let m = 1; m <= 60; m++) {
    const tm = A.solve(m, m);
    for (let r = 0; r <= m; r++) if (tm[r] !== t[r].slice(0, m + 1)) fail('K3', `m=${m} r=${r} が m=${K3MAX} の表の先頭と違う`);
  }
}

const ranges = {
  K1: `2 ≤ m ≤ ${MMAX}, 0 ≤ r ≤ ${N}, 全 p（全探索）`,
  K2: `2 ≤ m ≤ ${MMAX}, 0 ≤ r ≤ ${N}（全探索）`,
  K3: `1 ≤ r ≤ m ≤ ${K3MAX}（全探索。r ≤ m の行が m に依らないことは m ≤ 60 で直接確認）`,
  K4: `2 ≤ m ≤ ${MMAX}, 1 ≤ n ≤ ${N}（全探索）`,
  K5: `2 ≤ m ≤ ${MMAX}（全探索、r ≤ ${N}）`,
  K6: `m ≡ 5 (mod 8), 5 ≤ m ≤ ${MMAX}, 1 ≤ n ≤ ${N}（全探索）`,
  K8: `2 ≤ m ≤ ${MMAX}, 0 ≤ r ≤ ${N}, 全 p（全探索の表と照合）`,
};
log('## 全探索による検証');
for (const k of ['K1', 'K2', 'K3', 'K4', 'K5', 'K6', 'K8']) {
  const f = fails[k] || [];
  log(`${k}: ${f.length === 0 ? '反例なし' : '反例 ' + f.length + ' 件'} — 範囲 ${ranges[k]}`);
  for (const s of f.slice(0, 20)) log('    ' + s);
}

// ---- R 経由（K8 を前提にした計算。結果は [予想] のまま） ----
log('');
log(`## 漸化式 R 経由の計算（K8 が正しいと仮定。m ≤ ${RMAX}、状態が繰り返すまで回すので n はすべて）`);
const rf = { K4: [], K6: [] };
for (let m = 2; m <= RMAX; m++) {
  const res = R.periods(m);
  // 前周期 + 周期 2 回分のブロックを作る
  let prev = null; let a = 0; const As = [];
  for (let j = 0; j < res.preBlocks + 2 * res.periodBlocks; j++) { prev = R.nextBlock(m, prev); a += prev.g; As.push(a); }
  const T = a;
  const isP = new Uint8Array(T + 1); for (const x of As) isP[x] = 1;
  let mult = true; for (let n = 1; n <= T; n++) if ((isP[n] === 1) !== (n % (m + 1) === 0)) { mult = false; break; }
  if (mult !== (v2(m + 1) % 2 === 0)) rf.K4.push(`m=${m}`);
  if (m % 8 === 5) {
    for (let n = 1; n <= T; n++) { const q = n % (2 * m + 3); if ((isP[n] === 1) !== (q === 0 || q === m + 2)) { rf.K6.push(`m=${m} n=${n}`); break; } }
  }
}
log(`K4（R 経由）: ${rf.K4.length === 0 ? '反例なし' : '反例 ' + rf.K4.join(', ')} — 2 ≤ m ≤ ${RMAX}`);
log(`K6（R 経由）: ${rf.K6.length === 0 ? '反例なし' : '反例 ' + rf.K6.join(', ')} — m ≡ 5 (mod 8), m ≤ ${RMAX}`);
log('K7（周期）: data/block_periods_m2-200.txt を参照');

process.stdout.write(out.join('\n') + '\n');
