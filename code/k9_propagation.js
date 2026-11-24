/*
 * k9_propagation.js — 予想 K9 の十分性のための「3 値伝播」を試し、実際のブロック列と比べる
 *
 * 何を計算するか:
 *   v2(m+1) = 1 かつ v2(3h+1) が奇数の m（5 ≤ m ≤ M、h = (m+1)/2）について、次の 3 つを調べる。
 *   1. 交互の局面を仮定した抽象的なブロック E, O の所属を、3 値（入る / 入らない / 未定）で伝播させて決める。
 *        E … 1 つ前の間隔が m+1 の、偶数番目のブロック
 *        O … 1 つ前の間隔が m+2 の、奇数番目のブロック
 *      規則は漸化式 R（[非形式証明] K8）の (i)〜(iii) を、交互の場合に当てはめたもの。
 *        E: 奇数 d は入る。2x は「x ∉ E かつ h+x ∉ O」のとき入る。
 *        O: 奇数 d ≤ m−2 は「h+(d+1)/2 ∉ E」のとき入る。d = m は入る。2x は「x ∉ O かつ 2x ≠ h−1」のとき入る。
 *   2. 伝播で E, O が完全に決まるかどうか。
 *   3. 実際の R のブロック列（j ≥ 2）が、何番目のブロックから E, O に一致し、その後ずっと一致し続けるか。
 *
 * 実行方法（リポジトリのルートで）:
 *   node code/k9_propagation.js 400 > data/k9_propagation.txt
 */
'use strict';

const R = require('./block_rule');
const M = +(process.argv[2] || 400);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };

function propagate(m) {
  const h = (m + 1) / 2;
  const E = new Int8Array(m + 1).fill(-1), O = new Int8Array(m + 1).fill(-1);
  const not = v => (v < 0 ? -1 : 1 - v);
  const and = (a, b) => (a === 0 || b === 0 ? 0 : a === 1 && b === 1 ? 1 : -1);
  let changed = true;
  while (changed) {
    changed = false;
    for (let d = 1; d <= m; d++) {
      let v;
      if (d % 2) v = 1;
      else { const x = d / 2; v = and(not(E[x]), h + x <= m ? not(O[h + x]) : 1); }
      if (E[d] < 0 && v >= 0) { E[d] = v; changed = true; }
      if (d % 2) { const e = h + (d + 1) / 2; v = e <= m ? not(E[e]) : 1; }
      else { const x = d / 2; v = d === h - 1 ? 0 : not(O[x]); }
      if (O[d] < 0 && v >= 0) { O[d] = v; changed = true; }
    }
  }
  return { E, O, h };
}

const out = ['# K9 の十分性のための 3 値伝播と、実際のブロック列との比較', `# 生成: node code/k9_propagation.js ${M}`,
  '# 列: m | 伝播で決まらなかった (ブロック, d) の個数 | 伝播で h ∉ O が確定したか | 実際のブロック列が E/O に一致し始める j（その後ずっと一致）'];
let full = 0, undetermined = [], converge = 0;
for (let m = 5; m <= M; m += 4) {
  if (v2(m + 1) !== 1) continue;
  const h = (m + 1) / 2;
  if (v2(3 * h + 1) % 2 !== 1) continue;
  const { E, O } = propagate(m);
  let unk = 0; for (let d = 1; d <= m; d++) { if (E[d] < 0) unk++; if (O[d] < 0) unk++; }
  const hO = O[h] === 0 ? 'はい' : O[h] === 1 ? 'いいえ（h ∈ O）' : '未定';
  let first = '—';
  if (unk === 0) {
    full++;
    const p = R.periods(m);
    let prev = null, f = -1, stays = true;
    for (let j = 0; j < p.preBlocks + 2 * p.periodBlocks; j++) {
      prev = R.nextBlock(m, prev);
      if (j < 2) continue;
      const T = j % 2 ? O : E;
      let eq = true; for (let d = 1; d <= m; d++) if (prev.S[d] !== T[d]) { eq = false; break; }
      if (eq && f < 0) f = j;
      if (!eq && f >= 0) stays = false;
    }
    first = f >= 0 && stays ? String(f) : '一致しない';
    if (f >= 0 && stays) converge++;
  } else undetermined.push(m);
  out.push(`m=${m} | ${unk} | ${hO} | ${first}`);
}
out.push('');
out.push(`伝播で完全に決まった m: ${full} 個（そのうち実際のブロック列が収束したもの ${converge} 個）`);
out.push(`伝播で未定が残った m: ${undetermined.join(', ')}`);
process.stdout.write(out.join('\n') + '\n');
