/*
 * k55_check.js — 定理 K55（ρ = v + 1、定理 K47b の族、q = −(2^v − 1) < 0）の鎖の条件 (M+d)/2 ≤ m を、補題 K53 の形から確かめる
 *
 * 何を計算するか:
 *   奇数 v = 3..VMAX、ρ = v + 1、Q = 2^v − 1、3r = 2^ρ − 1、z = ρ/2 について、
 *   c < 2^{ρ−1} の奇数 c ≥ 3 で 1 の個数 ≤ z のすべてを入口とし、鎖の奇数の点（K = v + S、S = それまでの t の和、2 周分）で
 *   厳密な不等式 b·2^{v+S} + c·Q < 3r·2^{v+S} が成り立つかを調べる（S = 0 の点は d = c(3a−1)/2^v で別に扱う：c < 2^v を確かめる）。
 *   この不等式は、d = (ab + cσ·2^{N−K})/r（σ·2^N = Qa + r）について、a が十分大きいとき d ≤ 3a − 4、つまり (M+d)/2 ≤ m を与える。
 *   あわせて、補題 K53 の巡回シフトの形（T(b) = b を右に t 桁回転）を各点で確かめる。
 * 実行方法（リポジトリのルートで）:
 *   node code/k55_check.js 17 > data/k55_check.txt
 */
'use strict';
const VMAX = +(process.argv[2] || 17);
const out = ['# 定理 K55 の鎖の条件の確認（ρ = v + 1）', '# 生成: node code/k55_check.js ' + VMAX, 'v | 入口の個数 | 調べた奇数の点 | 不等式が成り立たない点 | 回転の形と違う点'];
let allOk = true;
for (let v = 3; v <= VMAX; v += 2) {
  const rho = v + 1, z = rho / 2, Q = 2n ** BigInt(v) - 1n, R3 = 2n ** BigInt(rho) - 1n;
  const T = b => { let x = b + R3, t = 0; while (x % 2n === 0n) { x /= 2n; t++; } return [x, t]; };
  const rot = (x, t) => ((x >> BigInt(t)) | (x << BigInt(rho - t))) & R3;
  let nc = 0, np = 0, bad = 0, badRot = 0;
  for (let c = 3n; c < 2n ** BigInt(rho - 1); c += 2n) {
    let p = 0; for (let x = c; x > 0n; x >>= 1n) p += Number(x & 1n); if (p > z) continue;
    nc++; if (c >= 2n ** BigInt(v)) bad++;   // S = 0 の点：c < 2^v
    let b = c, S = 0; const L0 = p;   // 閉路の長さは 1 の個数以下
    for (let i = 0; i < 2 * L0; i++) {
      const [nb, t] = T(b); if (nb !== rot(b, t)) badRot++;
      b = nb; S += t; np++;
      if (!(b * 2n ** BigInt(v + S) + c * Q < R3 * 2n ** BigInt(v + S))) bad++;
    }
  }
  if (bad || badRot) allOk = false;
  out.push(`${v} | ${nc} | ${np} | ${bad} | ${badRot}`);
}
out.push('', allOk ? 'すべての点で成り立つ' : '成り立たない点がある');
console.log(out.join('\n'));
