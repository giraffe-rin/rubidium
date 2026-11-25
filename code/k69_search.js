// k69_search.js — v2(m+1) = 5（m + 1 = 32u）で Lean の定理がない u mod MOD の各類について、u = r の型の語を漸化式 R で求め、
//   k69_gen.js が通る類を挙げる。K29（u ≡ 1 (mod 4)）と K38（u ≡ 3 (mod 4)、w = v2(u+1) が 3 または 6 以上）の類は除く。
// 使い方（lean/ で）: node ../code/k69_search.js MOD ../code/k69_gen.js ../code/block_rule.js
'use strict';
const { execFileSync } = require('child_process');
const [MODs, gen, br] = process.argv.slice(2); const MOD = +MODs;
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const covered = u => u % 4 === 1 || (u % 4 === 3 && (v2(u + 1) === 3 || v2(u + 1) >= 6));
const ok = [];
for (let r = 3; r < MOD; r += 4) {
  if (covered(r) && covered(r + MOD)) continue;
  if (v2(r + 1) === 3) continue;
  let u = r; while (u < 32) u += MOD;
  const line = execFileSync(process.execPath, [br, 'periods', String(32 * u - 1), String(32 * u - 1)], { encoding: 'utf8' }).split(/\r?\n/).find(l => l.startsWith('m='));
  const f = line.split('|'), t = +f[4].split(',')[0], w = f[5].trim();
  if (t !== 0 || !w.endsWith('000')) continue;
  try { const o = execFileSync(process.execPath, [gen, process.platform === 'win32' ? 'NUL' : '/dev/null', String(MOD), w, String(r)], { encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }); if (o.includes('ok')) { ok.push([w, r]); console.log('OK', w, r); } } catch (e) {}
}
console.log('TOTAL', ok.length, JSON.stringify(ok));
