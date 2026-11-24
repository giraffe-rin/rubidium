// k68_asm11100.js — k68_gen11100.js の出力と K67b.lean の雛形から lean/Rubidium/K68c.lean を組み立てる
const fs=require('fs');const [k67b,factsF,outF]=process.argv.slice(2);
const b=fs.readFileSync(k67b,'utf8'); const facts=JSON.parse(fs.readFileSync(factsF,'utf8'));
const blk0=b.slice(b.indexOf("/-- a' = c + (m+1)（行 c で Blk m 1）"), b.indexOf('theorem k67b_step'));
const h4u=b.slice(b.indexOf('  -- O 型の行 b = p + (m+2) で (b + 4u) が P ⇔ (p + X₁) が N'), b.indexOf('  -- O 型の行 b = p + (m+2) で (b + X₁) が P'));
const tail=b.slice(b.indexOf('  -- 行 c = b₃ + (m+1)'), b.indexOf('theorem k67b_rows'));
const rowsT=b.slice(b.indexOf('theorem k67b_rows'), b.indexOf('end K67b'));
const finT=b.slice(b.indexOf('/-- 予想 K67 の u ≡ 19'), b.lastIndexOf('end Rubidium'));
const head0=b.slice(b.indexOf('theorem k67b_step'), b.indexOf('  have hoddA'));
let src=`/-
  Rubidium.K68c — 予想 K68 の 11100 型の類 u ≡ ${Object.keys(facts).join(', ')} (mod 256) の証明

  定理：m + 1 = 8u、u がこれらの類なら、(n, 0) が P ⇔ n mod (5m+8) ∈ {0, m+2, 2m+4, 3m+6, 4m+7}（11100 型）。
  K67b（u ≡ 19 (mod 64)）と同じ形：始まりの行の不変量は Blk m 3。O 型の行 b₁、b₂、b₃ で (b + 4u) が P、P、N であることと、
  (b₃ + 6u) が P であることを、O 型の行の 2 つの規則（偶数 x は (b + x/2) へ、奇数 x は前の行の (m+2+x)/2 へ）を
  繰り返して始まりの行 a の距離に落とし、Blk m 3 で決める。鎖の形は類ごとに違う（code/k68_gen11100.js で生成）。
-/
import Rubidium.K67b

namespace Rubidium

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
`;
for(const r of Object.keys(facts)){
  const F=facts[r].split(/(?=  have F\d)/); const n='k68c'+r;
  const step=head0.replace('k67b_step',n+'_step')+`  have hah : IsP m (a + 4 * u) (4 * u) := (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have hb1 := row_long m a hmo (by omega) hrow (by rw [hh]; exact hah)
${h4u}${F[0]}  have hb1h : IsP m (a + (m + 2) + 4 * u) (4 * u) := (h4u a hrow hb1 hah).mpr F0
  have hb2 := row_long m (a + (m + 2)) hmo (by omega) hb1 (by rw [hh]; exact hb1h)
${F[1]}  have hb2h : IsP m (a + (m + 2) + (m + 2) + 4 * u) (4 * u) := (h4u _ hb1 hb2 hb1h).mpr F1
  have hb3 := row_long m (a + (m + 2) + (m + 2)) hmo (by omega) hb2 (by rw [hh]; exact hb2h)
${F[2]}  have hb3h : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := fun h => ((h4u _ hb2 hb3 hb2h).mp h) F2
`;
  let t=tail.replace(/  -- \(b₃ \+ 6u\) は P：[\s\S]*?  have hc4/, F[3].replace('have F3','have hb36')+'  have hc4').replace('k67b_blk m u hmu hu',n+'_blk m u hmu hu');
  src+=`
section K68c${r}

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 256 = ${r})
include hmu hu

${blk0.replace(/k67b_blk/g,n+'_blk')}${step}${t}${rowsT.replace(/k67b_/g,n+'_')}end K68c${r}

${finT.replace('予想 K67 の u ≡ 19 (mod 64)','予想 K68 の u ≡ '+r+' (mod 256)').replace('theorem K67_19','theorem K68_'+r).replace('(m + 1) % 512 = 152','(m + 1) % 2048 = '+(8*r)).replace(/k67b_/g,n+'_')}`;
}
src+='end Rubidium\n';
fs.writeFileSync(outF,src);
