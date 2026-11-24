/*
 * k63_explain.js — 予想 K63 の (2) の対象の m で、交互が崩れる局面 (4m+6+h, h)（N）がなぜ N かを、局面の手で説明する木を出す
 *
 * 何を計算するか: 直接の DP（(r, p) が P ⇔ A_r ⊆ {p}）で表を作り、N の局面には P に移る手を 1 つ、P の局面には「行き先が P になりうる手」
 *   （行き先がブロックの始まりから k の位置、または行の終わり m+1 の位置）を並べて、再帰的に木を出す。位置は「B<ブロック番号>+<距離>」と書く。
 * 実行方法（リポジトリのルートで）: node code/k63_explain.js 157
 */
'use strict';
const v2=x=>{let c=0;while(x%2===0){x/=2;c++}return c};
const u=+process.argv[2]; const m=8*u-1,h=4*u,L=2*m+3,N=L*3; const typ=new Int32Array(N+1); typ[0]=-1; const isP=(r,p)=>typ[r]===-1||typ[r]===p;
for(let r=1;r<=N;r++){let c=0,kk=0;for(let k=1;k<=Math.min(m,r)&&c<2;k++)if(isP(r-k,k)){c++;kk=k;} typ[r]=c===0?-1:c===1?kk:-2;}
const e11=v2(11*u+1),Y=(11*u+1)/2**e11;
// row starts: 0, m+2, 2m+3, 3m+5, 4m+6
const rows=[0,m+2,2*m+3,3*m+5,4*m+6];
const name=r=>{let i=rows.length-1;while(rows[i]>r)i--;return "B"+i+"+"+(r-rows[i]);};
const seen=new Set(); const out=[];
function ex(r,p,depth){ const key=r+","+p; if(seen.has(key)||depth>12) return; seen.add(key);
  const P=isP(r,p);
  if(!P){ // find a move to P (prefer within same block or K3 range)
    for(let k=1;k<=Math.min(m,r);k++) if(k!==p&&isP(r-k,k)){ out.push(`${"  ".repeat(depth)}N ${name(r)} p=${p}  手 ${k} → ${name(r-k)} p=${k}`); ex(r-k,k,depth+1); return; } }
  else { const nontriv=[]; for(let k=1;k<=Math.min(m,r);k++){ if(k===p) continue; const t=r-k; if(typ[t]===-2) continue; if(typ[t]===-1){continue;} if(typ[t]!==k) continue; }
    // list moves whose target is a "single p = k" row equal (r-k, k) — but those are P? they are N necessarily since P
    for(let k=1;k<=Math.min(m,r);k++){ if(k===p) continue; const t=r-k; if(typ[t]===k) {} }
    // interesting targets: t whose row type is single-p and that p equals k would be P (contradiction), so look at targets with typ[t] === -2 ? no.
    // Instead: targets (t,k) where t is in a block at distance d=k from the block start (candidate P), i.e. t - rowstart(t) === k
    const cand=[]; for(let k=1;k<=Math.min(m,r);k++){ if(k===p) continue; const t=r-k; let i=rows.length-1;while(rows[i]>t)i--; const d=t-rows[i]; if(d===k || (t===rows[i]+m+1)) cand.push(k);} 
    out.push(`${"  ".repeat(depth)}P ${name(r)} p=${p}  （気になる手 ${cand.join(",")}）`); for(const k of cand) ex(r-k,k,depth+1); }
}
ex(4*m+6+h,h,0);
console.log("u="+u,"m="+m,"h="+h,"e11="+e11,"Y="+Y); console.log(out.join("\n"));
