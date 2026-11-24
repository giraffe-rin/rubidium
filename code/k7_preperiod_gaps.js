/*
 * k7_preperiod_gaps.js — 前周期のある m（m ≤ 2000 の 10 個）について、開始局面の間隔の列（間隔 − (m+1) を 0/1 で）を直接の DP で作り、
 *                        前周期の間隔と周期の語に分ける（notes/2026-11-25-claude-1-k7-periods-2000.md の表）
 *
 * 何を計算するか: (r, p) が P ⇔ A_r ⊆ {p}（A_r = {k : (r − k, k) が P}）の DP で n ≤ t + 4L まで開始局面を求め、間隔の列の
 *   最小の j0（j0 番目以降が周期 p 個の間隔で繰り返す）を探す。(m, t, L) は data/k7_periods_*.txt の値。
 * 実行方法（リポジトリのルートで）: node code/k7_preperiod_gaps.js
 */
'use strict';
const ms=[[55,58,169],[95,194,290],[481,1932,1448],[801,2409,4014],[929,2793,5585],[991,994,3969],[1185,2374,5934],[1463,1466,8788],[1503,7524,4514],[1953,3910,9774]];
for (const [m,t,L] of ms){ const N=t+4*L; const typ=new Int32Array(N+1); typ[0]=-1; const isP=(r,p)=>typ[r]===-1||typ[r]===p;
 for(let r=1;r<=N;r++){let c=0,kk=0;for(let k=1;k<=Math.min(m,r)&&c<2;k++)if(isP(r-k,k)){c++;kk=k;} typ[r]=c===0?-1:c===1?kk:-2;}
 const st=[0];for(let n=1;n<=N;n++)if(typ[n]===-1)st.push(n);
 const g=[];for(let i=1;i<st.length;i++)g.push(st[i]-st[i-1]-(m+1));
 const w=g.join(''); const p=st.filter(x=>x>t&&x<=t+L).length;
 let j0=0; while(j0<w.length-2*p && w.slice(j0,j0+p)!==w.slice(j0+p,j0+2*p) || [...Array(Math.max(0,w.length-j0-p))].some((_,i)=>w[j0+i]!==w[j0+i+p])) j0++;
 console.log(m, 'v2='+Math.log2((m+1)&-(m+1)), '前周期の間隔:', w.slice(0,j0)||'-', ' 周期の語:', w.slice(j0,j0+p), ' (m+1) mod 2^6 =', (m+1)%64, ' m mod 12 =', m%12);
}
