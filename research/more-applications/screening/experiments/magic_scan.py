from core import *
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
st={'+Z':np.array([1,0],complex),'-Z':np.array([0,1],complex),'+X':np.array([1,1],complex)/np.sqrt(2),'-X':np.array([1,-1],complex)/np.sqrt(2),'+Y':np.array([1,1j],complex)/np.sqrt(2),'-Y':np.array([1,-1j],complex)/np.sqrt(2)}
S=np.diag([1,1j]);H=(X+Z)/np.sqrt(2)
channels={}
for n,s in st.items(): channels['reset'+n]=reset(np.outer(s,s.conj()))
for ax,P in zip('XYZ',[X,Y,Z]):
    channels['measure'+ax]=[ (I2+P)/2,(I2-P)/2]
    for name,U in [('H',H),('S',S)]: channels['measure'+ax+'_then_'+name]=[U@(I2+P)/2,U@(I2-P)/2]
for name,U in [('H',H),('S',S),('X',X),('Z',Z)]: channels['gate'+name]=[U]
rows=[]
for an,A in channels.items():
 for bn,B in channels.items():
  for sn,s in st.items():
   rho=np.outer(s,s.conj())
   for sign,ks in zip(['+','-'],switch_branches(A,B)):
    R=apply(ks,rho);p=np.trace(R).real
    if p<1e-10:continue
    R/=p
    b=np.array([np.trace(R@P).real for P in [X,Y,Z]])
    norm=np.sum(np.abs(b))
    if norm>1+1e-10: rows.append(dict(A=an,B=bn,input=sn,flag=sign,p=p,bloch=b.tolist(),l1=norm,weighted_excess=p*(norm-1)))
rows.sort(key=lambda r:r['weighted_excess'],reverse=True)
ROOT.joinpath('magic_scan.json').write_text(json.dumps({'tested':len(channels)**2*len(st)*2,'positive_cases':len(rows),'top':rows[:100],'reset_only':[r for r in rows if r['A'].startswith('reset') and r['B'].startswith('reset')][:30]},indent=2))
print('tested',len(channels)**2*len(st)*2,'positive',len(rows))
print(json.dumps(rows[:5],indent=2))
print('reset only: ',json.dumps([r for r in rows if r['A'].startswith('reset') and r['B'].startswith('reset')][:5],indent=2))
