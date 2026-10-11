import json,math
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from coset_kernel import reduce_word

def add(*terms):
 d={}
 for scale,p in terms:
  for w,c in p.items():d[w]=d.get(w,0)+scale*c
 return {w:c for w,c in d.items() if c}
def mul(a,b):
 d={}
 for u,c in a.items():
  for v,e in b.items():
   w=reduce_word(u+v);d[w]=d.get(w,0)+c*e
 return {w:c for w,c in d.items() if c}
def pmul(a,b):
 out=[F(0)]*(len(a)+len(b)-1)
 for i,c in enumerate(a):
  for j,d in enumerate(b):out[i+j]+=c*d
 return out
def polys(s,N):
 out=[[F(1)],[F(-s),F(1)]]
 for n in range(1,N):
  p=[F(0)]+out[-1];prev=out[-2]
  for j,c in enumerate(prev):p[j]-=c
  out.append(p)
 return out[:N+1]
I={():1};T={(0,):1,(1,):1};D={(0,):1,(1,):-1};cases=0;overlap=0;orth=0
for s in [-1,1]:
 pg=[I,add((1,T),(-s,I))]
 for n in range(1,10):pg.append(add((1,mul(pg[-1],T)),(-1,pg[-2])))
 pp=polys(s,10)
 for m in range(11):
  for n in range(11):
   coeff=pmul(pp[m],pp[n]);val=sum(c*(math.comb(k,k//2) if k%2==0 else s*math.comb(k+1,(k+1)//2)//2) for k,c in enumerate(coeff));assert val==int(m==n);orth+=1
 for x in [0,1]:
  P={():1,(x,):s};ws=[tuple((1-x+j)%2 for j in range(n)) for n in range(11)]
  for n,u in enumerate(ws):assert mul(P,{u:1})==mul(P,pg[n]);cases+=1
  for m in range(6):
   for n in range(6):
    lhs=add((2,mul(mul({tuple(reversed(ws[m])):1},P),{ws[n]:1})))
    pminus={w:(-1)**len(w)*c for w,c in pg[n].items()}
    rhs=add((1,mul(mul(add((2,I),(s,T)),pg[m]),pg[n])),(((-1)**x)*s,mul(mul(pg[m],pminus),D)))
    assert lhs==rhs,(s,x,m,n);overlap+=1
# Exact degree9 annihilators for the new rational certified angle support.
cl=json.load(open(Path(__file__).with_name('Radau1_lower160.json')));pairs=cl['rational_tangent_pairs'];assert pairs[-1]==[0,1];records=[];ann=0
for s in [-1,1]:
 qpoly=[F(-2*s),F(1)]
 for p,q in pairs[:-1]:qpoly=pmul(qpoly,[F(-4*q*q,p*p+q*q),0,1])
 basis=polys(s,9);rem=qpoly.copy();coeff=[F(0)]*10
 for n in reversed(range(10)):
  coeff[n]=rem[n]
  for k,c in enumerate(basis[n]):rem[k]-=coeff[n]*c
 assert all(v==0 for v in rem)
 for p,q in pairs:
  den=p*p+q*q;R0=np.array([[F(1),0],[0,F(-1)]],dtype=object);R1=np.array([[F(q*q-p*p,den),F(2*p*q,den)],[F(2*p*q,den),F(p*p-q*q,den)]],dtype=object);tt=R0+R1;value=np.zeros((2,2),dtype=object);power=np.eye(2,dtype=object)
  for c in qpoly:value+=c*power;power=power@tt
  for R in [R0,R1]:assert all(v==0 for v in ((np.eye(2,dtype=object)+s*R)@value).ravel());ann+=1
 records.append({'sign':s,'monomial_coefficients':[str(v) for v in qpoly],'coset_coefficients':[str(v) for v in coeff]})
out={'status':'PASSED_EXACT','word_Jacobi_identities':cases,'word_overlap_normal_form_identities':overlap,'spectral_measure_orthogonality_checks':orth,'candidate_annihilator_checks':ann,'candidate_annihilators':records,'floating_arithmetic':False,'scope':'Exact structural identities and support annihilators. No positive universal extension or optimality certificate.'};Path(__file__).with_name('jacobi_coset_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='candidate_annihilators'},indent=2))
