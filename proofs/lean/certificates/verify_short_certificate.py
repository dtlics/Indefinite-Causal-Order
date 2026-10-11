"""Exact replay of the switch separation certificate, standard library only.
Verifies the sparse causal and CPTP-gauge dual identities directly from tensors.
Run certify_switch_support.py separately for the finite-unitary rank bound.
"""
from fractions import Fraction as F
from itertools import product,combinations_with_replacement
from pathlib import Path
import json,time
st=time.time();p=Path(__file__).parent;data=json.loads((p/'short_dual_relations.json').read_text())
ids=list(product(range(2),repeat=7));index={x:i for i,x in enumerate(ids)};pairs=list(combinations_with_replacement(range(25),2));pi={x:i for i,x in enumerate(pairs)}
E=[]
for p0,ai,ao,bi,bo,c,t in ids:
 row=[0]*25;row[ai*8+ao*4+bi*2+bo]=int(p0==t);row[16+bi*2+bo]=int(p0==ai and ao==t);row[20+ai*2+ao]=int(p0==bi and bo==t);row[24]=int((c==0 and p0==ai and ao==bi and bo==t)or(c==1 and p0==bi and bo==ai and ao==t));E.append(row)
Es=[[(j,v) for j,v in enumerate(row) if v] for row in E]
def add_entry(out,i,j,scale):
 for a,x in Es[i]:
  for b,y in Es[j]:out[pi[min(a,b),max(a,b)]]+=scale*x*y
small5=list(product(range(2),repeat=5));small3=list(product(range(2),repeat=3))
def mrow(k):
 out=[0]*325
 if k<1024:
  a=small5[k//32];b=small5[k%32]
  for f in product(range(2),repeat=2):add_entry(out,index[a+f],index[b+f],2)
  if a[4]==b[4]:
   for z,c,t in product(range(2),repeat=3):add_entry(out,index[a[:4]+(z,c,t)],index[b[:4]+(z,c,t)],-1)
 else:
  k-=1024;a=small3[k//8];b=small3[k%8]
  for tail in product(range(2),repeat=4):add_entry(out,index[a+tail],index[b+tail],2)
  if a[2]==b[2]:
   for tail in product(range(2),repeat=5):add_entry(out,index[a[:2]+tail],index[b[:2]+tail],-1)
 return out

def grow(k):
 # Vectorization is column-major: entry(i,j) has index i+128*j.
 a=ids[k%128];b=ids[k//128];out=[0]*325
 for A,sa in [((),1),((2,),-1),((1,2),1)]:
  for B,sb in [((),1),((4,),-1),((3,4),1)]:
   factors=A+B
   if any(a[f]!=b[f] for f in factors):continue
   for vals in product(range(2),repeat=len(factors)):
    aa=list(a);bb=list(b)
    for f,v in zip(factors,vals):aa[f]=bb[f]=v
    add_entry(out,index[tuple(aa)],index[tuple(bb)],sa*sb*(16//(2**len(factors))))
 return out

def combination(rows,generator):
 out=[F(0)]*325
 for k,c in rows:
  c=F(c)
  for j,v in enumerate(generator(k)):
   if v:out[j]+=c*v
 return out
w=[F(x) for x in data['witness']];assert combination(data['AB_rows'],mrow)==w
assert combination(data['G16_rows'],grow)==w
R=data['swap_matrix']
# Verify exact physical A/B slot permutation representation.
for i,(p0,ai,ao,bi,bo,c,t) in enumerate(ids):
 assert [sum(E[i][k]*R[k][j] for k in range(25)) for j in range(25)]==E[index[p0,bi,bo,ai,ao,c,t]]
# Pull back f under X -> R X R^T, in upper-triangle coordinate convention.
wb=[]
for a,b in pairs:
 value=F(0)
 for k,v in enumerate(w):
  if not v:continue
  i,j=pairs[k];entry=R[i][a]*R[j][b]
  if a!=b:entry+=R[i][b]*R[j][a]
  value+=v*entry
 wb.append(value)
assert combination(data['BA_rows'],mrow)==wb
assert w[pi[24,24]]==1
for lo,hi in [(0,16),(16,20),(20,24)]:assert sum(w[pi[j,j]] for j in range(lo,hi))==0
out={'result':'PASS','arithmetic':'exact Python integers and rational fractions','basis_rows':128,'basis_columns':25,'symmetric_coordinates':325,'AB_dual_terms':len(data['AB_rows']),'BA_dual_terms':len(data['BA_rows']),'gauge_dual_terms':len(data['G16_rows']),'identities_verified':3,'switch_coefficient':1,'noise_coefficients':[0,0,0],'seconds':time.time()-st}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
