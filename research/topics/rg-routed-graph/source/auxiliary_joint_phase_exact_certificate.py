"""Lift the discovered affine inconsistency to an exact short rational dual witness."""
import itertools,json,math
from fractions import Fraction as Q
import numpy as np,sympy as s
from exact_fixtures import I16,E,local,Z,WORDS
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16));T=[]
for o in WORDS:
 V=I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16));T.append(np.array(4*V*D0,dtype=np.int64))
T=np.array(T);C=np.zeros_like(T);D=np.zeros_like(T)
for r,ow in enumerate(WORDS):
 for a,aw in enumerate(WORDS):
  if ow[1]==0 and ((aw[0]==0 and aw[3]==0) or(aw[0]==1 and aw[2]==0)):C[r,a]=T[r,a]
  if ow[3]==0 and (aw[2]==0 or(aw[0]==0 and aw[1]==1 and aw[2]==1)):D[r,a]=T[r,a]
opts=[[(1,a,1,a,1) for a in range(2)]]+[[(0,a,0,b,1),(1,a,1,b,-1)] for a,b in itertools.product(range(2),repeat=2)]
source=json.load(open('auxiliary_joint_phase_affine_obstruction_checks.json'));records=source['rank_rows'];pivots={};actual=[];witness=None
for rid,rec in enumerate(records):
 pp=rec['row'];qq=rec['column'];row={};rhs=0
 for term in itertools.product(*[opts[rec['word_key'][k]] for k in range(4)]):
  r=sum(term[k][0]<<(3-k) for k in range(4));a=sum(term[k][1]<<(3-k) for k in range(4));b=sum(term[k][3]<<(3-k) for k in range(4));sg=math.prod(t[4] for t in term)
  rhs+=sg*(int(C[r,a,pp])*int(D[r,b,qq])+int(D[r,a,pp])*int(C[r,b,qq]))
  x=int(T[r,a,pp])*sg;y=int(T[r,b,qq])*sg
  if x:
   col=(r*16+b)*16+qq;row[col]=row.get(col,0)+x
  if y:
   col=(r*16+a)*16+pp;row[col]=row.get(col,0)+y
 row={j:Q(x) for j,x in row.items() if x};actual.append((row.copy(),rhs));val=Q(rhs);comb={rid:Q(1)}
 while row:
  col=min(row);z=row[col]
  if col not in pivots:
   pivots[col]=({j:x/z for j,x in row.items()},val/z,{j:x/z for j,x in comb.items()});break
  old,vv,oldcomb=pivots[col];val-=z*vv
  for j,x in old.items():
   zz=row.get(j,0)-z*x
   if zz:row[j]=zz
   elif j in row:del row[j]
  for j,x in oldcomb.items():
   zz=comb.get(j,0)-z*x
   if zz:comb[j]=zz
   elif j in comb:del comb[j]
 else:
  if val:
   witness=(comb,val);print('exact inconsistency',val,'dual support',len(comb),flush=True);break
assert witness is not None
comb,val=witness;den=math.lcm(*[x.denominator for x in comb.values()]);weights={i:int(x*den) for i,x in comb.items()};g=math.gcd(*weights.values());weights={i:x//g for i,x in weights.items()}
coeff={};total=0;rows=[]
for i,w in sorted(weights.items()):
 row,rhs=actual[i]
 for j,x in row.items():coeff[j]=coeff.get(j,0)+w*x
 total+=w*rhs
 rows.append({'word_key':records[i]['word_key'],'row':records[i]['row'],'column':records[i]['column'],'weight':w,'exact_rhs':rhs})
assert all(x==0 for x in coeff.values()) and total!=0
out={'status':'EXACT CONTRADICTION','weighted_coefficient_sum':'zero on all4096 real variables','weighted_rhs':int(total),'dual_witness_rows':len(rows),'maximum_absolute_weight':max(map(abs,weights.values())),'rows':rows,'scope':'No multilinear mixed coefficient E solves the necessary complete equation Fdag E+Edag F=C4dag C5+C5dag C4. Therefore no simultaneous independent complete extension of these two fixed phase slots exists.'}
print(json.dumps({k:v for k,v in out.items() if k!='rows'},indent=2));json.dump(out,open('auxiliary_joint_phase_exact_obstruction.json','w'),indent=2)
