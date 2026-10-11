"""Complete linear obstruction to a qubit lift of the rank8 input flag P4.
A represented Pauli X must be a complete tangent insertion anticommuting with
J_Z=Fdag(2 C_P4-F). This is necessary, not sufficient for a qubit extension.
"""
import itertools,json,numpy as np,sympy as s,time
from exact_fixtures import I16,E,local,Z,WORDS
p=1000003;D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16));F=[]
for o in WORDS:
 V=I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16));F.append(np.array(4*V*D0,dtype=np.int64))
F=np.array(F);T=F.copy()
for r in range(16):
 for n,nw in enumerate(WORDS):
  flag=(nw[0]==0 and nw[3]==0)or(nw[0]==1 and nw[2]==0)
  T[r,n]*=(1 if flag else -1)
def raw_terms(mask,key):
 opts=[]
 for bit in [8,4,2,1]:
  if mask&bit:opts.append([[(r,a,1-r,b,1)] for r,a,b in itertools.product(range(2),repeat=3)])
  else:opts.append([[(1,a,1,a,1) for a in range(2)]]+[[(0,a,0,b,1),(1,a,1,b,-1)] for a,b in itertools.product(range(2),repeat=2)])
 out=[]
 for term in itertools.product(*[opts[i][key[i]] for i in range(4)]):
  r=sum(term[i][0]<<(3-i) for i in range(4));a=sum(term[i][1]<<(3-i) for i in range(4));rr=sum(term[i][2]<<(3-i) for i in range(4));b=sum(term[i][3]<<(3-i) for i in range(4));sg=int(np.prod([x[4] for x in term]));out.append((r,a,rr,b,sg))
 return out
def make(A,raw,pp,qq,parity):
 row={}
 for r,a,rr,b,sg in raw:
  x=int(A[r,a,pp])*sg;y=int(A[rr,b,qq])*sg*parity
  if x:col=(r*16+b)*16+qq;row[col]=(row.get(col,0)+x)%p
  if y:col=(rr*16+a)*16+pp;row[col]=(row.get(col,0)+y)%p
 return {j:x for j,x in row.items() if x}
def insert(row,pivots):
 while row:
  col=min(row);z=row[col]
  if col not in pivots:
   inv=pow(z,-1,p);pivots[col]={j:x*inv%p for j,x in row.items()};return True
  for j,x in pivots[col].items():
   y=(row.get(j,0)-z*x)%p
   if y:row[j]=y
   elif j in row:del row[j]
 return False
out=[]
for mask in [0,4]:
 for kind in ['real','imag']:
  piv={};parity=-1 if kind=='real' else 1;old=json.load(open(f'auxiliary_tangent_output_block_{mask}_{kind}.json'));cache={}
  for key,pp,qq in old['rows']:
   key=tuple(key)
   if key not in cache:cache[key]=raw_terms(mask,key)
   insert(make(F,cache[key],pp,qq,parity),piv)
  initial=len(piv);records=[]
  for key in itertools.product(*[range(8 if mask&bit else 5) for bit in [8,4,2,1]]):
   raw=raw_terms(mask,key)
   for pp,qq in itertools.product(range(16),repeat=2):
    if insert(make(T,raw,pp,qq,-parity),piv):records.append((list(key),pp,qq))
    if len(piv)==4096:break
   if len(piv)==4096:break
  json.dump({str(k):{str(j):v for j,v in row.items()} for k,row in piv.items()},open(f'auxiliary_input_flag_anticommutant_echelon_{mask}_{kind}.json','w'))
  rec={'mask':mask,'kind':kind,'initial_tangent_rank':initial,'joint_rank_lower_bound':len(piv),'anticommuting_tangent_dimension_upper_bound':4096-len(piv),'added_rows':records};out.append(rec);print({k:v for k,v in rec.items() if k!='added_rows'},flush=True)
json.dump({'prime':p,'blocks':out,'scope':'Necessary complete linear Hermiticity and anticommutation only; positive survivors are not quantum lifts.'},open('auxiliary_input_flag_anticommutant_echelon_checks.json','w'),indent=2)
