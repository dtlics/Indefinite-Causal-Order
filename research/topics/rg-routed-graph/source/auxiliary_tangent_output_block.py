"""Exact modular rank scout for a fixed future/query-output XOR tangent block.
A rank is a rigorous lower bound; completeness requires an explicit matching kernel.
"""
import itertools,json,sys,time
import numpy as np
from exact_fixtures import I16,E,local,Z,WORDS
import sympy as s
mask=int(sys.argv[1]) if len(sys.argv)>1 else 7
mode=sys.argv[2] if len(sys.argv)>2 else 'real'; parity=-1 if mode=='real' else 1
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16));T=[]
for o in WORDS:
 v=I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16));A=4*v*D0;assert all(x.q==1 for x in A);T.append(np.array(A,dtype=np.int64))
T=np.array(T);prime=1000003
opts=[]
for bit in [8,4,2,1]:
 if mask&bit:
  opts.append([[(r,a,1-r,b,1)] for r,a,b in itertools.product(range(2),repeat=3)])
 else:
  opts.append([[(1,a,1,a,1) for a in range(2)]]+[[(0,a,0,b,1),(1,a,1,b,-1)] for a,b in itertools.product(range(2),repeat=2)])
pivots={};records=[];keys=0;scanned=0;start=time.time()
for choice in itertools.product(*(range(len(x)) for x in opts)):
 raw=[]
 for term in itertools.product(*[opts[k][choice[k]] for k in range(4)]):
  r=sum(term[k][0]<<(3-k) for k in range(4));a=sum(term[k][1]<<(3-k) for k in range(4));rr=sum(term[k][2]<<(3-k) for k in range(4));b=sum(term[k][3]<<(3-k) for k in range(4));sg=int(np.prod([t[4] for t in term]));raw.append((r,a,rr,b,sg))
 for p,q in itertools.product(range(16),repeat=2):
  row={}
  for r,a,rr,b,sg in raw:
   x=int(T[r,a,p])*sg;y=int(T[rr,b,q])*sg*parity
   if x:
    col=(r*16+b)*16+q;row[col]=(row.get(col,0)+x)%prime
   if y:
    col=(rr*16+a)*16+p;row[col]=(row.get(col,0)+y)%prime
  row={j:x for j,x in row.items() if x}
  if not row:continue
  scanned+=1
  while row:
   col=min(row);z=row[col]
   if col not in pivots:
    inv=pow(z,-1,prime);pivots[col]={j:v*inv%prime for j,v in row.items()};records.append((list(choice),p,q));break
   for j,v in pivots[col].items():
    x=(row.get(j,0)-z*v)%prime
    if x:row[j]=x
    elif j in row:del row[j]
  if len(pivots)>=4088:break
 keys+=1
 if keys%10==0:print('keys',keys,'rank',len(pivots),'seconds',time.time()-start,flush=True)
 if len(pivots)>=4088:break
if mask in [0,1,2,4]:json.dump({str(k):{str(j):v for j,v in row.items()} for k,row in pivots.items()},open(f'auxiliary_tangent_echelon_{mask}_{mode}.json','w'))
out={'xor_mask':mask,'mode':mode,'prime':prime,'variables':4096,'rank_lower_bound':len(pivots),'normal_keys_scanned':keys,'nonzero_rows_scanned':scanned,'rows':records,'seconds':time.time()-start}
print('FINAL',json.dumps({k:v for k,v in out.items() if k!='rows'}),flush=True);json.dump(out,open(f'auxiliary_tangent_output_block_{mask}_{mode}.json','w'),indent=2)
