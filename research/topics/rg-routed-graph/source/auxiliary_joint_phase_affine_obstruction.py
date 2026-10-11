"""All-joint-extension necessary mixed second-derivative equation.
Solve F*E+E*F=C4*C5+C5*C4 for a multilinear E in the complete word quotient.
The homogeneous real-PLUS operator has independently proved exact rank3967.
"""
import itertools,json,time,numpy as np,sympy as s
from exact_fixtures import I16,E,local,Z,WORDS
p=1000003;D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16));T=[]
for o in WORDS:
 V=I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16));T.append(np.array(4*V*D0,dtype=np.int64))
T=np.array(T);C=np.zeros_like(T);D=np.zeros_like(T)
for r,ow in enumerate(WORDS):
 for a,aw in enumerate(WORDS):
  P4=(aw[0]==0 and aw[3]==0) or(aw[0]==1 and aw[2]==0)
  P5=(aw[2]==0) or(aw[0]==0 and aw[1]==1 and aw[2]==1)
  if ow[1]==0 and P4:C[r,a]=T[r,a]
  if ow[3]==0 and P5:D[r,a]=T[r,a]
opts=[[(1,a,1,a,1) for a in range(2)]]+[[(0,a,0,b,1),(1,a,1,b,-1)] for a,b in itertools.product(range(2),repeat=2)]
pivots={};records=[];keys=0;start=time.time();witness=None
for choice in itertools.product(range(5),repeat=4):
 raw=[];rhs=np.zeros((16,16),dtype=np.int64)
 for term in itertools.product(*[opts[choice[k]] for k in range(4)]):
  r=sum(term[k][0]<<(3-k) for k in range(4));a=sum(term[k][1]<<(3-k) for k in range(4));b=sum(term[k][3]<<(3-k) for k in range(4));sg=int(np.prod([t[4] for t in term]));raw.append((r,a,b,sg))
  rhs+=sg*(np.outer(C[r,a],D[r,b])+np.outer(D[r,a],C[r,b]))
 for pp,qq in itertools.product(range(16),repeat=2):
  row={};val=int(rhs[pp,qq])%p
  for r,a,b,sg in raw:
   x=int(T[r,a,pp])*sg;y=int(T[r,b,qq])*sg
   if x:
    col=(r*16+b)*16+qq;row[col]=(row.get(col,0)+x)%p
   if y:
    col=(r*16+a)*16+pp;row[col]=(row.get(col,0)+y)%p
  row={j:x for j,x in row.items() if x}
  original_rhs=val
  while row:
   col=min(row);z=row[col]
   if col not in pivots:
    inv=pow(z,-1,p);pivots[col]=({j:x*inv%p for j,x in row.items()},val*inv%p);records.append({'word_key':list(choice),'row':pp,'column':qq,'rhs':original_rhs});break
   old,vv=pivots[col];val=(val-z*vv)%p
   for j,x in old.items():
    z2=(row.get(j,0)-z*x)%p
    if z2:row[j]=z2
    elif j in row:del row[j]
  else:
   if val:
    witness={'word_key':list(choice),'row':pp,'column':qq,'rhs':original_rhs,'reduced_rhs':val,'coefficient_rank_so_far':len(pivots),'augmented_rank_lower_bound':len(pivots)+1};records.append(witness);break
 if witness:break
 keys+=1
 if keys%20==0:print(keys,len(pivots),time.time()-start,flush=True)
out={'status':'INCONSISTENT' if witness else 'NO_OBSTRUCTION_FOUND','prime':p,'known_exact_total_coefficient_rank':3967,'coefficient_rank_found':len(pivots),'word_keys_scanned':keys,'witness':witness,'rank_rows':records,'seconds':time.time()-start}
# A first early inconsistency certifies augmented rank only len(pivots)+1; to
# exceed the full exact base rank, append all previously certified base rows
# with their recomputed rhs during independent validation if necessary.
print('RESULT',json.dumps({k:v for k,v in out.items() if k!='rank_rows'}),flush=True);json.dump(out,open('auxiliary_joint_phase_affine_obstruction_checks.json','w'),indent=2)
