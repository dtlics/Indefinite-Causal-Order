"""Exact complete joint phase sectors for the two new lab input/output flags."""
import itertools,json,numpy as np,sympy as s
from exact_fixtures import I16,E,local,Z,WORDS
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16));T=[]
for o in WORDS:
 v=I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16));T.append(np.array(4*v*D0,dtype=np.int64))
T=np.array(T);opts=[[(1,a,1,a,1) for a in range(2)]]+[[(0,a,0,b,1),(1,a,1,b,-1)] for a,b in itertools.product(range(2),repeat=2)]
out=[]
for aa,bb in itertools.product(range(2),repeat=2):
 C=np.zeros_like(T)
 for o,ob in enumerate(WORDS):
  for n,nb in enumerate(WORDS):
   a=(ob[1]==0 and ((nb[0]==0 and nb[3]==0) or (nb[0]==1 and nb[2]==0)))
   b=(ob[3]==0 and (nb[2]==0 or (nb[0]==0 and nb[1]==1 and nb[2]==1)))
   if a==bool(aa) and b==bool(bb):C[o,n,:]=T[o,n,:]
 bad=0
 for choice in itertools.product(range(5),repeat=4):
  M=np.zeros((16,16),dtype=np.int64)
  for term in itertools.product(*[opts[choice[i]] for i in range(4)]):
   r=sum(term[i][0]<<(3-i) for i in range(4));a=sum(term[i][1]<<(3-i) for i in range(4));b=sum(term[i][3]<<(3-i) for i in range(4));sg=int(np.prod([x[4] for x in term]))
   M+=sg*(np.outer(C[r,a,:],C[r,b,:])-np.outer(T[r,a,:],C[r,b,:]))
  if np.any(M):bad+=1
 origin=np.array([C[o,o,:] for o in range(16)])
 rec={'flags':[aa,bb],'origin_trace':int(np.trace(origin))//4,'nonzero_complete_projection_defect_keys':bad};print(rec,flush=True);out.append(rec)
json.dump({'sectors':out,'meaning':'All four zero defects would prove a simultaneous complete four-sector phase extension; any nonzero defect rejects this direct joint mask construction.'},open('auxiliary_joint_phase_test_checks.json','w'),indent=2)
