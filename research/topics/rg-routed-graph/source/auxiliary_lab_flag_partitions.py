"""Exact phase-sector completeness for own-output/laboratory-input partitions."""
import itertools,json,numpy as np,sympy as s
from exact_fixtures import I16,E,local,Z,WORDS
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16));T=[]
for o in WORDS:
 V=I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16));T.append(np.array(4*V*D0,dtype=np.int64))
T=np.array(T);opts=[[(1,a,1,a,1) for a in range(2)]]+[[(0,a,0,b,1),(1,a,1,b,-1)] for a,b in itertools.product(range(2),repeat=2)]
allterms=[]
for choice in itertools.product(range(5),repeat=4):
 terms=[]
 for term in itertools.product(*[opts[choice[i]] for i in range(4)]):
  r=sum(term[i][0]<<(3-i) for i in range(4));a=sum(term[i][1]<<(3-i) for i in range(4));b=sum(term[i][3]<<(3-i) for i in range(4));sg=int(np.prod([x[4] for x in term]));terms.append((r,a,b,sg))
 allterms.append(terms)
out=[]
for label,party,P in [('P4',1,lambda n:(n[0]==0 and n[3]==0)or(n[0]==1 and n[2]==0)),('P5',3,lambda n:n[2]==0 or(n[0]==0 and n[1]==1 and n[2]==1))]:
 for oo,pp in [(0,0),(0,1),(1,0),(1,1),(None,1)]:
  C=np.zeros_like(T)
  for r,rw in enumerate(WORDS):
   for n,nw in enumerate(WORDS):
    if(oo is None or rw[party]==oo)and int(P(nw))==pp:C[r,n]=T[r,n]
  bad=0
  for terms in allterms:
   M=np.zeros((16,16),dtype=np.int64)
   for r,a,b,sg in terms:M+=sg*(np.outer(C[r,a],C[r,b])-np.outer(T[r,a],C[r,b]))
   if np.any(M):bad+=1
  origin=np.array([C[r,r] for r in range(16)]);res={'input_flag':label,'own_output':oo,'input_flag_value':pp,'origin_rank':int(np.trace(origin))//4,'nonzero_complete_projection_word_keys':bad};print(res,flush=True);out.append(res)
json.dump({'results':out,'scope':'Zero defects prove individual complete projector coefficients; a full four-sector partition is valid only if all its sectors pass.'},open('auxiliary_lab_flag_partitions_checks.json','w'),indent=2)
