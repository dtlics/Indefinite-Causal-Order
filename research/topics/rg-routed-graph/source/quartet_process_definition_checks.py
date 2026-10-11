"""Exact target coefficients and projection identities for the uniform proof."""
from pathlib import Path
from itertools import product
import json
import sympy as s
from exact_fixtures import E,R,I16,I2,Z,WORDS,local,tensor
O=s.zeros(16);ROOT=Path(__file__).parent
assert all(p.H==p and p*p==p and p.trace()==2 for p in E)
assert all(E[i]*E[j]==O for i in range(4) for j in range(4) if i!=j)
units=[]
for a,b in product((0,1),repeat=2):
 x=s.zeros(2);x[a,b]=1;units.append(x)
for i in range(4):
 for x in units:assert E[i]*local(i,x)==local(i,x)*E[i]
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),O)
assert D0.H==D0 and D0*D0==I16
Vs=[I16-2*sum((o[i]*E[i] for i in range(4)),O) for o in WORDS]
assert all(v.H==v and v*v==I16 for v in Vs)
# Every complex multilinear basis coefficient, independently as row formula
# and normalized orthogonal-cylinder formula.
for out in WORDS:
 for inp in WORDS:
  xs=[]
  for a,b in zip(out,inp):
   x=s.zeros(2);x[a,b]=1;xs.append(x)
  W=tensor(xs);row=sum((s.diag(*(int(w==o) for w in WORDS))*W*v for o,v in zip(WORDS,Vs)),O)*D0
  direct=W+sum((tensor([I2 if k==i else xs[k] for k in range(4)])*(local(i,Z)*local(i,xs[i])*local(i,Z)-local(i,xs[i]))*E[i] for i in range(4)),O)
  assert row==direct
for i in range(4):
 for x in units:
  xs=[I2]*4;xs[i]=x;W=tensor(xs)
  raw=sum((s.diag(*(int(w==o) for w in WORDS))*W*v for o,v in zip(WORDS,Vs)),O)*D0
  assert raw==R[i]*local(i,x)*R[i]
data={'status':'PASS','projection_ranks':[2]*4,'pairwise_orthogonal':True,
 'own_factor_matrix_unit_commutation_checks':16,'unitary_Vo_checks':16,
 'normalizer_unitary':True,'full_multilinear_coefficients_checked':256,
 'single_representation_matrix_units_checked':16,
 'complete_unitarity_argument':'Uniform all-private-dimension cancellation proof in quartet_routed_obstruction_manuscript.md Section2; no finite-unitary test substitutes for it.'}
(ROOT/'quartet_process_definition_checks.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps(data,indent=2))
