"""Exact all-Bloch-direction obstruction to whole original3/4 in red core."""
from pathlib import Path
import json
import sympy as s
from exact_fixtures import E,I16,WORDS,local,X,Y,Z
ROOT=Path(__file__).parent
# S1 from the independently specified 34 carrier vectors, with qubit2=0.
u=s.Matrix([1,0,1,0]);v=s.Matrix([1,0,0,1]);B=s.Matrix.hstack(u,v)
P34=B*(B.H*B).inv()*B.H
S1=s.kronecker_product(s.eye(2),s.diag(1,0),P34)
assert S1*S1==S1 and S1.H==S1 and S1.trace()==4 and S1*E[0]==E[0]
expected=s.Matrix([[s.Rational(32,9),0,-s.Rational(8,9)],
 [0,s.Rational(16,3),0],[-s.Rational(8,9),0,s.Rational(32,9)]])
rows=[]
for name,Q in [('E1',E[0]),('S1',S1)]:
 for j in (2,3):
  cc=[Q*local(j,h)-local(j,h)*Q for h in (X,Y,Z)]
  G=s.Matrix(3,3,lambda a,b:s.trace(cc[a].H*cc[b]))
  assert G==(4*s.eye(3) if name=='E1' else expected)
  minors=[G[:k,:k].det() for k in (1,2,3)]
  assert all(m>0 for m in minors)
  assert Q*E[j]==s.zeros(16)
  for h in (X,Y,Z):
   p=local(j,h);D=p*(I16-E[j])
   assert Q*D-D*Q==Q*p-p*Q
  rows.append({'support':name,'physical_query':j+1,'Gram':[[str(z) for z in G.row(k)] for k in range(3)],
   'leading_principal_minors':[str(m) for m in minors],'all_rank_one_local_projectors_excluded':True,
   'passive_complement_commutator_equals_full_local_commutator':True})
# Independent entanglement negative controls agree with the commutator proof.
PT34=s.Matrix(4,4,lambda a,b:P34[2*(b//2)+a%2,2*(a//2)+b%2])
assert PT34.extract([1,2],[1,2]).det()==-s.Rational(1,9)
out={'status':'PASS','cases':rows,'S1_rank':4,
 'optional_S1_partial_transpose_negative_principal_minor':'-1/9',
 'scope':'Exact continuous local-projector commutator exclusion. The graph conclusion uses the whole-red-vertex input-tuple record and the unconditional passive-core bridge.'}
(ROOT/'branch_red_original34_commutator_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
