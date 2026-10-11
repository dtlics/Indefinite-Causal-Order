"""Exact coefficient geometry for saturated common-passive-core rigidity."""
from pathlib import Path
from itertools import product,combinations
import json
import sympy as s
from exact_fixtures import E,R,I16,I2,X,Y,Z,WORDS,local,tensor
ROOT=Path(__file__).parent
zero=s.zeros(16)
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),zero)
Vo=[I16-2*sum((E[i] for i in range(4) if o[i]),zero) for o in WORDS]
RE=I16-sum(E,zero)
assert D0==D0.H and D0*D0==I16 and D0*RE==RE
assert all(D0*E[i]==local(i,Z)*E[i] for i in range(4))
assert all(v==v.H and v*v==I16 for v in Vo)
# Independently recover every matrix-unit row from the orthogonal-cylinder
# normalized expression W + sum_i (Z_i U_i Z_i-U_i) U_bar_i E_i.
for o,v in zip(WORDS,Vo):
 for a,aw in enumerate(WORDS):
  row=s.zeros(1,16);row[a]=1
  direct=row+sum((((-1)**(o[i]+aw[i])-1)*(row*E[i]) for i in range(4)),s.zeros(1,16))
  assert direct==row*v*D0
# Joint sign sectors of the four generating reflections.
generators=[I16-2*e for e in E];sectors=[]
for signs in product((1,-1),repeat=4):
 P=I16
 for v,sgn in zip(generators,signs):P=P*(I16+sgn*v)/2
 rank=int(P.trace());assert P*P==P and P==P.H
 if rank:
  negatives=[i for i,x in enumerate(signs) if x==-1]
  assert (not negatives and P==RE) or(len(negatives)==1 and P==E[negatives[0]])
 sectors.append({'signs':signs,'rank':rank})
assert sorted(row['rank'] for row in sectors if row['rank'])==[2,2,2,2,8]
# Every sufficient coefficient identity, including all physical rows o.
for o,v in zip(WORDS,Vo):
 assert v*D0*RE==RE
 for i,e in enumerate(E):assert v*D0*e==((-1)**o[i])*local(i,Z)*e
# Independent canonical cylinders, avoiding imported generated supports.
def cylinder(i,vecs):
 cols=[];other=[j for j in range(4) if j!=i]
 for bit in (0,1):
  for v in vecs:
   cols.append(s.Matrix([v[sum(w[j]<<(2-k) for k,j in enumerate(other))] if w[i]==bit else 0 for w in WORDS]))
 B=s.Matrix.hstack(*cols);return B*(B.H*B).inv()*B.H
S=[cylinder(0,[[1,0,1,0,0,0,0,0],[1,0,0,1,0,0,0,0]]),
   cylinder(1,[[0,1,0,0,0,0,0,0],[0,0,0,0,1,1,-1,-1]]),E[2],E[3]]
assert [int(q.trace()) for q in S]==[4,4,2,2]
for i in range(4):
 assert S[i]*S[i]==S[i] and S[i]*E[i]==E[i]
 assert S[i]*RE==S[i]-E[i]
 for j in range(4):
  if i!=j:assert S[i]*S[j]==zero
allowed=[]
for big1,big2 in product((False,True),repeat=2):
 Q=[S[0] if big1 else E[0],S[1] if big2 else E[1],E[2],E[3]]
 residual=I16-sum(Q,zero)
 assert residual*residual==residual and RE*residual==residual
 assert all(v*D0*residual==residual for v in Vo)
 allowed.append({'Q1':'S1' if big1 else 'E1','Q2':'S2' if big2 else 'E2',
                 'residual_rank':int(residual.trace()),'Q_total_rank':int(sum(q.trace() for q in Q))})
# Explicit old allowed rank-two tilted reducing supports, now excluded here.
tilts=[]
for i,v in [(0,[1,0,1,0,0,0,0,0]),(1,[0,1,0,0,0,0,0,0])]:
 q=R[i]*cylinder(i,[v])*R[i]
 assert q*q==q and q.H==q and q.trace()==2 and S[i]*q==q
 assert all(q*(R[i]*local(i,h)*R[i])==(R[i]*local(i,h)*R[i])*q for h in (X,Y,Z))
 Q=list(E);Q[i]=q;rr=I16-sum(Q,zero)
 assert rr*rr==rr and rr.trace()==8
 defect=(I16-RE)*rr
 norm=s.trace(defect.H*defect);assert norm>0
 tilts.append({'query':i+1,'total_active_rank':2,'residual_rank':8,
               'squared_HS_outside_RE':str(norm),'parallel_column_impossible':True})
# Pauli words form an exact basis of M16. Commutation with the three physical
# spectator factors leaves precisely the missing physical M2 factor.
paulis=[I2,X,Y,Z];commutants=[]
for i in range(4):
 survivors=[]
 for word in product(range(4),repeat=4):
  A=tensor([paulis[k] for k in word])
  if all(A*local(j,h)==local(j,h)*A for j in range(4) if j!=i for h in (X,Z)):
   survivors.append(word)
 assert len(survivors)==4 and all(all(word[j]==0 for j in range(4) if j!=i) for word in survivors)
 commutants.append(survivors)
for i,j in combinations(range(4),2):assert set(commutants[i])&set(commutants[j])=={(0,0,0,0)}
out={'status':'PASS','joint_reflection_sectors':sectors,
 'all_256_matrix_unit_coefficient_rows_reconstructed':True,
 'all_parallel_column_sector_identities':True,'D0_sector_actions':True,
 'canonical_residual_intersection_ranks':[int((q*RE).trace()) for q in S],
 'allowed_common_passive_support_tuples':allowed,'excluded_tilted_total_support_examples':tilts,
 'three_spectator_commutants_physical_missing_factor':commutants,
 'distinct_assignment_factors_intersect_only_scalars':True,
 'scope':'Exact quartet coefficient and support certificate. The common-core graph conclusion uses the exchange/module proof and same-baseline joint faithfulness in the accompanying audit.'}
(ROOT/'branch_layer_saturated_passive_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
