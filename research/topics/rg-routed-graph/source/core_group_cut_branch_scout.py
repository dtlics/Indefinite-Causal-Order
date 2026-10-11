"""Exact linear necessary test for a native {1,2}-cut phase branch outside forced red core."""
import sympy as s,json
from itertools import product
from pathlib import Path
from exact_fixtures import *
# Orthogonal isometric embedding of Q12; omit common sqrt2 using an
# unnormalised frame, which does not change the unknown matrix span.
v=s.Matrix([1,-1]);q34=s.kronecker_product(v,s.Matrix([0,1]));B=s.kronecker_product(s.eye(4),q34)
K0=s.Matrix.hstack(s.Matrix([1,0,1,0]),s.Matrix([1,0,0,1]));K=K0*(K0.T*K0).inv()*K0.T
S1=tensor([I2,s.diag(1,0),K]);S2=s.zeros(16)
for vv in [s.kronecker_product(s.Matrix([1,0]),s.Matrix([1,0]),s.Matrix([0,1])),s.kronecker_product(s.Matrix([0,1]),s.Matrix([1,-1]),s.Matrix([1,1]))]:
 pp=vv*vv.T/(vv.T*vv)[0]
 for a,p in enumerate(WORDS):
  for b,q in enumerate(WORDS):
   if p[1]==q[1]:S2[a,b]+=pp[4*p[0]+2*p[2]+p[3],4*q[0]+2*q[2]+q[3]]
BB=[]
for a,b in product(range(4),repeat=2):
 h=s.zeros(4);h[a,b]=1;BB.append(B*h*B.T)
reports=[]
for n1,Q1 in [('E1',E[0]),('S1',S1)]:
 for n2,Q2 in [('E2',E[1]),('S2',S2)]:
  rows=[]
  for i,Qi in enumerate([Q1,Q2]):
   for x in [X,Z]:
    al=R[i]*local(i,x)*R[i]
    rows.append(s.Matrix.hstack(*[(comm(Q,al)*(I16-Qi)).reshape(256,1) for Q in BB]))
  A=s.Matrix.vstack(*rows);nz=[r for r in range(A.rows) if any(A.row(r))];A=A[nz,:]
  rr,piv=A.rref();report={'Q1':n1,'Q2':n2,'rank':len(piv),'nullity':16-len(piv),'rows':A.rows}
  reports.append(report);print(report,flush=True)
Path(__file__).with_name('core_group_cut_branch_scout_checks.json').write_text(json.dumps(reports,indent=2)+'\n')
