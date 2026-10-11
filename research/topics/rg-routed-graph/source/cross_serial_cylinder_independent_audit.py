"""Independent exact positivity certificate for cross-query carrier geometry."""
from pathlib import Path
from itertools import product
import json
import sympy as s
from exact_fixtures import E,R,I16,WORDS
ROOT=Path(__file__).parent

def cylinder(i,vectors):
 cols=[]
 for bit in [0,1]:
  for v in vectors:
   cols.append(s.Matrix([v[sum(w[j]<<(2-k) for k,j in enumerate([t for t in range(4) if t!=i]))] if w[i]==bit else 0 for w in WORDS]))
 B=s.Matrix.hstack(*cols);return B*(B.H*B).inv()*B.H
S=[cylinder(0,[[1,0,1,0,0,0,0,0],[1,0,0,1,0,0,0,0]]),
   cylinder(1,[[0,1,0,0,0,0,0,0],[0,0,0,0,1,1,-1,-1]]),E[2],E[3]]
source=json.loads((ROOT/'cross_serial_cylinder_geometry_checks.json').read_text())['results'];rows=[]
for j,i in product(range(4),repeat=2):
 if i==j:continue
 assert S[j]**2==S[j] and S[j].H==S[j]
 assert S[j]*E[i]==s.zeros(16) and R[i]*S[j]*R[i]==S[j]
 others=[k for k in range(4) if k!=i];rest=list(product([0,1],repeat=3))
 def embed(v,bit):
  w=[0]*4;w[i]=bit
  for k,b in zip(others,v):w[k]=b
  return sum(w[k]<<(3-k) for k in range(4))
 A=I16-S[j];Q=s.Matrix(8,8,lambda a,b:sum(A[embed(rest[a],t),embed(rest[b],t)] for t in [0,1]))
 minors=[Q[:k,:k].det() for k in range(1,9)]
 assert all(d>0 for d in minors)
 author=next(r for r in source if r['support_query']==j+1 and r['other_factor_query']==i+1)
 assert Q.det()==s.Rational(author['determinant'])
 rows.append({'support_query':j+1,'other_factor_query':i+1,'R_i_fixes_support':True,'partial_trace_positive_definite':True,'leading_principal_minors':[str(d) for d in minors],'determinant':str(Q.det()),'cross_commuting_projection_must_be_zero':True})
(ROOT/'cross_serial_cylinder_independent_audit_checks.json').write_text(json.dumps({'status':'PASS','pairs':rows,'scope':'No nonzero P<=S_j commutes with alpha_i(M2) for i!=j. All twelve certificates are exact; the graph non-nesting consequence separately needs the branched flag-loop theorem.'},indent=2)+'\n')
print('PASS: all12 cross-carrier partial traces positive definite; no cross commuting projection')
