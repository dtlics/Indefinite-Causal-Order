"""No nonzero projection in S_j can commute with another original factor alpha_i."""
from pathlib import Path
from itertools import product
import json,sympy as s
from exact_fixtures import E,I2,I16,R,X,Y,Z,local,tensor,WORDS
ROOT=Path(__file__).parent;cuts=json.loads((ROOT/'continuous_product_supported_cut_audit_all_cylinders_checks.json').read_text())['cuts']
S=[]
for j in range(4):
 rec=next(x for x in cuts if x['before_queries']==[j+1]);rr=[i for i in range(4) if i!=j];cols=[]
 for b in range(2):
  for vv in rec['after_carrier_basis']:
   v=s.Matrix([s.sympify(x) for x in vv]);col=s.zeros(16,1)
   for bits in product(range(2),repeat=3):
    w=[0]*4;w[j]=b
    for i,a in zip(rr,bits):w[i]=a
    col[sum(a<<(3-i) for i,a in enumerate(w))]=v[sum(a<<(2-i) for i,a in enumerate(bits))]
   cols.append(col)
 B=s.Matrix.hstack(*cols);S.append(B*(B.H*B).inv()*B.H)
out=[]
for j,i in product(range(4),repeat=2):
 if i==j:continue
 assert S[j]*E[i]==s.zeros(16)
 spectators=[k for k in range(4) if k!=i]
 def embed(bits,b):
  w=[0]*4;w[i]=b
  for k,a in zip(spectators,bits):w[k]=a
  return sum(a<<(3-k) for k,a in enumerate(w))
 words=list(product(range(2),repeat=3));A=I16-S[j]
 Q=s.Matrix(8,8,lambda a,b:sum(A[embed(words[a],z),embed(words[b],z)] for z in range(2)))
 assert Q.rank()==8
 out.append({'support_query':j+1,'other_factor_query':i+1,'partial_trace_complement_rank':8,'determinant':str(Q.det()),'largest_cross_cylinder_rank':0})
 print(out[-1],flush=True)
(ROOT/'cross_serial_cylinder_geometry_checks.json').write_text(json.dumps({'status':'PASS','results':out,'consequence':'For i!=j, no nonzero projection P<=S_j commutes with alpha_i(M2). S_j is orthogonal to E_i, so commutation with alpha_i is equivalent to physical i-factor commutation; every such projection is an i-cylinder, excluded by the positive partial-trace complement.'},indent=2)+'\n')
