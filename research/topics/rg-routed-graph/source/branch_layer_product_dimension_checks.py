"""Exact partial-exchange and module audit of same-SCC product capacity."""
from pathlib import Path
from itertools import product,combinations
import json
import sympy as s
ROOT=Path(__file__).parent
BITS=list(product((0,1),repeat=3))
def w(o):
 a,b,c=o;return (b*(1-c),(1-a)*c,a*(1-b))
def n(x):return 4*x[0]+2*x[1]+x[2]
def embed(i,f):
 fs=[s.eye(2)]*3;fs[i]=f;return s.kronecker_product(*fs)
def kron(*fs):
 entries={(0,0):s.S.One};nr=nc=1
 for f in fs:
  rr,cc=f.shape;ee=f.todok()
  entries={(a*rr+c,b*cc+d):u*v for (a,b),u in entries.items() for (c,d),v in ee.items()}
  nr*=rr;nc*=cc
 return s.SparseMatrix(nr,nc,entries)
# Green full exchange, transposed and ordered as a RED exchange:
# input = old future o, old C-input c, old R-input r;
# output = old past p, old C-output t, old R-output v.
full={}
for p,t,v in product(BITS,repeat=3):
 sols=[o for o in BITS if all(o[i]==(t[i] if w(o)[i]==0 else v[i]) for i in range(3))]
 assert len(sols)==1;o=sols[0];xx=w(o)
 c=tuple(p[i] if xx[i]==0 else t[i] for i in range(3))
 r=tuple(p[i] if xx[i]==1 else v[i] for i in range(3))
 full[p,t,v,o,c,r]=1
assert len({(o,c,r) for p,t,v,o,c,r in full})==512
# Current losing joint pattern B={0,1,2}.
TB=s.SparseMatrix(512,512,{(64*n(p)+8*n(t)+n(v),64*n(o)+8*n(c)+n(r)):1
      for p,t,v,o,c,r in full if w(o)==(0,0,0)})
assert len(TB.todok())==128
for b in range(3):
 for a,d in product((0,1),repeat=2):
  f=s.zeros(2);f[a,d]=1;f=embed(b,f)
  right=kron(s.eye(8),f,s.eye(8))
  left=kron(f,s.eye(64))
  assert TB*right==left*TB
# Exact old-past R recovery: active winner uses I; inactive uses I/2.
# Right-domain R patterns are specified by w(o), independent of current c.
from collections import defaultdict
small=defaultdict(lambda:s.S.Zero)
for p,t,v,o,c,r in full:
 weight=s.prod(int(v[i]==r[i]) if w(o)[i]==1 else s.Rational(int(v[i]==r[i]),2) for i in range(3))
 if weight:small[p,t,o,c]+=weight
assert len(small)==64 and set(small.values())=={1}
results=[]
for k in (1,2,3):
 for B in combinations(range(3),k):
  entries={(8*n(p)+n(t),8*n(o)+n(c)):weight for (p,t,o,c),weight in small.items()
           if all(w(o)[b]==0 for b in B)}
  S=s.SparseMatrix(64,64,entries)
  for b in B:
   for a,d in product((0,1),repeat=2):
    f=s.zeros(2);f[a,d]=1;f=embed(b,f)
    assert S*kron(s.eye(8),f)==kron(f,s.eye(8))*S
  # Matrix of all partial-Cin row vectors, with each vector on original F.
  rows=s.zeros(8,512)
  for (r,c),v in entries.items():
   p,t=divmod(r,8);rows[p,64*t+c]=v
  dim=rows.rank();assert dim==8 and dim%(2**k)==0
  # Closing all current branches at identity gives the diagonal joint flag.
  rank=sum(all(w(o)[b]==0 for b in B) for o in BITS)
  results.append({'marked_losing_vertices':B,'native_dimension_product':2**k,
                  'module_dimension':dim,'fully_closed_origin_marker_rank':rank})
assert results[-1]['fully_closed_origin_marker_rank']==2
out={'status':'PASS','boundary_dimension':8,'before_recovery_exchange_dimension':512,
 'before_recovery_joint_marked_nonzero_entries':128,'full_matrix_unit_intertwiners_checked':12,
 'after_recovery_exchange_dimension':64,'same_vertex_winner_sibling_recovery_exact':True,
 'module_results':results,'product_saturates_boundary_for_three_branches':True,
 'joint_origin_marker_rank_not_divisible_by_product':True,
 'scope':'Exact red-Lugano exchange/module calibration. General product bound is proved algebraically in the accompanying note.'}
(ROOT/'branch_layer_product_dimension_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
