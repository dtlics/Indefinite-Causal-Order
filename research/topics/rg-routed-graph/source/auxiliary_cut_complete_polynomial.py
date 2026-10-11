"""Exact free-unitary-word certificate for the {1,2}|{3,4} cut.
No sampling: reduces U*U / UU* only, valid for arbitrary private operator blocks.
"""
import itertools,json
from collections import defaultdict
import numpy as np
import sympy as s
from exact_fixtures import I16,E,local,Z,tensor,I2,WORDS
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16));V=[I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16)) for o in WORDS]
T=[]
for v in V:
 A=4*v*D0;assert all(x.q==1 for x in A);T.append(np.array(A,dtype=np.int64))
T=np.array(T)
assert np.max(np.abs(T))<=4
# Every unreduced term has entries <=4*(16*4*(16*4))=16384.
# There are at most 256*4*16 terms and <=16 reduction descendants each.
# Thus every intermediate accumulated coefficient is bounded by 2**32;
# the final subtraction adds at most 64. All int64 operations are exact.
integer_bound=2**32+64
assert integer_bound < np.iinfo(np.int64).max
# Coefficient matrices multiplied by four.
left={};right={}
for oo,jj in itertools.product(range(4),repeat=2):
 a=np.zeros((16,16),dtype=np.int64);b=a.copy()
 for rr in range(4):
  o=4*oo+rr;i=4*jj+rr;a[o,:]=T[o,i,:]
  o=4*rr+oo;i=4*rr+jj;b[o,:]=T[o,i,:]
 left[oo,jj]=a;right[oo,jj]=b
K=np.array(tensor([I2,I2,s.Matrix([1,-1]),s.Matrix([0,1])]),dtype=np.int64)
# 0 is constant, 1+4*x+y is the formal (left coefficient, right coefficient) word.
def reduce_word(x,y,orient):
 a,b=divmod(x,2);c,d=divmod(y,2)
 if orient=='UU*' and b==d==1:
  z=[(1+4*(2*a)+(2*c),-1)]
  if a==c:z.append((0,1))
  return z
 if orient=='U*U' and a==c==1:
  z=[(1+4*b+d,-1)]
  if b==d:z.append((0,1))
  return z
 return [(1+4*x+y,1)]
poly={};term_count=0
for o,i in itertools.product(range(16),repeat=2):
 ob=WORDS[o];ib=WORDS[i]
 for jr in range(4):
  jr_b=(jr//2,jr%2);lv=right[o%4,jr][o,:] # R-coefficient dagger |o>
  if not np.any(lv):continue
  rwords=[reduce_word(2*ob[k]+jr_b[k-2],2*ob[k]+ib[k],'U*U') for k in [2,3]]
  for ol,jl in itertools.product(range(4),repeat=2):
   ol_b=(ol//2,ol%2);jl_b=(jl//2,jl%2)
   rv=T[o,i,:]@left[ol,jl].T@K
   if not np.any(rv):continue
   M=np.outer(lv,rv)
   lwords=[reduce_word(2*ob[k]+ib[k],2*ol_b[k]+jl_b[k],'UU*') for k in [0,1]]
   for choices in itertools.product(*(lwords+rwords)):
    key=tuple(x[0] for x in choices);sgn=np.prod([x[1] for x in choices]);
    if key in poly:poly[key]+=sgn*M
    else:poly[key]=sgn*M.copy()
   term_count+=1
key=(0,0,0,0)
assert key in poly
poly[key]-=64*K
bad=[(key,int(np.max(np.abs(v)))) for key,v in poly.items() if np.any(v)]
out={'status':'PASS' if not bad else 'FAIL','coefficient_scale':64,'certified_absolute_integer_bound':integer_bound,'matrix_terms_before_reduction':term_count,'normal_word_keys':len(poly),'nonzero_defect_keys':len(bad),'first_bad':bad[:10],'private_ancilla_scope':'Arbitrary independently sized ancillary operator blocks: uses only each original unitary block matrix U_i U_i*=I for i=1,2 and U_i*U_i=I for i=3,4.'}
print(json.dumps(out,indent=2));json.dump(out,open('auxiliary_cut_complete_polynomial_checks.json','w'),indent=2)
assert not bad
