from itertools import product
from pathlib import Path
import json
import numpy as np
O=list(product(range(2),repeat=3)); I=np.eye(8,dtype=np.int64); i2=np.eye(2,dtype=np.int64)
w=lambda p:(p[1]*(1-p[2]),(1-p[0])*p[2],p[0]*(1-p[1]))
for f in product(range(2),repeat=6):
 assert sum(all(p[k]==f[2*k+w(p)[k]] for k in range(3)) for p in O)==1
for p in O:
 for q in O:
  if p!=q: assert any(p[k]!=q[k] and w(p)[k]==w(q)[k] for k in range(3))
E=[np.diag([w(p)[k] for p in O]) for k in range(3)]
assert all(not np.any(E[j]@E[k]) for j in range(3) for k in range(j))
def native(A):
 return np.array([[np.prod([A[k][w(p)[k]][o[k],p[k]] for k in range(3)]) for p in O] for o in O],dtype=np.int64)
Z=np.diag([1,-1]); X=np.array([[0,1],[1,0]])
def raw(A):return native([(a,Z@a) for a in A])
D=raw([i2]*3)
def F(A):return raw(A)@D
assert np.array_equal(D@D,I)
units=[np.eye(2,dtype=np.int64)[:,[a]]@np.eye(2,dtype=np.int64)[[b],:] for a,b in product(range(2),repeat=2)]
# Exhaust all native tensor coefficients: each slot chooses branch and matrix unit.
nb=[(u,np.zeros((2,2),dtype=np.int64)) for u in units]+[(np.zeros((2,2),dtype=np.int64),u) for u in units]
for labels in product(range(8),repeat=3):
 C=native([nb[k] for k in labels])
 for j in range(3):assert np.array_equal(C@E[j],C if labels[j]>=4 else 0*C)
report={'status':'PASS','fixed_point_assignments':64,'native_coefficients_checked':512,'active_flag_ranks':[int(np.trace(e)) for e in E],'endpoint_grams':[]}
for j in range(3):
 gr=[np.zeros((8,8),dtype=np.int64),np.zeros((8,8),dtype=np.int64)]
 for v in product(units,repeat=2):
  context=[i2]*3
  for k,a in zip([k for k in range(3) if k!=j],v):context[k]=a
  other=F(context)
  for a in units:
   single=[i2]*3;single[j]=a;alpha=F(single)
   args=context.copy();args[j]=a;out=F(args)
   df=out-other@alpha;dl=out-alpha@other
   gr[0]+=df.T@df;gr[1]+=dl@dl.T
 assert np.array_equal(gr[1],4*I+8*E[j])
 assert np.array_equal(gr[0],8*(I-E[j]))
 report['endpoint_grams'].append({'query':j+1,'first_diagonal':gr[0].diagonal().tolist(),'last_diagonal':gr[1].diagonal().tolist(),'first_kernel_rank':2,'last_kernel_rank':0})
# Ordinary hub and the six-query composition have moving past flags.
args=[i2,X,i2];L=F([a.T for a in args]).T
moving=L.T@E[0]@L
assert not np.array_equal(moving,E[0])
report['six_query_second_block_flag_difference_HS_squared']=int(np.sum((moving-E[0])**2))
assert report['six_query_second_block_flag_difference_HS_squared']==4
Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
