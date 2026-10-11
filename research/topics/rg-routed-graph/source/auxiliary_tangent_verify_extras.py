"""Verify every reduced complete tangent word equation for rational extra directions."""
import itertools,json,numpy as np,sympy as s
from exact_fixtures import I16,E,local,Z,WORDS
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16));T=[]
for o in WORDS:
 v=I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16));A=4*v*D0;assert all(x.q==1 for x in A);T.append(np.array(A,dtype=np.int64))
T=np.array(T);ds=json.load(open('auxiliary_tangent_extra_directions.json'))['directions'];out=[]
for mask in [0,1,2,4]:
 for kind in ['real','imag']:
  dd=[d for d in ds if d['mask']==mask and d['kind']==kind];N=len(dd);C=np.zeros((16,16,16,N),dtype=np.int64)
  for k,d in enumerate(dd):
   for idx,v in d['integer_coefficients'].items():
    r,t=divmod(int(idx),256);a,b=divmod(t,16);C[r,a,b,k]=v
  assert np.max(np.abs(C))<=78
  parity=-1 if kind=='real' else 1;opts=[]
  for bit in [8,4,2,1]:
   if mask&bit:opts.append([[(r,a,1-r,b,1)] for r,a,b in itertools.product(range(2),repeat=3)])
   else:opts.append([[(1,a,1,a,1) for a in range(2)]]+[[(0,a,0,b,1),(1,a,1,b,-1)] for a,b in itertools.product(range(2),repeat=2)])
  count=0;bad=0
  for choice in itertools.product(*(range(len(x)) for x in opts)):
   M=np.zeros((16,16,N),dtype=np.int64)
   for term in itertools.product(*[opts[k][choice[k]] for k in range(4)]):
    r=sum(term[k][0]<<(3-k) for k in range(4));a=sum(term[k][1]<<(3-k) for k in range(4));rr=sum(term[k][2]<<(3-k) for k in range(4));b=sum(term[k][3]<<(3-k) for k in range(4));sg=int(np.prod([t[4] for t in term]))
    M+=sg*(T[r,a,:,None,None]*C[r,b,None,:,:]+parity*C[rr,a,:,None,:]*T[rr,b,None,:,None])
   assert np.max(np.abs(M))<=16*2*4*78
   if np.any(M):bad+=1
   count+=1
  assert not bad
  out.append({'mask':mask,'kind':kind,'rational_directions':N,'all_normal_word_coefficients_checked':count*256*N,'nonzero_defect_coefficients':0})
  print(out[-1],flush=True)
json.dump({'status':'PASS','extra_directions':len(ds),'certified_absolute_integer_bound':16*2*4*78,'blocks':out,'conclusion':'Together with the explicit 557-dimensional boundary/cut subspace and the 583-dimensional modular upper bound, the complete real tangent dimension is exactly 583.'},open('auxiliary_tangent_verify_extras_checks.json','w'),indent=2)
