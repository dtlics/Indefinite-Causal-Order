import itertools,json,numpy as np,sympy as s
from exact_fixtures import I16,E,local,Z,WORDS
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16));F=[]
for o in WORDS:
 V=I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16));F.append(np.array(4*V*D0,dtype=np.int64))
F=np.array(F);T=F.copy()
for r in range(16):
 for n,nw in enumerate(WORDS):T[r,n]*=1 if((nw[0]==0 and nw[3]==0)or(nw[0]==1 and nw[2]==0))else -1
j=json.load(open('auxiliary_input_flag_anticommutant_basis_checks.json'));ds=j['directions'];out=[]
for mask in [0,4]:
 for kind in ['real','imag']:
  dd=[d for d in ds if d['mask']==mask and d['kind']==kind];N=len(dd);C=np.zeros((16,16,16,N),dtype=np.int64)
  for k,d in enumerate(dd):
   for idx,v in d['integer_coefficients'].items():
    r,t=divmod(int(idx),256);n,p=divmod(t,16);C[r,n,p,k]=v
  opts=[]
  for bit in [8,4,2,1]:
   if mask&bit:opts.append([[(r,a,1-r,b,1)] for r,a,b in itertools.product(range(2),repeat=3)])
   else:opts.append([[(1,a,1,a,1) for a in range(2)]]+[[(0,a,0,b,1),(1,a,1,b,-1)] for a,b in itertools.product(range(2),repeat=2)])
  for label,A,parity in [('complete tangent',F,-1 if kind=='real'else 1),('flag anticommutant',T,1 if kind=='real'else -1)]:
   bad=0;count=0
   for key in itertools.product(*(range(len(a)) for a in opts)):
    M=np.zeros((16,16,N),dtype=np.int64)
    for term in itertools.product(*[opts[key_i][key[key_i]] for key_i in range(4)]):
     r=sum(term[k][0]<<(3-k) for k in range(4));a=sum(term[k][1]<<(3-k) for k in range(4));rr=sum(term[k][2]<<(3-k) for k in range(4));b=sum(term[k][3]<<(3-k) for k in range(4));sg=int(np.prod([t[4] for t in term]));M+=sg*(A[r,a,:,None,None]*C[r,b,None,:,:]+parity*C[rr,a,:,None,:]*A[rr,b,None,:,None])
    if np.any(M):bad+=1
    count+=1
   assert bad==0;out.append({'mask':mask,'kind':kind,'condition':label,'rational_directions':N,'normal_keys':count,'nonzero_coefficients':0});print(out[-1],flush=True)
json.dump({'status':'PASS','exact_real_dimension':22,'conditions':out,'scope':'Complete linear tangent and anticommutation only; not yet a unital quantum lift.'},open('auxiliary_input_flag_anticommutant_verify_checks.json','w'),indent=2)
