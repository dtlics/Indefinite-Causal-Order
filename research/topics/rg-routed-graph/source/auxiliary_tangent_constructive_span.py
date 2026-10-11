"""Explicit boundary + supported-cut tangent basis, exact modular independence."""
import itertools,json,numpy as np,sympy as s
from exact_fixtures import I16,I2,E,R,local,Z,WORDS,tensor
p=1000003
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16))
def modmat(A):return np.array([[int(x.p)*pow(int(x.q),-1,p)%p for x in row] for row in A.tolist()],dtype=np.int64)
F=np.zeros((16,16,16,16),dtype=np.int64) # query output,input,future,source
for o,ob in enumerate(WORDS):
 v=I16-2*sum((ob[i]*E[i] for i in range(4)),s.zeros(16));rows=modmat(v*D0)
 for n in range(16):F[o,n,o,:]=rows[n,:]
left={};right={}
for oo,jj in itertools.product(range(4),repeat=2):
 left[oo,jj]=sum((F[4*oo+r,4*jj+r] for r in range(4)),np.zeros((16,16),dtype=np.int64))%p
 right[oo,jj]=sum((F[4*r+oo,4*r+jj] for r in range(4)),np.zeros((16,16),dtype=np.int64))%p
j=json.load(open('auxiliary_supported_cut_spaces_checks.json'));Bs=[]
for i in range(4):
 x=next(x for x in j if x['before_queries']==[i+1]);Bs.append(s.Matrix.hstack(*[s.Matrix([s.sympify(v) for v in b]) for b in x['basis']]))
Bs.append(tensor([I2,I2,s.Matrix([1,-1]),s.Matrix([0,1])]))
pivots={(m,kind):{} for m in range(16) for kind in ['real','imag']};records=[]
def add(C,kind,label):
 for mask in range(16):
  # C indexed output,input,future,source
  v=np.array([C[r^mask,n,r,q] for r in range(16) for n in range(16) for q in range(16)],dtype=np.int64)
  rr={i:int(x) for i,x in enumerate(v) if x}
  pp=pivots[mask,kind]
  while rr:
   col=min(rr);a=rr[col]
   if col not in pp:
    inv=pow(a,-1,p);pp[col]={i:x*inv%p for i,x in rr.items()};records.append({'mask':mask,'kind':kind,'label':label});break
   for i,x in pp[col].items():
    z=(rr.get(i,0)-a*x)%p
    if z:rr[i]=z
    elif i in rr:del rr[i]
def gens(n):
 for a in range(n):
  H=s.zeros(n);H[a,a]=1;yield H,'real',[a,a]
 for a in range(n):
  for b in range(a+1,n):
   H=s.zeros(n);H[a,b]=H[b,a]=1;yield H,'real',[a,b]
   H=s.zeros(n);H[a,b]=1;H[b,a]=-1;yield H,'imag',[a,b]
for kindside in ['past','future']:
 for H,kind,ab in gens(16):
  h=modmat(H);C=np.empty_like(F)
  for o,n in itertools.product(range(16),repeat=2):C[o,n]=(F[o,n]@h if kindside=='past' else h@F[o,n])%p
  add(C,kind,[kindside,*ab])
 print(kindside,'done',flush=True)
units=[s.Matrix([[int(r==a and c==b) for c in range(2)] for r in range(2)]) for a,b in itertools.product(range(2),repeat=2)]
for i,B in enumerate(Bs[:4]):
 aa=[modmat(R[i]*local(i,u)*R[i]) for u in units]
 for H,kind,ab in gens(B.cols):
  h=modmat(B*H*B.H);C=np.zeros_like(F)
  for o,n in itertools.product(range(16),repeat=2):
   ob=WORDS[o];nb=WORDS[n];bar=tensor([I2 if j==i else units[2*ob[j]+nb[j]] for j in range(4)]);bb=modmat(bar)
   C[o,n]=((bb@h)%p@aa[2*ob[i]+nb[i]])%p
  add(C,kind,['serial',i+1,*ab])
 print('serial',i+1,'done',flush=True)
B=Bs[4]
for H,kind,ab in gens(B.cols):
 h=modmat(B*H*B.H);C=np.empty_like(F)
 for o,n in itertools.product(range(16),repeat=2):C[o,n]=((right[o%4,n%4]@h)%p@left[o//4,n//4])%p
 add(C,kind,['cut12',*ab])
print('cut12 done',flush=True)
for i in range(4):
 for hh,kind,ab in gens(2):
  h=modmat(hh)
  for side in ['pre','post']:
   C=np.zeros_like(F)
   for o,n in itertools.product(range(16),repeat=2):
    bit=1<<(3-i);ob=WORDS[o];nb=WORDS[n]
    for a in range(2):
     if side=='post':C[o,n]=(C[o,n]+h[a,ob[i]]*F[(o&~bit)|(a*bit),n])%p
     else:C[o,n]=(C[o,n]+h[nb[i],a]*F[o,(n&~bit)|(a*bit)])%p
   add(C,kind,['query_'+side,i+1,*ab])
 print('query local',i+1,'done',flush=True)
rows=[{'mask':m,'real_dimension':len(pivots[m,'real']),'imag_dimension':len(pivots[m,'imag'])} for m in range(16)]
print(json.dumps(rows,indent=2));print('total',sum(x['real_dimension']+x['imag_dimension'] for x in rows),flush=True)
json.dump({'prime':p,'blocks':rows,'basis_records':records,'total_dimension_lower_bound':sum(x['real_dimension']+x['imag_dimension'] for x in rows)},open('auxiliary_tangent_constructive_span_checks.json','w'),indent=2)

json.dump({f'{m}_{kind}':{str(k):{str(j):v for j,v in row.items()} for k,row in pivots[m,kind].items()} for m in [0,1,2,4] for kind in ['real','imag']},open('auxiliary_tangent_constructive_span_echelons.json','w'))
