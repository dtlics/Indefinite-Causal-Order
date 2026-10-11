"""Independent audit: every proper strict auxiliary partition is impossible.

Rebuild all used contexts from raw F, not the saved row tensor. Check exact
squarefree characteristic factorizations and independently reduce every one
of the four selected255-row Gaussian commutator systems.
"""
from pathlib import Path
from functools import lru_cache
from itertools import combinations
import json,math
import numpy as np
import sympy as s
from exact_fixtures import E,R,I2,I16,X,Y,Z,tensor,local,WORDS
ROOT=Path(__file__).parent
pauli=json.loads((ROOT/'strict_auxiliary_cocycle_spectral_test_checks.json').read_text())
generic=json.loads((ROOT/'strict_auxiliary_cocycle_generic_spectral_test_checks.json').read_text())
comm=json.loads((ROOT/'strict_auxiliary_last_query_commutant_checks.json').read_text())
prime=comm['prime'];imag=comm['image_of_i'];assert s.isprime(prime) and imag*imag%prime==prime-1
J=X*Z;realgates=[I2,X,Z,J]
assert generic['quaternions']==comm['quaternions']
gates=[(a*I2+s.I*b*X+c*J+s.I*d*Z)/5 for a,b,c,d in generic['quaternions']]
assert all((u.H*u-I2).applyfunc(s.expand)==s.zeros(2) for u in gates+realgates)
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16));assert D0.H*D0==I16
@lru_cache(None)
def value(kind,choice):
 bank=realgates if kind=='real_Pauli' else gates
 us=[bank[k] if k>=0 else I2 for k in choice];W=tensor(us)
 raw=(W+sum(((local(i,Z)-I16)*W*E[i] for i in range(4)),s.zeros(16)))*D0
 out=raw.applyfunc(s.expand)
 assert (out.H*out-I16).applyfunc(s.expand)==s.zeros(16)
 return out
@lru_cache(None)
def cocycle(before,kind,choice):
 left=set(before);ll=tuple(c if i+1 in left else -1 for i,c in enumerate(choice));rr=tuple(-1 if i+1 in left else c for i,c in enumerate(choice))
 C=(value(kind,rr).H*value(kind,choice)*value(kind,ll).H).applyfunc(s.expand)
 assert (C.H*C-I16).applyfunc(s.expand)==s.zeros(16)
 return C
x=s.Symbol('x');spectral=[]
def verify_factors(A,factors):
 cp=s.Poly(A.charpoly(x).as_expr(),x,extension=s.I)
 product=s.Poly(1,x,extension=s.I)
 for f,e in factors:
  f=s.Poly(f,x,extension=s.I)
  assert f.LC()==1 and s.gcd(f,f.diff()).degree()==0
  product*=f**e
 assert product==cp
 for (f,_),(g,_) in combinations(factors,2):assert s.gcd(s.Poly(f,x,extension=s.I),s.Poly(g,x,extension=s.I)).degree()==0
 assert any(e%2 for _,e in factors)
 return [int(e) for _,e in factors]
for rec in pauli['results']:
 w=rec['witness']
 if w is None:continue
 before=tuple(rec['before_queries']);C=cocycle(before,'real_Pauli',tuple(w['real_Pauli_indices']));scale=w['cocycle_integer_scale'];A=(scale*C).applyfunc(s.expand)
 assert all(a.is_Integer for a in A)
 factors=[(s.sympify(t['polynomial']),t['multiplicity']) for t in w['characteristic_factors']]
 mult=verify_factors(A,factors)
 spectral.append({'before_queries':list(before),'kind':'real_Pauli','multiplicities':mult,'exact_squarefree_factorization':True})
 print('Exact odd spectral witness',before,'real Pauli',mult,flush=True)
for rec in generic['results']:
 w=rec['odd_multiplicity_witness']
 if w is None:continue
 before=tuple(rec['before_queries']);C=cocycle(before,'quaternion',tuple(w['quaternion_indices']));scale=int(w['scale'])
 den=math.lcm(*[int(s.denom(z)) for a in C for z in a.as_real_imag()]);assert scale==den
 A=(scale*C).applyfunc(s.expand);assert all(s.re(a).is_Integer and s.im(a).is_Integer for a in A)
 factors=[]
 for f in w['squarefree_factors']:
  coeff=[s.sympify(v) for v in f['coefficients']];poly=sum(c*x**(len(coeff)-1-j) for j,c in enumerate(coeff));factors.append((poly,f['multiplicity']))
 mult=verify_factors(A,factors)
 spectral.append({'before_queries':list(before),'kind':'quaternion','multiplicities':mult,'scale':scale,'exact_squarefree_factorization':True})
 print('Exact odd spectral witness',before,'quaternion',mult,flush=True)
assert len(spectral)==10

denominators=set()
def residue(z):
 a,b=s.expand(z).as_real_imag();a=s.Rational(a);b=s.Rational(b)
 for q in [int(a.q),int(b.q)]:
  assert math.gcd(q,prime)==1;denominators.add(q)
 return (int(a.p)*pow(int(a.q),-1,prime)+imag*int(b.p)*pow(int(b.q),-1,prime))%prime
# Dense modular elimination is independent of the author's sparse pivot map.
def rank_minor(A):
 A=np.array(A,dtype=np.int64);m,n=A.shape;rank=0;piv=[];det=1
 for col in range(n):
  candidates=np.flatnonzero(A[rank:,col]%prime)
  if not len(candidates):continue
  rr=rank+int(candidates[0])
  if rr!=rank:A[[rank,rr]]=A[[rr,rank]];det=-det
  pivot=int(A[rank,col]);det=det*pivot%prime
  A[rank]=A[rank]*pow(pivot,-1,prime)%prime
  for r in range(rank+1,m):
   z=int(A[r,col])
   if z:A[r]=(A[r]-z*A[rank])%prime
  piv.append(col);rank+=1
  if rank==m:break
 return rank,piv,int(det%prime)
comm_results=[]
for rec in comm['results']:
 before=tuple(rec['before_queries']);rows=[];contexts={}
 for item in rec['rank_rows']:
  kind=item['context']['type'];choice=tuple(item['context']['indices']);key=(kind,choice)
  if key not in contexts:
   C=cocycle(before,kind,choice)
   if kind=='real_Pauli':C=64*C;assert all(a.is_Integer for a in C)
   # Independent Kronecker form for row-major [C,H].
   K=s.kronecker_product(C,I16)-s.kronecker_product(I16,C.T)
   identity=s.Matrix([int(i==j) for i in range(16) for j in range(16)])
   assert K*identity==s.zeros(256,1)
   contexts[key]=K
  a,b=item['entry'];row=contexts[key][16*a+b,:]
  rows.append([residue(z) for z in row])
 assert len(rows)==255
 rank,piv,det=rank_minor(rows)
 assert rank==255 and det!=0
 # The exact identity matrix is a nonzero common kernel vector, proving
 # the opposite upper rank255. No positive parameter inference is needed.
 comm_results.append({'last_query':rec['last_query'],'before_queries':list(before),'selected_rows':255,'contexts':len(contexts),'rank_mod_prime':rank,'certified_nonzero_minor_columns':piv,'minor_determinant_mod_prime':det,'exact_common_commutant_dimension':1})
 print('Exact scalar common commutant, last',rec['last_query'],'255 rows, minor det modp',det,flush=True)
partitions={tuple(r['before_queries']) for r in spectral+comm_results}
assert len(partitions)==14 and partitions=={tuple(i+1 for i in range(4) if mask&(1<<(3-i))) for mask in range(1,15)}
# Exact zero intersections used for the rank-two refined M2 block placement.
def cyl(i,vs):
 cols=[]
 for bit in [0,1]:
  for v in vs:
   col=s.zeros(16,1)
   for k,w in enumerate(WORDS):
    if w[i]==bit:
     ix=0
     for j,b in enumerate(w):
      if j!=i:ix=2*ix+b
     col[k]=v[ix]
   cols.append(col)
 B=s.Matrix.hstack(*cols);return B*(B.H*B).inv()*B.H
S=[cyl(0,[[1,0,1,0,0,0,0,0],[1,0,0,1,0,0,0,0]]),cyl(1,[[0,1,0,0,0,0,0,0],[0,0,0,0,1,1,-1,-1]]),E[2],E[3]]
minus=s.Matrix([1,-1]);one=s.Matrix([0,1]);q=s.kronecker_product(minus*minus.T/2,one*one.T);Q12=s.kronecker_product(s.eye(4),q)
assert all(s.Matrix.vstack(I16-P,I16-Q12).rank()==16 for P in S)
out={'status':'PASS','prime':prime,'image_of_i':imag,'prime_and_square_root_verified':True,'rational_denominators_reduced':sorted(denominators),'all_denominators_invertible_mod_prime':True,'spectral_partition_witnesses':spectral,'commutant_partition_witnesses':comm_results,'all14_proper_partitions_excluded':True,'strict_full_Mr_boundary_only':[2,4,8,16],'serial_Sj_intersection_Q12_dimensions':[0,0,0,0],'scope':'Finite exact negative witnesses exclude each proper strict partition. No sample-based positive claim; actual unbranched M2 auxiliaries with nontrivial native comparisons retain repeated-multiplicity residual blocks.'}
(ROOT/'strict_auxiliary_complete_independent_audit_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: all proper strict partitions excluded; full nontrivial matrix auxiliary is boundary-only',flush=True)
