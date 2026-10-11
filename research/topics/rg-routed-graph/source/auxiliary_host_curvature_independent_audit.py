"""Independent forward-word verification of 13 curvature duals and native tests.

No import of author curvature/native test programs. Reconstruct 4F from the
support fixtures, reduce raw equal-output operator words forward, and verify
all saved dual coefficients and full-space matrices over integers/rationals.
The full tangent basis was independently validated in the earlier audit.
"""
from pathlib import Path
from itertools import product
from collections import defaultdict
import hashlib,json
import numpy as np
import sympy as s
from exact_fixtures import E,R,WORDS,I2,I16,Z,local
ROOT=Path(__file__).parent
source=json.loads((ROOT/'auxiliary_host_curvature_exact_checks.json').read_text())
data=np.load(ROOT/'auxiliary_host_compatibility_tangent_basis.npz',allow_pickle=False)
native=json.loads((ROOT/'auxiliary_host_native_coordinate_test_checks.json').read_text())
T=np.zeros((16,16,16),dtype=np.int64)
for o,ow in enumerate(WORDS):
 for a,aw in enumerate(WORDS):
  v=4*I16[a,:]-sum((8*E[i][a,:] for i in range(4) if ow[i]!=aw[i]),s.zeros(1,16))
  assert all(x.is_Integer for x in v)
  T[o,a]=[int(x) for x in v]

def reduce_equal(r,a,b):
 if r==0:return [(1+2*a+b,1)]
 return [(1+2*a+b,-1)]+([(0,1)] if a==b else [])
# Forward expansion of every raw word; unlike the author this does not
# start from a chosen normal key and enumerate its inverse preimages.
forward=defaultdict(list)
for o,a,b in product(range(16),repeat=3):
 for red in product(*[reduce_equal(WORDS[o][i],WORDS[a][i],WORDS[b][i]) for i in range(4)]):
  key=tuple(x[0] for x in red);sg=1
  for x in red:sg*=x[1]
  forward[key].append((o,a,b,sg))
L=s.zeros(8,172)
defs=[{167:1},{168:8,169:1},{164:3,165:-1,168:-1,170:1},{161:1,162:-1,164:-2,170:-2},{163:1,168:-8,170:-8},{159:1,160:-1,161:-1,162:1},{160:1,162:-1},{151:2,153:-2,164:-1,165:-1,168:1,170:-1}]
for k,d in enumerate(defs):
 for j,x in d.items():L[k,j]=x
assert L.rank()==8
piv=L.rref()[1];section=s.zeros(172,8);J=L[:,list(piv)].inv()
for k,j in enumerate(piv):section[j,:]=J[k,:]
assert L*section==s.eye(8)
coords=s.symbols('a:h')
results=[];quotient_forms=[]
for rec in source['forms']:
 terms=defaultdict(int)
 for row in rec['dual_rows']:
  p,q=row['boundary_entry'];w=row['weight']
  for o,a,b,sg in forward[tuple(row['word_key'])]:terms[o,a,b,p,q]+=w*sg
 terms={key:v for key,v in terms.items() if v}
 # lambda((4F)^* X+X^*(4F)) for arbitrary real zero-XOR X.
 # Other XORs do not enter these equal-output words, and imaginary X
 # gives pure imaginary coefficients before lambda takes real parts.
 linear=defaultdict(int)
 for (o,a,b,p,q),w in terms.items():
  linear[o,b,q]+=w*int(T[o,a,p]);linear[o,a,p]+=w*int(T[o,b,q])
 assert all(v==0 for v in linear.values())
 blocks=[];quot=None
 for typed in data.files:
  mask,kind=typed.split('_');mask=int(mask);V=np.asarray(data[typed],dtype=np.int64).reshape(-1,16,16,16);n=len(V)
  bound=2*sum(abs(w) for w in terms.values())*int(np.abs(V).max())**2
  assert bound<2**63
  B=np.zeros((n,n),dtype=np.int64)
  for (o,a,b,p,q),w in terms.items():
   x=V[:,o^mask,a,p];y=V[:,o^mask,b,q]
   B+=w*(np.outer(x,y)+np.outer(y,x))
  saved=next(x for x in rec['forms'] if x['typed_block']==typed)
  if typed=='0_real':
   M=s.Matrix(B.tolist());quot=section.T*M*section
   assert M==L.T*quot*L
   assert quot.rank()==2
   inds=saved['basis_indices']
   assert M.extract(inds,inds)==s.Matrix(saved['matrix'])
   assert not any(B[i,j] for i in range(n) for j in range(n) if i not in inds or j not in inds)
   form=s.expand((s.Matrix(1,8,coords)*quot*s.Matrix(coords))[0])
   quotient_forms.append(quot)
   blocks.append({'typed_block':typed,'rank':2})
  else:
   assert not np.any(B);assert saved['rank']==0
   blocks.append({'typed_block':typed,'rank':0})
 results.append({'number':rec['number'],'dual_rows':len(rec['dual_rows']),'combined_raw_terms':len(terms),'annihilates_arbitrary_complex_mixed_tensor':True,'quotient_quadratic':str(form),'typed_blocks':blocks})
 print('Dual',rec['number'],'exact annihilator, full-space rank2:',form,flush=True)
assert sum(len(data[k]) for k in data.files)==583
# Exact equality of the span of the 13 bilinear forms with the monomial
# graph, including scales; diagonal polynomial has twice offdiagonal entry.
edges=['ab','ac','ad','ae','af','ag','bc','bd','be','bf','bg','ch','eh']
def flat(M):return [M[i,j] for i in range(8) for j in range(i,8)]
target=[]
for edge in edges:
 i,j=[ord(x)-ord('a') for x in edge];M=s.zeros(8);M[i,j]=M[j,i]=1;target.append(M)
A=s.Matrix([flat(M) for M in quotient_forms]);B=s.Matrix([flat(M) for M in target])
assert A.rank()==B.rank()==A.col_join(B).rank()==13
assert A.rref()[0]==B.rref()[0]
independent=[]
for bits in product([0,1],repeat=8):
 supp={chr(97+i) for i,x in enumerate(bits) if x}
 if all(not set(edge)<=supp for edge in edges):independent.append(supp)
maximal=[x for x in independent if not any(x<y for y in independent)]
assert {''.join(sorted(x)) for x in maximal}=={'ah','bh','cdefg','dfgh'}
# Verify author's canonical component constraint row spaces, without using
# their component-generation algorithm.
author=json.loads((ROOT/'auxiliary_host_curvature_alternatives_checks.json').read_text())
active=author['active_basis_coordinate_indices'];expected=[]
for support in maximal:
 constraints=L[[i for i in range(8) if chr(97+i) not in support],:]
 small=constraints[:,active]
 canon=small.rref()[0]
 match=[r for r in author['maximal_simultaneously_isotropic_linear_components'] if s.Matrix([[s.Rational(v) for v in row] for row in r['constraint_rows']]).rref()[0]==canon]
 assert len(match)==1 and match[0]['dimension_in_full_tangent']==575+len(support)
 expected.append({'free_quotient_coordinates':''.join(sorted(support)),'dimension':575+len(support)})
print('Exact 13-dimensional form span; common radical575; alternatives',expected,flush=True)
# Sparse coefficient duals are actual C entries, not entries of 4C. Check
# their claimed coordinate action on all172 zero-real basis vectors.
D=s.zeros(8,4096)
for k,row in enumerate(native['coefficient_functionals']):
 assert row['name']==chr(97+k)
 for term in row['terms']:
  o,a,p=term['coefficient_index'];D[k,(o*16+a)*16+p]+=s.Rational(term['weight'])
V=s.Matrix(data['0_real'].tolist())
assert D*V.T==L
print('All8 exact coefficient functionals match basis coordinates',flush=True)
# Independently verify the ordinary boundary and physical-query directions
# claimed to lie in the common radical. On real coefficients only the real
# symmetric part of a Hermitian matrix contributes to these functionals.
radical_tests=[]
for mode in ['past','future']+[f'query_{i}_{side}' for i in range(4) for side in ['left','right']]:
 n=16 if mode in ['past','future'] else 2
 Ks=[s.zeros(n) for _ in range(8)]
 for k in range(8):
  for row in native['coefficient_functionals'][k]['terms']:
   o,a,p=row['coefficient_index'];weight=s.Rational(row['weight'])/4
   if mode=='past':
    for q in range(16):Ks[k][q,p]+=weight*int(T[o,a,q])
   elif mode=='future':Ks[k][o,o]+=weight*int(T[o,a,p])
   else:
    _,ii,side=mode.split('_');ii=int(ii);bit=1<<(3-ii)
    if side=='left':
     rr=int(bool(o&bit));Ks[k][rr,rr]+=weight*int(T[o,a,p])
    else:
     aa=int(bool(a&bit))
     for b in [0,1]:
      aprime=(a&~bit)|(b*bit);Ks[k][aa,b]+=weight*int(T[o,aprime,p])
 assert all(K+K.T==s.zeros(n) for K in Ks)
 radical_tests.append({'direction':mode,'all_eight_coordinates_zero':True})
print('All ordinary boundary and physical-query insertion coordinates vanish',flush=True)
# Construct carriers independently, from explicit vectors proved in the
# earlier all-context serial-carrier audit, rather than author's JSON.
def cylinder(i,vectors):
 cols=[];others=[j for j in range(4) if j!=i]
 for bit in [0,1]:
  for small in vectors:
   col=s.zeros(16,1)
   for k,w in enumerate(WORDS):
    if w[i]==bit:
     ix=0
     for j in others:ix=2*ix+w[j]
     col[k]=small[ix]
   cols.append(col)
 return s.Matrix.hstack(*cols)
B1=cylinder(0,[[1,0,1,0,0,0,0,0],[1,0,0,1,0,0,0,0]])
# S2=I2 tensor span{|0,0,1>, |1,-,+>} on134.
B2=cylinder(1,[[0,1,0,0,0,0,0,0],[0,0,0,0,1,1,-1,-1]])
Bs=[B1,B2,s.Matrix.hstack(*E[2].columnspace()),s.Matrix.hstack(*E[3].columnspace())]
Ss=[B*(B.H*B).inv()*B.H for B in Bs]
assert [int(s.trace(P)) for P in Ss]==[4,4,2,2]
assert Ss[0]*E[0]==E[0]
Hphys=local(0,Z)*(Ss[0]-E[0])/3
native_records=[]
units=[s.Matrix(2,2,lambda r,c:int(r==a and c==b)) for a,b in product(range(2),repeat=2)]
needed=sorted({j for j in range(4096) if any(D[k,j] for k in range(8))})
Ds=D[:,needed]
for i,Bc in enumerate(Bs):
 bit=1<<(3-i);reps=[R[i]*local(i,u)*R[i] for u in units]
 assert all(Ss[i]*rep==rep*Ss[i] for rep in reps)
 assert R[i]*local(i,Z)*R[i]==local(i,Z)
 count=0
 # These are functionals on the REAL Hermitian tangent space. Test all
 # diagonal, real-symmetric and imaginary-antisymmetric Hermitian units.
 hermitian=[]
 for a in range(Bc.cols):
  hermitian.append(Bc[:,a]*Bc[:,a].H)
  for b in range(a+1,Bc.cols):
   ab=Bc[:,a]*Bc[:,b].H;ba=ab.H
   hermitian.extend([ab+ba,s.I*(ab-ba)])
 for H in hermitian:
  mats=[H*rep for rep in reps];vals=[]
  for jj in needed:
   o,tmp=divmod(jj,256);lab,p=divmod(tmp,16)
   row=(lab&~bit)|(o&bit);unit=2*int(bool(o&bit))+int(bool(lab&bit))
   vals.append(mats[unit][row,p])
  actual=(Ds*s.Matrix(vals)).applyfunc(s.re);want=s.zeros(8,1)
  if i==0:want[7]=s.trace(Hphys*H)
  assert actual==want
  count+=1
 native_records.append({'query':i+1,'hermitian_matrix_basis_directions_verified':count,'nonzero_coordinates':['h'] if i==0 else [],'h_formula':'Tr[Z1(S1-E1)H]/3' if i==0 else '0'})
 print('Native query',i+1,'all',count,'Hermitian basis directions PASS',flush=True)
# H=Z1 Q is allowed in every active algebra: Q is its identity and the
# whole original Z1 image is in that algebra. Positivity is mathematical,
# while exact fixtures here check the required commutations and inclusion.
assert (Ss[0]-E[0])**2==Ss[0]-E[0]
assert Hphys.H==Hphys
out={'status':'PASS','basis_sha256':hashlib.sha256((ROOT/'auxiliary_host_compatibility_tangent_basis.npz').read_bytes()).hexdigest(),'basis_dimension':583,'basis_validation_reference':'auxiliary_host_compatibility_independent_audit_checks.json','duals':results,'form_span_dimension':13,'monomial_products':edges,'common_radical_dimension':575,'maximal_simultaneously_isotropic_linear_spaces':expected,'coefficient_coordinates_exact':True,'boundary_and_physical_query_tests':radical_tests,'native_insertions':native_records,'native_q1_consequence':'An actual active Q1 not contained E1 supplies H=Z1 Q1 with h>0, hence every direction of the same augmented host tangent span has c=e=0.','scope':'Necessary host-wide constraints only; no claim all possible mixed obstructions have been found, no sufficiency or routed-host exclusion.'}
(ROOT/'auxiliary_host_curvature_independent_audit_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: all13 duals, full583 space, exact four alternatives, native coordinates and scales',flush=True)
