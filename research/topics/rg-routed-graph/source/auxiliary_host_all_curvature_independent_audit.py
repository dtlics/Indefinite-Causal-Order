"""Independent exact audit of all-sector host curvature certificates.

Rebuild raw operator words FORWARD; derive complex phase signs explicitly;
evaluate every compatible pair among all72 nonboundary directions, rather
than reusing the discovery scout's pair list. Verify the boundary quotient
and reconstruct every minimal-native direction on all4096 coefficients.
"""
from pathlib import Path
from itertools import product
from collections import defaultdict
from functools import lru_cache
import hashlib,math,json
import numpy as np
import sympy as s
from exact_fixtures import E,R,WORDS,I2,I16,X,Y,Z,local
ROOT=Path(__file__).parent
source=json.loads((ROOT/'auxiliary_host_all_curvature_exact_checks.json').read_text())
meta=json.loads((ROOT/'auxiliary_host_compatibility_form_checks.json').read_text())
data=np.load(ROOT/'auxiliary_host_compatibility_tangent_basis.npz',allow_pickle=False)
T=np.zeros((16,16,16),dtype=np.int64)
for o,ow in enumerate(WORDS):
 for a,aw in enumerate(WORDS):
  row=4*I16[a,:]-sum((8*E[i][a,:] for i in range(4) if ow[i]!=aw[i]),s.zeros(1,16))
  assert all(x.is_Integer for x in row)
  T[o,a]=[int(x) for x in row]
# Verify all511 declared boundary basis directions against F H or H F.
boundary=0;complement=[];labels=[]
for key,labs in meta['basis_labels'].items():
 mask,kind=key.split('_');mask=int(mask);sg=1 if kind=='real' else -1
 for idx,lab in enumerate(labs):
  V=data[key][idx].reshape(16,16,16)
  if lab[0] not in ['past','future']:
   complement.append(V);labels.append({'mask':mask,'kind':kind,'typed_basis_index':idx,'label':lab});continue
  H=np.array([V[f,f^mask] for f in range(16)],dtype=np.int64)
  assert np.array_equal(H.T,sg*H)
  if lab[0]=='past':
   assert mask==0
   assert np.array_equal(4*V,np.einsum('oaq,qp->oap',T,H))
  else:
   assert all(H[f,p]==0 for f in range(16) for p in range(16) if p!=f^mask)
   assert np.array_equal(4*V,np.array([H[f,f^mask]*T[f^mask] for f in range(16)]))
  boundary+=1
assert boundary==511 and len(complement)==72 and labels==source['coordinate_labels']
# Direct coefficient full-span check: the 16 row vectors for each future
# row o form an invertible 16x16 matrix, so coefficient span(F)=M16.
assert all(s.Matrix(T[o].tolist()).det()!=0 for o in range(16))
print('Boundary511 directions exact; complement72; coefficient span M16',flush=True)
V=np.asarray(complement,dtype=np.int64);masks=np.array([x['mask'] for x in labels]);kinds=np.array([int(x['kind']=='imag') for x in labels])
lookup={(x['mask'],x['kind'],x['typed_basis_index']):i for i,x in enumerate(labels)}

def local_reduction(r,a,t,b):
 if r!=t:return [(4*r+2*a+b,1)]
 if r==0:return [(1+2*a+b,1)]
 return [(1+2*a+b,-1)]+([(0,1)] if a==b else [])
@lru_cache(None)
def forward_sector(kappa):
 out=defaultdict(list)
 for r,a,b in product(range(16),repeat=3):
  t=r^kappa
  for red in product(*[local_reduction(WORDS[r][i],WORDS[a][i],WORDS[t][i],WORDS[b][i]) for i in range(4)]):
   key=tuple(x[0] for x in red);sign=math.prod(x[1] for x in red)
   out[key].append((r,a,t,b,sign))
 return out

def component(z,mode):return int(z.real if mode=='real' else z.imag)
allforms=[];report=[];sector_flat=defaultdict(list);gram=np.zeros((72,72),dtype=np.int64)
for number,rec in enumerate(source['forms']):
 kappa,mode=rec['sector'];forward=forward_sector(kappa);terms=defaultdict(int)
 for rr in rec['dual_rows']:
  p,q=rr['boundary_entry']
  for r,a,t,b,sg in forward[tuple(rr['word_key'])]:terms[r,a,t,b,p,q]+=rr['weight']*sg
 terms={key:w for key,w in terms.items() if w}
 # Extract Re/Im of coefficients for both E=X and E=iX explicitly.
 for ekind in [0,1]:
  z=1j**ekind;p1=component(z,mode);p2=component(z.conjugate(),mode)
  linear=defaultdict(int)
  for (r,a,t,b,p,q),w in terms.items():
   linear[r,b,q]+=w*p1*int(T[r,a,p])
   linear[t,a,p]+=w*p2*int(T[t,b,q])
  assert all(v==0 for v in linear.values())
 # Generate ALL pairs independently. Only matching mask/parity can enter.
 pairs=[(i,j) for i in range(72) for j in range(i,72) if (masks[i]^masks[j])==kappa and (kinds[i]^kinds[j])==int(mode=='imag')]
 ii=np.array([i for i,j in pairs]);jj=np.array([j for i,j in pairs]);values=np.zeros(len(pairs),dtype=np.int64)
 p1=np.array([component((1j**int(kinds[i])).conjugate()*(1j**int(kinds[j])),mode) for i,j in pairs],dtype=np.int64)
 p2=np.array([component((1j**int(kinds[j])).conjugate()*(1j**int(kinds[i])),mode) for i,j in pairs],dtype=np.int64)
 bound=2*sum(abs(w) for w in terms.values())*int(np.abs(V).max())**2
 assert bound<2**63
 for (r,a,t,b,p,q),w in terms.items():
  f=r^masks[ii];g=r^masks[jj]
  assert np.all(f==t^masks[jj]) and np.all(g==t^masks[ii])
  values+=w*(p1*V[ii,f,a,p]*V[jj,f,b,q]+p2*V[jj,g,a,p]*V[ii,g,b,q])
 divisor=math.gcd(*[int(x) for x in values if x]);assert divisor==rec['bilinear_normalization_divisor']
 values//=divisor;B=np.zeros((72,72),dtype=np.int64)
 for (i,j),value in zip(pairs,values):B[i,j]=B[j,i]=value
 saved=np.zeros((72,72),dtype=np.int64)
 for entry in rec['bilinear_entries']:
  i,j=entry['coordinates'];saved[i,j]=saved[j,i]=entry['value']
 assert np.array_equal(B,saved)
 assert 204*72*int(np.abs(B).max())**2<2**63
 gram+=B.T@B;allforms.append(B)
 sector_flat[kappa,mode].append(values.tolist())
 report.append({'sector':[kappa,mode],'number':rec['number'],'dual_rows':len(rec['dual_rows']),'combined_raw_terms':len(terms),'exact_complex_mixed_annihilator':True,'all_compatible_pairs_checked':len(pairs),'exact_bilinear_matrix_matches':True})
 if number%20==0:print('Verified form',number,'sector',kappa,mode,flush=True)
assert len(allforms)==204
sector_ranks=[]
for key,rows in sector_flat.items():
 rank=s.polys.matrices.DomainMatrix.from_Matrix(s.Matrix(rows)).convert_to(s.QQ).rank()
 assert rank==len(rows)
 sector_ranks.append({'sector':list(key),'rank':rank})
GG=s.Matrix(gram.tolist());rank=s.polys.matrices.DomainMatrix.from_Matrix(GG).convert_to(s.QQ).rank()
assert rank==37
rad=s.Matrix.hstack(*[s.Matrix([s.Rational(x) for x in col]) for col in source['quotient_common_radical_basis']])
assert rad.shape==(72,35) and rad.rank()==35 and GG*rad==s.zeros(72,35)
print('204 independent forms exact; common quotient radical35; full radical546',flush=True)
# Reconstruct minimal active native coefficients independently, not merely
# evaluating the coordinate pivot columns used by the author.
units=[s.Matrix(2,2,lambda r,c:int(r==a and c==b)) for a,b in product(range(2),repeat=2)]
transforms={};native_results=[]
for i in range(4):
 bit=1<<(3-i);reps=[R[i]*local(i,u)*R[i] for u in units]
 for name,P in [('I',I2),('X',X),('Y',Y),('Z',Z)]:
  H=local(i,P)*E[i];kind='imag' if name=='Y' else 'real';Hreal=H/s.I if kind=='imag' else H
  mats=[Hreal*A for A in reps];qvec=s.zeros(72,1)
  for mask in [0,bit]:
   key=f'{mask}_{kind}';basis=s.Matrix(data[key].tolist());n=basis.rows
   if key not in transforms:
    _,cols=s.polys.matrices.DomainMatrix.from_Matrix(basis).convert_to(s.QQ).rref();transforms[key]=(cols,basis[:,list(cols)].T.inv())
   cols,inv=transforms[key];vec=[]
   for f,a,p in product(range(16),repeat=3):
    o=f^mask;row=(a&~bit)|(f&bit);unit=2*int(bool(o&bit))+int(bool(a&bit))
    vec.append(mats[unit][row,p])
   vec=s.Matrix(vec);coords=inv*vec[list(cols),:]
   assert basis.T*coords==vec
   for j,x in enumerate(coords):
    if (mask,kind,j) in lookup:qvec[lookup[mask,kind,j]]=x
  assert all(s.Matrix(B.tolist())*qvec==s.zeros(72,1) for B in allforms)
  saved=json.loads((ROOT/'auxiliary_host_minimal_native_test_checks.json').read_text())
  if name!='I':
   old=next(r for r in saved['results'] if r['query']==i+1 and r['Pauli']==name)
   expected=s.Matrix([s.Rational(old['nonboundary_coordinates'].get(str(j),'0')) for j in range(72)])
   assert qvec==expected
  native_results.append({'query':i+1,'Hermitian_generator':name,'full_coefficients_reconstructed':True,'annihilated_by_all204_forms':True,'quotient_coordinates':{str(j):str(x) for j,x in enumerate(qvec) if x}})
  print('Minimal native',i+1,name,'full coefficients and radical PASS',flush=True)
out={'status':'PASS','basis_sha256':hashlib.sha256((ROOT/'auxiliary_host_compatibility_tangent_basis.npz').read_bytes()).hexdigest(),'full_tangent_dimension':583,'verified_boundary_subspace_dimension':511,'complement_dimension':72,'number_of_independent_forms':204,'sector_ranks':sector_ranks,'common_radical_codimension':37,'full_common_radical_dimension':546,'quotient_radical_dimension':35,'forms':report,'minimal_native_tests':native_results,'boundary_radical_witnesses':{'past_FH':'E=C H, using F†C=C†F','future_HF':'E=H C'},'scope':'Exact necessary mixed obstructions, with no assertion that all possible obstruction forms have been found or that their common isotropic spaces are integrable/routable.'}
(ROOT/'auxiliary_host_all_curvature_independent_audit_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS full-sector audit including minimal native radical compatibility',flush=True)
