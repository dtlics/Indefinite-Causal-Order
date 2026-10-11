"""Independent exact coverage audit of the204 curvature common zero locus.

Verify descent and RREF, then certify the six initial spaces and final four
by recursive necessary-factor covers. Each discarded node is contained in
an already verified target space; every other node branches on an exact
real or complex product of equations. No numerical rank or random point is
used to establish coverage or maximality.
"""
from pathlib import Path
from itertools import product
from collections import Counter
import json,time
import sympy as s
ROOT=Path(__file__).parent;start=time.time()
source=json.loads((ROOT/'auxiliary_host_all_curvature_exact_checks.json').read_text())
quot=json.loads((ROOT/'auxiliary_host_all_curvature_quotient_checks.json').read_text())
rrefsource=json.loads((ROOT/'auxiliary_host_all_curvature_rref_checks.json').read_text())
L=s.Matrix([[s.Rational(x) for x in row] for row in quot['coordinate_rows']]);piv=quot['pivot_coordinates'];n=37
assert L.shape==(37,72) and L.rank()==37 and L[:,piv]==s.eye(37)
Bs=[]
for rec in source['forms']:
 B=s.zeros(72)
 for entry in rec['bilinear_entries']:
  i,j=entry['coordinates'];B[i,j]=B[j,i]=entry['value']
 A=B.extract(piv,piv);assert B==L.T*A*L;Bs.append(A)
mon=[(i,j) for i in range(n) for j in range(i,n)]
CO=s.Matrix([[B[i,j]*(1 if i==j else 2) for i,j in mon] for B in Bs]);RR,pp=CO.rref();assert len(pp)==204
saved=s.Matrix([[s.Rational(rec['terms'].get(str(j),'0')) for j in range(len(mon))] for rec in rrefsource['forms']])
assert RR==saved and rrefsource['monomials']==[list(x) for x in mon]
y=s.symbols('y0:37',real=True)
polys=[s.Poly(sum(RR[k,j]*y[a]*y[b] for j,(a,b) in enumerate(mon) if RR[k,j]),*y).as_expr() for k in range(204)]
def normalized_coeffs(poly,vs,mons):
 P=s.Poly(poly,*vs);v=tuple(P.coeff_monomial(vs[i]*vs[j]) for i,j in mons);first=next(x for x in v if x);return tuple(x/first for x in v)
factorized=[];irreducible=[]
for k,q in enumerate(polys):
 coeff,factors=s.factor_list(q)
 assert s.expand(coeff*s.prod(f**m for f,m in factors)-q)==0
 if all(s.Poly(f,*y).total_degree()==1 for f,m in factors):factorized.append(k)
 else:irreducible.append(k)
assert len(factorized)==183 and len(irreducible)==21
fg=json.loads((ROOT/'auxiliary_host_rank_two_factor_graph.json').read_text());vectors=[s.Matrix(1,n,[s.Rational(x) for x in row]) for row in fg['vectors']]
graphpolys=[s.expand((vectors[a]*s.Matrix(y))[0]*(vectors[b]*s.Matrix(y))[0]) for a,b in fg['pairs']]
assert Counter(normalized_coeffs(q,y,mon) for q in graphpolys)==Counter(normalized_coeffs(polys[k],y,mon) for k in factorized)
print('Exact37-coordinate descent,204-row RREF,183 products and21 remaining quadrics',flush=True)

def canon(M):
 rr,p=M.rref();return tuple(tuple(rr[i,:]) for i in range(len(p)))
def mat(key):return s.Matrix(key) if key else s.zeros(0,n)
def reduced(row,key):
 v=list(row)
 for r in key:
  k=next(j for j,x in enumerate(r) if x)
  if v[k]:
   z=v[k];v=[a-z*b for a,b in zip(v,r)]
 return tuple(v)
def contained(key,target):return all(not any(reduced(row,key)) for row in target)
def readspaces(fname,key):
 return [canon(s.Matrix([[s.Rational(x) for x in row] for row in rec['rows']])) for rec in json.loads((ROOT/fname).read_text())[key]]
initial=readspaces('auxiliary_host_rank_two_components_checks.json','components')
final=readspaces('auxiliary_host_all_curvature_components_checks.json','finished')
for key in initial:
 N=s.Matrix.hstack(*mat(key).nullspace())
 for a,b in fg['pairs']:
  assert vectors[a]*N==s.zeros(1,N.cols) or vectors[b]*N==s.zeros(1,N.cols)
for key in final:
 N=s.Matrix.hstack(*mat(key).nullspace())
 assert all(N.T*B*N==s.zeros(N.cols) for B in Bs)
assert len(final)==4
assert all(not contained(a,b) for i,a in enumerate(final) for j,b in enumerate(final) if i!=j)

# An independent depth-first certificate that the183 product equations are
# covered by the six saved spaces. Use graph-edge branching, not the author's
# iterative candidate-space enumeration and pruning procedure.
freq=Counter(i for pair in fg['pairs'] for i in pair)
edges=sorted(fg['pairs'],key=lambda ab:(-(freq[ab[0]]+freq[ab[1]]),ab))
seen=set();stack=[()];initial_nodes=0;initial_leaves=Counter();initial_branch_records=[]
while stack:
 key=stack.pop()
 if key in seen:continue
 seen.add(key);initial_nodes+=1
 targets=[j for j,t in enumerate(initial) if contained(key,t)]
 if targets:initial_leaves[targets[0]]+=1;continue
 pair=next(((a,b) for a,b in edges if any(reduced(tuple(vectors[a]),key)) and any(reduced(tuple(vectors[b]),key))),None)
 assert pair is not None,('Initial cover missed a solution space',key)
 children=[]
 for index in pair:
  child=canon(mat(key).col_join(vectors[index]));assert len(child)>len(key);children.append(child);stack.append(child)
 initial_branch_records.append({'codimension':len(key),'factor_pair':list(pair),'child_codimensions':[len(k) for k in children]})
print('Six-space product coverage certified with',initial_nodes,'distinct nodes',flush=True)

# Certify final coverage using necessary factorizations on each restricted
# space. Real symbols avoid the author's manual re()/im() substitution. We
# also try a single real equation over Q(i) before pairing two equations.
seen=set();stack=list(initial);counts=Counter();branch_records=[];leaves=Counter()
while stack:
 key=stack.pop()
 if key in seen:continue
 seen.add(key);M=mat(key);targets=[j for j,t in enumerate(final) if contained(key,t)]
 if targets:leaves[targets[0]]+=1;continue
 N=s.Matrix.hstack(*M.nullspace());d=N.cols
 restricted=[N.T*B*N for B in Bs];nonzero=[B for B in restricted if B!=s.zeros(d)]
 assert nonzero,('Final cover missed an entire solution space',key)
 mons=[(i,j) for i in range(d) for j in range(i,d)]
 rows=s.Matrix([[B[i,j]*(1 if i==j else 2) for i,j in mons] for B in nonzero]);rr,pp=rows.rref()
 z=s.symbols('z0:'+str(d),real=True)
 qs=[sum(rr[k,c]*z[i]*z[j] for c,(i,j) in enumerate(mons) if rr[k,c]) for k in range(len(pp))]
 found=None;mode=None;selected=None;factored=None
 for qi,q in enumerate(qs):
  coefficient,factors=s.factor_list(q)
  if factors and all(s.Poly(f,*z).total_degree()==1 for f,m in factors):
   found=[[f] for f,m in factors];mode='real';selected=[qi];factored=q;break
 if found is None:
  for qi,q in enumerate(qs):
   coefficient,factors=s.factor_list(q,extension=s.I)
   if factors and all(s.Poly(f,*z).total_degree()==1 for f,m in factors):
    found=[[s.expand(s.re(f)),s.expand(s.im(f))] for f,m in factors];mode='complex_single';selected=[qi];factored=q;break
 if found is None:
  for qi in range(len(qs)):
   for qj in range(qi+1,len(qs)):
    q=qs[qi]+s.I*qs[qj];coefficient,factors=s.factor_list(q,extension=s.I)
    if factors and all(s.Poly(f,*z).total_degree()==1 for f,m in factors):
     found=[[s.expand(s.re(f)),s.expand(s.im(f))] for f,m in factors];mode='complex_pair';selected=[qi,qj];factored=q;break
   if found is not None:break
 assert found is not None,('No exact factor branch found',len(key),d)
 assert s.expand(coefficient*s.prod(f**m for f,m in factors)-factored)==0
 free=[i for i in range(n) if i not in M.rref()[1]]
 assert N.extract(free,list(range(d)))==s.eye(d)
 children=[]
 for group in found:
  added=[]
  for f in group:
   if f==0:continue
   coeffs=[s.expand(f).coeff(v) for v in z];assert s.expand(f-sum(c*v for c,v in zip(coeffs,z)))==0
   row=s.zeros(1,n)
   for k,c in zip(free,coeffs):row[k]=c
   added.append(row)
  assert added
  child=canon(M.col_join(s.Matrix.vstack(*added)));assert len(child)>len(key);children.append(child);stack.append(child)
 counts[mode]+=1
 branch_records.append({'parent_codimension':len(key),'free_dimension':d,'mode':mode,'selected_restricted_RREF_equations':selected,'factored_polynomial':str(factored),'factorization_coefficient':str(coefficient),'factors':[[str(f),m] for f,m in factors],'real_child_constraints':[[str(f) for f in group if f!=0] for group in found],'child_codimensions':[len(c) for c in children]})
print('Four-space coverage:',len(seen),'nodes, branches',dict(counts),'leaves',dict(leaves),flush=True)
# Match the refined spaces to the old eight-coordinate alternatives.
olddefs=[{167:1},{168:8,169:1},{164:3,165:-1,168:-1,170:1},{161:1,162:-1,164:-2,170:-2},{163:1,168:-8,170:-8},{159:1,160:-1,161:-1,162:1},{160:1,162:-1},{151:2,153:-2,164:-1,165:-1,168:1,170:-1}]
old=s.zeros(8,72)
for j,lab in enumerate(source['coordinate_labels']):
 if lab['mask']==0 and lab['kind']=='real':
  for k,dct in enumerate(olddefs):old[k,j]=dct.get(lab['typed_basis_index'],0)
oldactive=old[:,piv];assert old==oldactive*L
components=[]
for key in final:
 N=s.Matrix.hstack(*mat(key).nullspace());image=oldactive*N
 label=''.join(chr(97+i) for i in range(8) if any(image[i,j] for j in range(image.cols)))
 components.append({'old_class':label,'codimension':len(key),'full_tangent_dimension':583-len(key),'all204_forms_vanish_identically':True})
assert {r['old_class']:r['full_tangent_dimension'] for r in components}=={'ah':556,'bh':556,'dfgh':568,'cdefg':570}
out={'status':'PASS','exact_quotient_dimension':37,'exact_form_space_dimension':204,'real_product_equations':183,'remaining_RREF_quadrics':21,'initial_cover_nodes':initial_nodes,'initial_cover_branch_steps':initial_branch_records,'final_cover_nodes':len(seen),'final_branch_counts':dict(counts),'final_cover_branch_steps':branch_records,'final_components':components,'pairwise_noncontainment':True,'common_radical_dimension':546,'scope':'The common zero locus of these204 necessary quadratic forms is exactly the union of the four listed real linear spaces. This classifies simultaneous isotropic linear spans for this form family, not auxiliary C*-algebras or routed hosts.'}
(ROOT/'auxiliary_host_all_components_independent_audit_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: exact coverage, bilinear vanishing, maximality and four refined dimensions',flush=True)
