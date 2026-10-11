"""Exact maximal linear alternatives imposed simultaneously by thirteen forms."""
from pathlib import Path
from itertools import product
import json
import sympy as s
ROOT=Path(__file__).parent
source=json.loads((ROOT/'auxiliary_host_curvature_exact_checks.json').read_text())
factors=[next(x for x in rec['forms'] if x['rank'])['linear_factors'] for rec in source['forms']]
active=sorted({int(k) for pair in factors for d in pair for k in d})
vs=[[s.Matrix(1,len(active),[s.Rational(d.get(str(i),'0')) for i in active]) for d in pair] for pair in factors]
def canon(M):
    A,piv=M.rref();return tuple(tuple(A[i,:]) for i in range(len(piv)))
def matrix(key):return s.Matrix(key) if key else s.zeros(0,len(active))
def span_contains(A,B):
    # Row(A) contains Row(B).
    MA,MB=matrix(A),matrix(B)
    return MA.col_join(MB).rank()==len(A)
components=[()]
for k,pair in enumerate(vs):
    candidates=set()
    for key in components:
        M=matrix(key)
        for v in pair:candidates.add(canon(M.col_join(v)))
    ordered=sorted(candidates,key=lambda key:(len(key),str(key)))
    components=[]
    for key in ordered:
        if not any(span_contains(key,small) for small in components):components.append(key)
    print('Forms',k+1,'maximal components',len(components),'codims',[len(x) for x in components],flush=True)
allfactor=s.Matrix.vstack(*[x for pair in vs for x in pair]);radicalcodim=allfactor.rank()
assert radicalcodim==8
records=[]
for key in components:
    M=matrix(key);ns=M.nullspace();K=s.Matrix.hstack(*ns)
    # Verify every complete bilinear form, not only its diagonal quadratic.
    for a,b in vs:
        assert a*K==s.zeros(1,K.cols) or b*K==s.zeros(1,K.cols)
    records.append({'codimension_in_full_tangent':M.rows,'dimension_in_full_tangent':583-M.rows,'constraint_rows':[[str(x) for x in row] for row in M.tolist()]})
out={'status':'EXACT_LINEAR_ALTERNATIVES','full_tangent_dimension':583,'active_basis_coordinate_indices':active,'common_radical_codimension':radicalcodim,'common_radical_dimension':583-radicalcodim,'maximal_simultaneously_isotropic_linear_components':records,'scope':'Every full auxiliary tangent span of any one host lies in one listed linear subspace. These are necessary conditions only and do not classify full auxiliary C*-algebras.'}
(ROOT/'auxiliary_host_curvature_alternatives_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
