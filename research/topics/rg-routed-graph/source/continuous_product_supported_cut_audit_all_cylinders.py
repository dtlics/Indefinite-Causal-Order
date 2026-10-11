"""Exact all-context cut classification from a parameter-level cylinder lower bound
and the independently audited finite Pauli upper bound."""
from pathlib import Path
from itertools import product
import json
import sympy as s
from exact_fixtures import E,I16,WORDS,local,X,Y,Z
ROOT=Path(__file__).parent
zero=s.zeros(16)
reference=json.loads((ROOT/'auxiliary_supported_cut_spaces_checks.json').read_text())

def idx(w):return sum(x<<(3-i) for i,x in enumerate(w))
def merge(L,l,R,r):
    w=[0]*4
    for i,x in zip(L,l):w[i]=x
    for i,x in zip(R,r):w[i]=x
    return tuple(w)

out=[]
for before_bits in product(range(2),repeat=4):
    L=[i for i in range(4) if before_bits[i]];R=[i for i in range(4) if not before_bits[i]]
    if not L or not R:continue
    lw=list(product(range(2),repeat=len(L)));rw=list(product(range(2),repeat=len(R)))
    H=s.zeros(len(rw))
    for j in R:
        for p,a in enumerate(rw):
            for q,b in enumerate(rw):
                H[p,q]+=sum(E[j][idx(merge(L,l,R,a)),idx(merge(L,l,R,b))] for l in lw)
    ns=H.nullspace()
    if ns:
        B=s.Matrix.hstack(*ns);q=B*(B.H*B).inv()*B.H
    else:q=s.zeros(len(rw))
    Q=s.zeros(16)
    for p,a in enumerate(WORDS):
        for k,b in enumerate(WORDS):
            if all(a[i]==b[i] for i in L):
                ar=sum(a[i]<<(len(R)-1-z) for z,i in enumerate(R))
                br=sum(b[i]<<(len(R)-1-z) for z,i in enumerate(R))
                Q[p,k]=q[ar,br]
    assert Q==Q.H and Q*Q==Q
    assert all(E[j]*Q==zero for j in R)
    assert all(Q*local(i,p)==local(i,p)*Q for i in L for p in [X,Y,Z])
    r=next(x for x in reference if x['before_queries']==[i+1 for i in L])
    assert Q.rank()==r['pauli_cut_dimension']
    if Q.rank():
        K=s.Matrix.hstack(*[s.Matrix([s.sympify(x) for x in col]) for col in r['basis']])
        assert Q*K==K
    out.append({'before_queries':[i+1 for i in L],'after_queries':[i+1 for i in R],
                'exact_all_context_cut_dimension':Q.rank(),
                'after_carrier_basis':[[str(x) for x in v] for v in ns],
                'after_carrier_factor_order':[i+1 for i in R],
                'upper_and_parameter_lower_bounds_match':True})
report={'status':'PASS','parameter_lower_bound':'Q_L is the largest physical L-cylinder annihilated by every E_j for j in R; the cylinder cut lemma proves Q_L is inside the all-context cut space',
        'finite_upper_bound':'Independently audited exhaustive Pauli constraints',
        'result':'For every one of the fourteen proper partitions, these lower and upper spaces coincide exactly',
        'cuts':out,
        'endpoint_cuts':'Both empty-before and empty-after cut spaces are all of C16',
        'scope':'Exact fixed cut subspaces, not routed-host realizations; the theorem only constrains multiplicity-one auxiliary blocks'}
(ROOT/'continuous_product_supported_cut_audit_all_cylinders_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
