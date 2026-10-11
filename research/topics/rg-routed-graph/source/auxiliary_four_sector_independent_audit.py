"""Independent forward-word audit of both four-sector classical auxiliaries."""
from pathlib import Path
from itertools import product
import json
import numpy as np
import sympy as s
from exact_fixtures import E, WORDS, I2, X, local
ROOT=Path(__file__).parent
T=np.zeros((16,16,16),dtype=np.int64)
for r,ow in enumerate(WORDS):
    for a,aw in enumerate(WORDS):
        v=4*s.eye(16)[a,:]-sum((8*E[i][a,:] for i in range(4) if ow[i]!=aw[i]),s.zeros(1,16))
        assert all(x.is_Integer for x in v)
        T[r,a]=[int(x) for x in v]


def local_reduce(r,a,b):
    if r==0:return [(1+2*a+b,1)]
    return ([(0,1)] if a==b else [])+[(1+2*a+b,-1)]


def coeff_normal_terms(r,a,b):
    choices=[local_reduce(WORDS[r][i],WORDS[a][i],WORDS[b][i]) for i in range(4)]
    for term in product(*choices):
        key=0;sg=1
        for digit,sg1 in term:key=5*key+digit;sg*=sg1
        yield key,sg


def evaluate(C,us):
    W=s.kronecker_product(*us)
    return s.Matrix.vstack(*[W[r,:]*s.Matrix(C[r].tolist())/4 for r in range(16)])


reports=[]
for label,party in [('P4',1),('P5',3)]:
    flag=[]
    for n in WORDS:
        flag.append(int(((n[0]==0 and n[3]==0)or(n[0]==1 and n[2]==0)) if label=='P4'
                        else (n[2]==0 or(n[0]==0 and n[1]==1 and n[2]==1))))
    sector=np.array([[2*ow[party]+flag[a] for a in range(16)] for ow in WORDS])
    C=np.array([T*(sector==k)[:,:,None] for k in range(4)])
    assert np.array_equal(np.sum(C,axis=0),T)
    # Every equation C_s^*C_t = delta_st F^*C_t, all at once.
    normal=np.zeros((4,4,625,16,16),dtype=np.int64)
    for r,a,b in product(range(16),repeat=3):
        raw=np.outer(T[r,a],T[r,b]);ss=int(sector[r,a]);tt=int(sector[r,b])
        for key,sign in coeff_normal_terms(r,a,b):
            normal[ss,tt,key]+=sign*raw
            normal[tt,tt,key]-=sign*raw
    assert 4096*2*4*4 < 2**63
    assert not np.any(normal)
    origins=[s.Matrix(16,16,lambda r,p:s.Rational(int(c[r,r,p]),4)) for c in C]
    assert all(q.H==q and q*q==q for q in origins)
    assert all(origins[a]*origins[b]==s.zeros(16) for a in range(4) for b in range(a))
    assert sum(origins,s.zeros(16))==s.eye(16)
    ranks=[q.rank() for q in origins]
    assert ranks==([4,4,4,4] if label=='P4' else [3,5,3,5])
    # The coarse input flag L has rank 8 or 10; the other marginal is a
    # fixed ordinary output flag at party j, coefficientwise.
    L=C[1]+C[3]
    P=s.diag(*flag)
    assert origins[1]+origins[3]==P
    O=[local(party,s.diag(1,0)),local(party,s.diag(0,1))]
    for oo in range(2):
        for r in range(16):
            assert np.array_equal(C[2*oo,r]+C[2*oo+1,r],int(O[oo][r,r])*T[r])
            assert np.array_equal(C[2*oo+1,r],int(O[oo][r,r])*L[r])
    # Coarse flag is not a fixed boundary input/output flag. Find exact
    # Pauli witnesses only for this interpretation, not for completeness.
    witnesses={}
    for choices in product([0,1],repeat=4):
        us=[X if bit else I2 for bit in choices]
        f=evaluate(T,us);l=evaluate(L,us)
        for name,defect in [('past',l-f*P),('future',l-P*f)]:
            if name not in witnesses and defect!=s.zeros(16):
                witnesses[name]={'X_query_indices':[i+1 for i,b in enumerate(choices) if b],
                                 'HS_squared':str(s.trace(defect.H*defect))}
        if len(witnesses)==2:break
    assert len(witnesses)==2
    reports.append({'input_flag':label,'output_query':party+1,
        'sector_order':'(output,input flag)=(0,0),(0,1),(1,0),(1,1)',
        'origin_sector_ranks':ranks,'all_16_cross_identities_checked':True,
        'normal_word_matrix_coefficients_checked':16*625*256,
        'nonzero_coefficients':0,'coarse_input_flag_origin_rank':P.rank(),
        'fixed_future_output_flag_marginal_verified_coefficientwise':True,
        'sector_equals_output_projection_times_input_flag_coefficientwise':True,
        'coarse_flag_not_fixed_boundary_witnesses':witnesses})
    print(label,'PASS, four complete orthogonal sectors:',ranks,flush=True)

(ROOT/'auxiliary_four_sector_independent_audit_checks.json').write_text(json.dumps({
    'status':'PASS','results':reports,
    'scope':'Two separate complete C^4 auxiliary slots; no joint extension of C4 and C5 and no routed-host realization is asserted.'},indent=2)+'\n')
