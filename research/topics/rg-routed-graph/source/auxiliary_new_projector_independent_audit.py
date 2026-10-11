"""Independent full-word audit of the rank-four and rank-five C direct-sum C extensions."""
from pathlib import Path
from itertools import product
import json
import numpy as np
import sympy as s
from exact_fixtures import E,I16,I2,X,Y,Z,R,WORDS,tensor,local
ROOT=Path(__file__).parent
D=json.loads((ROOT/'auxiliary_tangent_extra_directions.json').read_text())['directions']
T=np.zeros((16,16,16),dtype=np.int64)
for o,ow in enumerate(WORDS):
    for a,aw in enumerate(WORDS):
        v=4*s.eye(16)[a,:]-sum((8*E[i][a,:] for i in range(4) if ow[i]!=aw[i]),s.zeros(1,16))
        assert all(x.is_Integer for x in v)
        T[o,a]=[int(x) for x in v]

def local_reduce(r,a,b):
    if r==0:return [(1+2*a+b,1)]
    return ([(0,1)] if a==b else [])+[(1+2*a+b,-1)]

cuts=json.loads((ROOT/'continuous_product_supported_cut_audit_all_cylinders_checks.json').read_text())['cuts']
def basis(L):
    rec=next(x for x in cuts if x['before_queries']==[i+1 for i in L])
    rr=[i for i in range(4) if i not in L];cols=[]
    for left in product(range(2),repeat=len(L)):
        for sv in rec['after_carrier_basis']:
            v=s.Matrix([s.sympify(x) for x in sv]);col=s.zeros(16,1)
            for right in product(range(2),repeat=len(rr)):
                w=[0]*4
                for i,b in zip(L,left):w[i]=b
                for i,b in zip(rr,right):w[i]=b
                n=sum(b<<(3-i) for i,b in enumerate(w));a=sum(b<<(len(rr)-1-i) for i,b in enumerate(right))
                col[n]=v[a]
            cols.append(col)
    return s.Matrix.hstack(*cols)
Bs=[basis([i]) for i in range(4)]+[basis([0,1])]
Qs=[B*(B.H*B).inv()*B.H for B in Bs]

def evaluate(C,den,us):
    W=tensor(us)
    return s.Matrix.vstack(*[W[r,:]*s.Matrix(C[r].tolist())/den for r in range(16)]).applyfunc(s.expand)

tests=[];candidate_vectors=[]
for k,scale,sg,rank in [(0,4,1,4),(6,1,-1,5)]:
    d=D[k];assert d['mask']==0 and d['kind']=='real'
    den=d['denominator']*scale;C=np.zeros((16,16,16),dtype=np.int64)
    for j,v in d['integer_coefficients'].items():
        r,t=divmod(int(j),256);a,p=divmod(t,16);C[r,a,p]=sg*v
    # Full raw-word forward reduction of the quadratic projector defect.
    normal=np.zeros((625,16,16),dtype=np.int64)
    bound=16*(4*int(np.max(np.abs(C)))**2+den*4*int(np.max(np.abs(C))))
    assert bound<2**63
    for r,a,b in product(range(16),repeat=3):
        raw=4*np.outer(C[r,a],C[r,b])-den*np.outer(T[r,a],C[r,b])
        if not np.any(raw):continue
        choices=[local_reduce(WORDS[r][i],WORDS[a][i],WORDS[b][i]) for i in range(4)]
        for term in product(*choices):
            key=0;sign=1
            for digit,sign1 in term:key=5*key+digit;sign*=sign1
            normal[key]+=sign*raw
    assert not np.any(normal)
    assert np.max(np.abs(normal))<=bound
    # Verify every coefficient of the claimed laboratory-input/output mask.
    for r,a in product(range(16),repeat=2):
        o,n=WORDS[r],WORDS[a]
        if rank==4:mask=int(o[1]==0 and ((n[0]==0 and n[3]==0) or (n[0]==1 and n[2]==0)))
        else:mask=int(o[3]==0 and (n[2]==0 or (n[0]==0 and n[1]==1 and n[2]==1)))
        assert np.array_equal(4*C[r,a],den*mask*T[r,a])
    origin=s.Matrix(16,16,lambda r,p:s.Rational(int(C[r,r,p]),den))
    assert origin.H==origin and origin*origin==origin and origin.rank()==rank
    # No proper cut can support this same origin projection.
    eligible=[i for i,Q in enumerate(Qs) if Q*origin==origin]
    assert not eligible
    # Both endpoint coefficient forms fail on actual Pauli unitary contexts.
    endpoint_witnesses={}
    for choice in product(range(4),repeat=4):
        if len(endpoint_witnesses)==2:break
        us=[[I2,X,Y,Z][i] for i in choice]
        f=evaluate(T,4,us);c=evaluate(C,den,us)
        for name,defect in [('past',c-f*origin),('future',c-origin*f)]:
            if name not in endpoint_witnesses and defect!=s.zeros(16):
                norm=s.expand(s.trace(defect.H*defect))
                assert norm>0
                endpoint_witnesses[name]={'Pauli_indices':list(choice),'defect_HS_squared':str(norm)}
    assert len(endpoint_witnesses)==2
    tests.append({'rank':rank,'direction':k,'rescaling':str(s.Rational(sg,scale)),
                  'all_quadratic_normal_word_coefficients_checked':625*256,
                  'projector_defect_coefficients':0,'integer_intermediate_bound':bound,
                  'closed_laboratory_mask_verified_coefficientwise':True,
                  'origin_support_indices':[i for i in range(16) if origin[i,i]],
                  'fits_any_proper_cut_carrier':False,
                  'endpoint_promotion_witnesses':endpoint_witnesses})
    assert den==4
    candidate_vectors.append(C.reshape(4096))
    print('Complete projector and promotion audit PASS, rank',rank,flush=True)

(ROOT/'auxiliary_new_projector_independent_audit_checks.json').write_text(json.dumps({'status':'PASS','tests':tests,
    'meaning':'Together with independently audited complete Hermiticity, these prove actual independently complete C direct-sum C auxiliary extensions with multiplicities (4,12) and (5,11)',
    'same_coefficient_full_matrix_promotion':'Impossible by the audited multiplicity-one cut theorem, proper-carrier exclusion, and explicit endpoint witnesses',
    'novelty_membership':'Separate exact-rank computation follows; not needed for validity or promotion obstruction',
    'scope':'Process-tensor extensions only; no routed realization'},indent=2)+'\n')

# Exact characteristic-zero dimension of the constructive XOR-zero real block.
# Uniformly use integer coefficient vectors 4C; the independent carrier bases are integral.
vectors=[]
def addv(v):
    v=np.asarray(v,dtype=np.int64).reshape(4096)
    if np.any(v):vectors.append(v)
def real_generators(n):
    for i in range(n):
        H=s.zeros(n);H[i,i]=1;yield H
    for i in range(n):
        for j in range(i+1,n):
            H=s.zeros(n);H[i,j]=H[j,i]=1;yield H

def intmat(M):
    assert all(x.is_Integer for x in M)
    return np.array(M.tolist(),dtype=np.int64)
for H in real_generators(16):
    h=intmat(H)
    addv(np.array([T[r]@h for r in range(16)]))
    addv(np.array([int(h[r,r])*T[r] for r in range(16)]))
units=[s.Matrix(2,2,lambda r,c:int(r==a and c==b)) for a,b in product(range(2),repeat=2)]
for i,B in enumerate(Bs[:4]):
    reps=[intmat(4*R[i]*local(i,u)*R[i]) for u in units];bit=1<<(3-i)
    for H in real_generators(B.cols):
        h=intmat(B*H*B.H);mats=[h@a for a in reps]
        v=np.zeros((16,16,16),dtype=np.int64)
        for r,n in product(range(16),repeat=2):
            t=(n&~bit)|(r&bit)
            v[r,n]=mats[2*((r&bit)>0)+((n&bit)>0)][t]
        addv(v)
left={}
for o,n in product(range(4),repeat=2):
    mat=np.zeros((16,16),dtype=np.int64)
    for r in range(4):mat[4*o+r]=T[4*o+r,4*n+r]
    left[o,n]=mat
for H in real_generators(Bs[4].cols):
    h=intmat(Bs[4]*H*Bs[4].H);mats={key:h@mat for key,mat in left.items()}
    v=np.zeros((16,16,16),dtype=np.int64)
    for r,n in product(range(16),repeat=2):v[r,n]=mats[r//4,n//4][4*(r//4)+n%4]
    addv(v)
for i in range(4):
    bit=1<<(3-i)
    for H in real_generators(2):
        h=intmat(H)
        pre=np.zeros((16,16,16),dtype=np.int64);post=pre.copy()
        for r,n in product(range(16),repeat=2):
            ni=int(bool(n&bit));ri=int(bool(r&bit))
            pre[r,n]=sum((int(h[ni,a])*T[r,(n&~bit)|(a*bit)] for a in range(2)),np.zeros(16,dtype=np.int64))
            post[r,n]=int(h[ri,ri])*T[r,n]
        addv(pre);addv(post)
mat=s.Matrix(np.stack(vectors,axis=1))
dm=s.polys.matrices.DomainMatrix.from_Matrix(mat).convert_to(s.QQ)
rank=dm.rank();assert rank==168
print('Constructive XOR-zero real rank over Q is exactly 168.',flush=True)
# Exact rational augmented ranks, so no characteristic-drop inference is needed.
augmented=[]
for v in candidate_vectors:
    rr=s.polys.matrices.DomainMatrix.from_Matrix(mat.row_join(s.Matrix(v.tolist()))).convert_to(s.QQ).rank()
    assert rr==169
    augmented.append(rr)
both=s.polys.matrices.DomainMatrix.from_Matrix(mat.row_join(s.Matrix(np.stack(candidate_vectors,axis=1)))).convert_to(s.QQ).rank()
assert both>=169
(ROOT/'auxiliary_new_projector_independent_membership_checks.json').write_text(json.dumps({'status':'PASS',
    'constructive_XOR_zero_real_rank_over_Q':168,'generator_count':len(vectors),
    'individual_augmented_ranks_over_Q':augmented,'both_augmented_rank_over_Q':both,
    'conclusion':'Each projector lies outside the full boundary/cut/physical-query-local span over R; the family is XOR graded, and both candidates lie in its zero-real block',
    'scope':'Linear coefficient-span non-membership, not a routed obstruction'},indent=2)+'\n')
print('Exact characteristic-zero projector non-membership PASS.',flush=True)
