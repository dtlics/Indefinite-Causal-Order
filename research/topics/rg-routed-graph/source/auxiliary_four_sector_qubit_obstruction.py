"""Independent necessary-row and origin-space obstruction to every P4 qubit lift."""
from pathlib import Path
from itertools import product
import json
import numpy as np
import sympy as s
from phase_endpoint_exact import row_tensor, WORDS
ROOT=Path(__file__).parent
p=1000003
assert s.isprime(p)
T=row_tensor(4,1)
flag=np.array([int((n[0]==0 and n[3]==0)or(n[0]==1 and n[2]==0)) for n in WORDS])
TZ=T*(2*flag[None,:,None]-1)


def reduce_local(r,a,t,b):
    if r!=t:return [(4*r+2*a+b,1)]
    if r==0:return [(1+2*a+b,1)]
    return [(1+2*a+b,-1)]+([(0,1)] if a==b else [])


inv={}
for delta in [0,1]:
    inv[delta]=[[] for _ in range(8 if delta else 5)]
    for r,a,t,b in product(range(2),repeat=4):
        if r^t != delta:continue
        for key,sg in reduce_local(r,a,t,b):inv[delta][key].append((r,a,t,b,sg))
raw_cache={}


def raw_terms(mask,key):
    if (mask,tuple(key)) not in raw_cache:
        out=[]
        for terms in product(*[inv[(mask>>(3-i))&1][key[i]] for i in range(4)]):
            r=a=t=b=0;sg=1
            for rr,aa,tt,bb,sign in terms:
                r=2*r+rr;a=2*a+aa;t=2*t+tt;b=2*b+bb;sg*=sign
            out.append((r,a,t,b,sg))
        raw_cache[mask,tuple(key)]=out
    return raw_cache[mask,tuple(key)]


def row(A,mask,kind,rec,anti=False):
    key,pp,qq=rec;parity=-1 if kind=='real' else 1
    if anti:parity=-parity
    ans={}
    for r,a,t,b,sg in raw_terms(mask,key):
        j=(r*16+b)*16+qq;k=(t*16+a)*16+pp
        ans[j]=ans.get(j,0)+sg*int(A[r,a,pp])
        ans[k]=ans.get(k,0)+sg*parity*int(A[t,b,qq])
    return {j:v for j,v in ans.items() if v}


def insert(row,piv):
    row={j:v%p for j,v in row.items() if v%p}
    while row:
        k=min(row);v=row[k]
        if k not in piv:
            vi=pow(v,-1,p);piv[k]={j:x*vi%p for j,x in row.items()};return True
        for j,x in piv[k].items():
            y=(row.get(j,0)-v*x)%p
            if y:row[j]=y
            elif j in row:del row[j]
    return False


directions=json.loads((ROOT/'auxiliary_input_flag_anticommutant_basis_checks.json').read_text())['directions']
upper=json.loads((ROOT/'auxiliary_input_flag_quantum_lift_scout_checks.json').read_text())['blocks']
rank_records=[]
for rec in upper:
    m=rec['mask'];kind=rec['kind'];piv={}
    dirs=[d for d in directions if d['mask']==m and d['kind']==kind]
    candidate=[]
    for d in dirs:
        v=np.zeros(4096,dtype=np.int64)
        for k,x in d['integer_coefficients'].items():v[int(k)]=x
        candidate.append(v)
    def check_and_insert(rr):
        for v in candidate:
            assert sum(int(v[j])*x for j,x in rr.items())==0
        assert insert(rr,piv)
    old=json.loads((ROOT/f'auxiliary_tangent_output_block_{m}_{kind}.json').read_text())
    for r0 in old['rows']:check_and_insert(row(T,m,kind,r0))
    for r0 in rec['added_rows']:check_and_insert(row(TZ,m,kind,r0,True))
    assert len(piv)==rec['joint_rank_lower_bound']
    assert len(dirs)==4096-len(piv)
    if dirs:
        assert s.Matrix(np.stack(candidate,axis=1).tolist()).rank()==len(dirs)
    rank_records.append({'mask':m,'kind':kind,'independent_rank':len(piv),
                         'exact_selected_constraint_nullity':len(dirs),
                         'rational_candidates_annihilate_every_selected_row':True})
    print('Necessary rows verified',m,kind,'nullity',len(dirs),flush=True)
assert sum(r['exact_selected_constraint_nullity'] for r in rank_records)==22

plus=[i for i in range(16) if flag[i]];minus=[i for i in range(16) if not flag[i]]
spaces={'real':[],'imag':[]};origins=[]
for d in directions:
    A=s.zeros(16)
    for k,x in d['integer_coefficients'].items():
        r,aa=divmod(int(k),256);a,q=divmod(aa,16)
        if a==(r^d['mask']):A[r,q]=s.Rational(x,d['denominator'])
    H=A*(s.I if d['kind']=='imag' else 1)
    assert H==H.H
    Z=s.diag(*[2*int(x)-1 for x in flag])
    assert H*Z+Z*H==s.zeros(16)
    origins.append(H)
    spaces[d['kind']].append(A.extract(plus,minus).reshape(64,1))
V={kind:s.Matrix.hstack(*cols) for kind,cols in spaces.items()}
assert V['real'].rank()==11 and V['imag'].rank()==11
assert V['real'].row_join(V['imag']).rank()==15
joint_kernel=s.Matrix.hstack(*V['real'].row_join(-V['imag']).nullspace())
W=V['real']*joint_kernel[:11,:]
assert W.rank()==7
rr,piv=W.T.rref();canonical=[s.Matrix(8,8,rr[i,:]) for i in range(len(piv))]
assert len(canonical)==7
fixed_column=minus.index(5)
assert all(B[:,fixed_column]==s.zeros(8,1) for B in canonical)
origin_rank=s.Matrix.hstack(*[H.reshape(256,1) for H in origins]).rank()
assert origin_rank==22
report={'status':'PASS','necessary_real_coefficient_space_dimension':22,
        'origin_evaluation_rank':origin_rank,'rank_checks':rank_records,
        'positive_origin_indices':plus,'negative_origin_indices':minus,
        'real_offdiagonal_space_rank':11,'imaginary_offdiagonal_space_rank':11,
        'combined_offdiagonal_real_space_rank':15,'intersection_rank':7,
        'intersection_basis':[[[str(x) for x in row] for row in B.tolist()] for B in canonical],
        'intersection_common_zero_column_boundary_index':5,
        'conclusion':'No full unital M2 auxiliary can have the prescribed coarse P4 input-flag coefficient: both Pauli X and Y would belong to the necessary space, their origin Pauli relation forces their upper-right blocks into the seven-dimensional intersection, and every such X kills |0101>, contradicting X^2=I.',
        'scope':'Fixed coarse P4 marginal on the original boundary; no general repeated-multiplicity or routed-host theorem.'}
(ROOT/'auxiliary_four_sector_qubit_obstruction_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS: the full P4 qubit lift is impossible already from simultaneous origin X/Y constraints.',flush=True)
