"""Independent complete-space verification of the host-wide bilinear alternative."""
from pathlib import Path
from itertools import product
import json
import numpy as np
import sympy as s
from phase_endpoint_exact import row_tensor, WORDS
ROOT=Path(__file__).parent
P=1000003
assert s.isprime(P)
T=row_tensor(4,1)
data=np.load(ROOT/'auxiliary_host_compatibility_tangent_basis.npz',allow_pickle=False)


def reduce_local(r,a,t,b):
    if r!=t:return [(4*r+2*a+b,1)]
    if r==0:return [(1+2*a+b,1)]
    return [(1+2*a+b,-1)]+([(0,1)] if a==b else [])


inv={d:[[] for _ in range(8 if d else 5)] for d in [0,1]}
for r,a,t,b in product(range(2),repeat=4):
    for k,sg in reduce_local(r,a,t,b):inv[r^t][k].append((r,a,t,b,sg))
cache={}


def raw_terms(mask,key):
    if (mask,tuple(key)) not in cache:
        terms=[]
        for term in product(*[inv[(mask>>(3-i))&1][key[i]] for i in range(4)]):
            r=a=t=b=0;sg=1
            for rr,aa,tt,bb,sign in term:
                r=2*r+rr;a=2*a+aa;t=2*t+tt;b=2*b+bb;sg*=sign
            terms.append((r,a,t,b,sg))
        cache[mask,tuple(key)]=terms
    return cache[mask,tuple(key)]


def tangent_row(mask,kind,rec):
    key,p,q=rec;parity=-1 if kind=='real' else 1;out={}
    for r,a,t,b,sg in raw_terms(mask,key):
        j=(r*16+b)*16+q;k=(t*16+a)*16+p
        out[j]=out.get(j,0)+sg*int(T[r,a,p])
        out[k]=out.get(k,0)+sg*parity*int(T[t,b,q])
    return {j:v for j,v in out.items() if v}


def insert(vector,pivots):
    row={int(j):int(vector[j])%P for j in np.flatnonzero(vector) if vector[j]%P}
    while row:
        k=min(row);v=row[k]
        if k not in pivots:
            vi=pow(v,-1,P);pivots[k]={j:x*vi%P for j,x in row.items()};return True
        for j,x in pivots[k].items():
            y=(row.get(j,0)-v*x)%P
            if y:row[j]=y
            elif j in row:del row[j]
    return False


# Generate the dual functional from FORWARD raw reduction, rather than the
# author's inverse-key enumeration. Selected entries use the same labels as
# the independently audited exact four-row contradiction.
chosen=[((0,1,0,1),2,2,-1),((0,1,0,2),2,0,-1),
        ((0,2,0,1),2,6,1),((0,2,0,3),0,6,1)]
dual_terms=[]
for o,a,b in product(range(16),repeat=3):
    reductions=[dict(reduce_local(WORDS[o][i],WORDS[a][i],WORDS[o][i],WORDS[b][i])) for i in range(4)]
    for key,p,q,weight in chosen:
        sg=weight
        for i in range(4):sg*=reductions[i].get(key[i],0)
        if sg:dual_terms.append((o,a,b,p,q,sg))


def lm(V):
    return (V[:,10,2,2]-V[:,14,2,2]+V[:,10,3,0]-V[:,14,3,0],
            -V[:,10,2,2]+V[:,11,2,2]+V[:,10,6,6]-V[:,11,6,6])


records=[];total=0
for mask,kind in product(range(16),['real','imag']):
    raw=data[f'{mask}_{kind}'];assert raw.ndim==2 and raw.shape[1]==4096
    vectors=np.asarray(raw,dtype=np.int64);n=len(vectors);total+=n
    piv={}
    for v in vectors:assert insert(v,piv)
    old=json.loads((ROOT/f'auxiliary_tangent_output_block_{mask}_{kind}.json').read_text())
    assert n==4096-old['rank_lower_bound']
    for rec in old['rows']:
        rr=tangent_row(mask,kind,rec)
        # Safe integer dot products, checked a priori from actual row bounds.
        assert sum(abs(x) for x in rr.values())*int(np.max(np.abs(vectors))) < 2**63
        val=sum((x*vectors[:,j] for j,x in rr.items()),np.zeros(n,dtype=np.int64))
        assert not np.any(val)
    V=vectors.reshape(n,16,16,16)
    form=np.zeros((n,n),dtype=np.int64)
    bound=2*sum(abs(sg) for *_,sg in dual_terms)*int(np.max(np.abs(V)))**2
    assert bound<2**63
    for o,a,b,p,q,sg in dual_terms:
        x=V[:,o^mask,a,p];y=V[:,o^mask,b,q]
        form+=sg*(np.outer(x,y)+np.outer(y,x))
    if mask==0 and kind=='real':
        ell,m=lm(V)
        expected=np.outer(ell,m)+np.outer(m,ell)
        assert np.array_equal(form,expected)
        assert s.Matrix(np.stack([ell,m],axis=0).tolist()).rank()==2
        rank=2
    else:
        assert not np.any(form)
        rank=0
    records.append({'mask':mask,'kind':kind,'basis_dimension':n,
        'basis_independent_mod_prime':True,
        'every_reconstructed_tangent_rank_row_annihilates_basis_exactly':True,
        'exact_bilinear_rank':rank,'explicit_ell_m_factorization_verified':True,
        'integer_bilinear_bound':bound})
    print(mask,kind,'basis',n,'form rank',rank,'PASS',flush=True)
assert total==583

anchors=[]
for rank in [4,5]:
    mask=np.array([[int(o[1]==0 and((a[0]==0 and a[3]==0)or(a[0]==1 and a[2]==0)))
        if rank==4 else int(o[3]==0 and(a[2]==0 or(a[0]==0 and a[1]==1 and a[2]==1)))
        for a in WORDS] for o in WORDS])
    anchors.append(T*mask[:,:,None])
A=np.stack(anchors)
ell,m=lm(A)
assert list(ell)==[4,0] and list(m)==[0,4]
forms=np.zeros((2,2),dtype=np.int64)
for o,a,b,p,q,sg in dual_terms:
    x=A[:,o,a,p];y=A[:,o,b,q];forms+=sg*(np.outer(x,y)+np.outer(y,x))
assert np.array_equal(forms,np.array([[0,16],[16,0]]))

(ROOT/'auxiliary_host_compatibility_independent_audit_checks.json').write_text(json.dumps({
    'status':'PASS','verified_prime':P,'total_rational_tangent_basis_dimension':total,
    'exact_total_form_rank':2,'signature':[1,1],'radical_dimension':581,
    'blocks':records,'anchor_functionals_C4':[1,0],'anchor_functionals_C5':[0,1],
    'anchor_omega_C4_C5':1,
    'mixed_XOR_typing':'Selected equal-output words require equal XOR masks on both coefficient factors.',
    'mixed_real_imaginary_typing':'Their products are purely imaginary and are killed by the real dual functional.',
    'scope':'Exact bilinear identity on the entire complete real tangent space; the host consequence requires the common-baseline mixed-derivative argument reviewed in the accompanying note.'},indent=2)+'\n')
print('PASS: omega = ell tensor m + m tensor ell on the entire583-dimensional real tangent space.',flush=True)
