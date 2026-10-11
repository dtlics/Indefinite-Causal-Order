"""Exact four-word obstruction form on the full audited auxiliary tangent space.

All actual native filler directions in any single host must jointly annihilate
this symmetric real bilinear form.  This is a necessary condition only.
"""
from pathlib import Path
from itertools import product
import json
import numpy as np
import sympy as s
from exact_fixtures import E,I16,I2,R,Z,WORDS,tensor,local
ROOT=Path(__file__).parent
P=1000003
T=np.zeros((16,16,16),dtype=np.int64)
for o,ow in enumerate(WORDS):
    for a,aw in enumerate(WORDS):
        row=4*s.eye(16)[a,:]-sum((8*E[i][a,:] for i in range(4) if ow[i]!=aw[i]),s.zeros(1,16))
        assert all(x.is_Integer for x in row)
        T[o,a]=[int(x) for x in row]

cuts=json.loads((ROOT/'continuous_product_supported_cut_audit_all_cylinders_checks.json').read_text())['cuts']
def carrier(L):
    rec=next(x for x in cuts if x['before_queries']==[i+1 for i in L]);rr=[i for i in range(4) if i not in L];cols=[]
    for left in product(range(2),repeat=len(L)):
        for sv in rec['after_carrier_basis']:
            v=s.Matrix([s.sympify(x) for x in sv]);col=s.zeros(16,1)
            for right in product(range(2),repeat=len(rr)):
                w=[0]*4
                for i,b in zip(L,left):w[i]=b
                for i,b in zip(rr,right):w[i]=b
                n=sum(b<<(3-i) for i,b in enumerate(w));a=sum(b<<(len(rr)-1-i) for i,b in enumerate(right));col[n]=v[a]
            cols.append(col)
    return s.Matrix.hstack(*cols)
Bs=[carrier([i]) for i in range(4)]+[carrier([0,1])]
def imat(A):
    assert all(x.is_Integer for x in A)
    return np.array(A.tolist(),dtype=np.int64)
def coords(n):
    for a in range(n):
        H=s.zeros(n);H[a,a]=1;yield H,'real',[a,a]
    for a in range(n):
        for b in range(a+1,n):
            H=s.zeros(n);H[a,b]=H[b,a]=1;yield H,'real',[a,b]
            H=s.zeros(n);H[a,b]=1;H[b,a]=-1;yield H,'imag',[a,b]
spaces={(m,k):[] for m in range(16) for k in ['real','imag']}
labels={key:[] for key in spaces};pivots={key:{} for key in spaces}
def add(m,k,v,label):
    v=v.reshape(4096)
    row={int(j):int(v[j])%P for j in np.flatnonzero(v) if v[j]%P};pp=pivots[m,k]
    while row:
        j=min(row);x=row[j]
        if j not in pp:
            inv=pow(x,-1,P);pp[j]={c:a*inv%P for c,a in row.items()}
            spaces[m,k].append(v.copy());labels[m,k].append(label);return
        for c,a in pp[j].items():
            z=(row.get(c,0)-x*a)%P
            if z:row[c]=z
            elif c in row:del row[c]

for H,k,ab in coords(16):
    h=imat(H)
    add(0,k,np.array([T[o]@h for o in range(16)]),['past',*ab])
    for m in range(16):add(m,k,np.array([int(h[r,r^m])*T[r^m] for r in range(16)]),['future',*ab])
units=[s.Matrix(2,2,lambda r,c:int(r==a and c==b)) for a,b in product(range(2),repeat=2)]
for i,B in enumerate(Bs[:4]):
    reps=[imat(4*R[i]*local(i,u)*R[i]) for u in units];bit=1<<(3-i)
    for H,k,ab in coords(B.cols):
        h=imat(B*H*B.H);mats=[h@rep for rep in reps]
        for m in [0,bit]:
            v=np.zeros((16,16,16),dtype=np.int64)
            for r,n in product(range(16),repeat=2):v[r,n]=mats[2*int(bool((r^m)&bit))+int(bool(n&bit))][(n&~bit)|(r&bit)]
            add(m,k,v,['serial',i+1,*ab])
left={}
for o,n in product(range(4),repeat=2):
    mat=np.zeros((16,16),dtype=np.int64)
    for r in range(4):mat[4*o+r]=T[4*o+r,4*n+r]
    left[o,n]=mat
for H,k,ab in coords(Bs[4].cols):
    h=imat(Bs[4]*H*Bs[4].H);mats={key:h@mat for key,mat in left.items()}
    for m in [0,4,8,12]:
        v=np.zeros((16,16,16),dtype=np.int64)
        for r,n in product(range(16),repeat=2):v[r,n]=mats[(r^m)//4,n//4][4*(r//4)+n%4]
        add(m,k,v,['cut12',*ab])
assert sum(map(len,spaces.values()))==557
extras=json.loads((ROOT/'auxiliary_tangent_extra_directions.json').read_text())['directions']
for i,d in enumerate(extras):
    v=np.zeros(4096,dtype=np.int64)
    for j,x in d['integer_coefficients'].items():v[int(j)]=x
    add(d['mask'],d['kind'],v,['extra',i,'denominator',d['denominator']])
assert sum(map(len,spaces.values()))==583

# Each raw summand contracts coefficient tensors at the SAME future row.
# Therefore the XOR-zero obstruction couples only equal XOR blocks. Taking
# its real part couples only real-real and imaginary-imaginary coefficients.
opts=[[(1,a,1,a,1) for a in range(2)]]+[[(0,a,0,b,1),(1,a,1,b,-1)] for a,b in product(range(2),repeat=2)]
chosen=[([0,1,0,1],2,2,-1),([0,1,0,2],2,0,-1),([0,2,0,1],2,6,1),([0,2,0,3],0,6,1)]
raw=[]
for key,pp,qq,weight in chosen:
    for term in product(*[opts[key[k]] for k in range(4)]):
        o=sum(term[k][0]<<(3-k) for k in range(4));a=sum(term[k][1]<<(3-k) for k in range(4));b=sum(term[k][3]<<(3-k) for k in range(4));sg=weight*int(np.prod([t[4] for t in term]));raw.append((o,a,b,pp,qq,sg))
report=[]
saved={}
for (m,k),vecs in spaces.items():
    V=np.array(vecs,dtype=np.int64).reshape(len(vecs),16,16,16);B=np.zeros((len(vecs),len(vecs)),dtype=np.int64)
    for o,a,b,pp,qq,sg in raw:
        x=V[:,o^m,a,pp];y=V[:,o^m,b,qq]
        B+=sg*(np.outer(x,y)+np.outer(y,x))
    assert np.array_equal(B,B.T)
    if m==0 and k=='real':
        ell=V[:,10,2,2]-V[:,14,2,2]+V[:,10,3,0]-V[:,14,3,0]
        mm=-V[:,10,2,2]+V[:,11,2,2]+V[:,10,6,6]-V[:,11,6,6]
    else:ell=mm=np.zeros(len(vecs),dtype=np.int64)
    assert np.array_equal(B,np.outer(ell,mm)+np.outer(mm,ell))
    MB=s.Matrix(B.tolist());rank=s.polys.matrices.DomainMatrix.from_Matrix(MB).convert_to(s.QQ).rank()
    active=np.flatnonzero(np.any(B,axis=0)).tolist()
    rec={'mask':m,'kind':k,'tangent_dimension':len(vecs),'exact_form_rank':rank,'explicit_functional_factorization_exact':True,'nonzero_basis_indices':active,'active_basis_labels':[labels[m,k][j] for j in active], 'active_form_matrix':B[np.ix_(active,active)].tolist()}
    report.append(rec);saved[f'{m}_{k}']=np.array(vecs,dtype=np.int64)
    print(m,k,'dim',len(vecs),'form rank',rank,'active',len(active),flush=True)
np.savez_compressed(ROOT/'auxiliary_host_compatibility_tangent_basis.npz',**saved)
(ROOT/'auxiliary_host_compatibility_form_checks.json').write_text(json.dumps({'status':'EXACT_FACTORIZATION_PASS','total_tangent_dimension':583,'total_form_rank':sum(x['exact_form_rank'] for x in report),'blocks':report,'basis_labels':{f'{m}_{k}':v for (m,k),v in labels.items()},'scope':'Necessary pairwise isotropy for all native filler directions in one actual host; no sufficiency or graph exclusion.'},indent=2)+'\n')
