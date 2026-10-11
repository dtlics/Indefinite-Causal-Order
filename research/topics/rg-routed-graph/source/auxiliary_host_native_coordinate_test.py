"""Exact eight obstruction coordinates on native original-query insertions."""
from pathlib import Path
from itertools import product
import json,numpy as np,sympy as s
from exact_fixtures import E,I16,I2,R,Z,WORDS,local,tensor
ROOT=Path(__file__).parent
V=s.Matrix(np.load(ROOT/'auxiliary_host_compatibility_tangent_basis.npz')['0_real'].tolist())
dm=s.polys.matrices.DomainMatrix.from_Matrix(V).convert_to(s.QQ)
_,piv=dm.rref();assert len(piv)==172
minor=V[:,list(piv)];L=s.zeros(8,172)
for row,d in enumerate([{167:1},{168:8,169:1},{164:3,165:-1,168:-1,170:1},{161:1,162:-1,164:-2,170:-2},{163:1,168:-8,170:-8},{159:1,160:-1,161:-1,162:1},{160:1,162:-1},{151:2,153:-2,164:-1,165:-1,168:1,170:-1}]):
    for i,x in d.items():L[row,i]=x
dual=L*minor.T.inv()
assert dual*minor.T==L
assert (L.rank(),dual.rank())==(8,8)
rows=[]
for name,row in zip('abcdefgh',dual.tolist()):
    rec=[]
    for jj,v in enumerate(row):
        if not v:continue
        rr,t=divmod(piv[jj],256);aa,pp=divmod(t,16);rec.append({'coefficient_index':[rr,aa,pp],'weight':str(v)})
    rows.append({'name':name,'terms':rec})
print('Coordinate term counts',[(r['name'],len(r['terms'])) for r in rows],flush=True)
cuts=json.loads((ROOT/'continuous_product_supported_cut_audit_all_cylinders_checks.json').read_text())['cuts']
def carrier(i):
    rec=next(x for x in cuts if x['before_queries']==[i+1]);rr=[j for j in range(4) if j!=i];cols=[]
    for bit in range(2):
        for sv in rec['after_carrier_basis']:
            v=s.Matrix([s.sympify(x) for x in sv]);col=s.zeros(16,1)
            for rights in product(range(2),repeat=3):
                w=[0]*4;w[i]=bit
                for j,b in zip(rr,rights):w[j]=b
                col[sum(b<<(3-j) for j,b in enumerate(w))]=v[sum(b<<(2-j) for j,b in enumerate(rights))]
            cols.append(col)
    return s.Matrix.hstack(*cols)
units=[s.Matrix(2,2,lambda r,c:int(r==a and c==b)) for a,b in product(range(2),repeat=2)]
native=[]
for i in range(4):
    B=carrier(i);n=B.cols;Ks=[s.zeros(n) for j in range(8)];bit=1<<(3-i)
    reps=[R[i]*local(i,u)*R[i] for u in units]
    for a in range(n):
        for b in range(a,n):
            A=s.zeros(n);A[a,b]=A[b,a]=1;H=B*A*B.H;mats=[H*rep for rep in reps];vec=[]
            for jj in piv:
                r,t=divmod(jj,256);nu,q=divmod(t,16);t=(nu&~bit)|(r&bit)
                vec.append(mats[2*int(bool(r&bit))+int(bool(nu&bit))][t,q])
            out=dual*s.Matrix(vec)
            for k,v in enumerate(out):Ks[k][a,b]=Ks[k][b,a]=v/(1 if a==b else 2)
    gram=B.H*B
    phys=[B*gram.inv()*K*gram.inv()*B.H for K in Ks]
    native.append({'query':i+1,'basis':[[str(x) for x in col] for col in B.columnspace()],'coordinate_compression_matrices':{k:[[str(x) for x in row] for row in K.tolist()] for k,K in zip('abcdefgh',Ks)},'nonzero_coordinates':[k for k,K in zip('abcdefgh',Ks) if K!=s.zeros(n)],'h_physical_matrix':[[str(x) for x in row] for row in phys[-1].tolist()]})
    print('query',i+1,'nonzero',[k for k,K in zip('abcdefgh',Ks) if K!=s.zeros(n)],'h in carrier coords',Ks[-1],flush=True)
(ROOT/'auxiliary_host_native_coordinate_test_checks.json').write_text(json.dumps({'status':'EXACT_COORDINATES','coefficient_functionals':rows,'native_serial_insertions':native,'scope':'Coordinates on allowed native original-query insertions; not a claim every host uses a maximal promotion.'},indent=2)+'\n')
