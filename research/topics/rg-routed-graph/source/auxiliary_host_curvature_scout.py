"""Discover all real XOR-zero mixed-word obstruction forms modulo a prime.

Boundary insertions are universally compatible with every tangent direction,
so only the 72-dimensional quotient by the boundary span is retained. This is
a discovery calculation; any resulting theorem needs rational dual lifting.
"""
from pathlib import Path
from itertools import product
import json,time
import numpy as np
from phase_endpoint_exact import row_tensor,WORDS
ROOT=Path(__file__).parent;P=1000003;T=row_tensor(4,1)
meta=json.loads((ROOT/'auxiliary_host_compatibility_form_checks.json').read_text());src=np.load(ROOT/'auxiliary_host_compatibility_tangent_basis.npz')
groups=[];pairs=[];count=0
for key,labs in meta['basis_labels'].items():
    ids=[i for i,label in enumerate(labs) if label[0] not in ['past','future']]
    if not ids:continue
    m=int(key.split('_')[0]);kind=key.split('_')[1];V=src[key][ids].reshape(len(ids),16,16,16)
    ij=[(i,j) for i in range(len(ids)) for j in range(i,len(ids))]
    groups.append((m,kind,V,np.array([i for i,j in ij]),np.array([j for i,j in ij]),count,count+len(ij)))
    pairs.extend([{'mask':m,'kind':kind,'basis_indices':[ids[i],ids[j]],'labels':[labs[ids[i]],labs[ids[j]]]} for i,j in ij]);count+=len(ij)
print('quotient dimension',sum(len(g[2]) for g in groups),'pair columns',count,flush=True)
opts=[[(1,a,1,a,1) for a in range(2)]]+[[(0,a,0,b,1),(1,a,1,b,-1)] for a,b in product(range(2),repeat=2)]
def rawterms(key):
    out=[]
    for term in product(*[opts[key[i]] for i in range(4)]):
        r=sum(term[i][0]<<(3-i) for i in range(4));a=sum(term[i][1]<<(3-i) for i in range(4));b=sum(term[i][3]<<(3-i) for i in range(4));sg=int(np.prod([t[4] for t in term]));out.append((r,a,b,sg))
    return out
def rhs(raw):
    B=np.zeros((count,16,16),dtype=np.int64)
    for r,a,b,sg in raw:
        for m,kind,V,ii,jj,lo,hi in groups:
            x=V[:,r^m,a,:];y=V[:,r^m,b,:]
            B[lo:hi]+=sg*(x[ii,:,None]*y[jj,None,:]+x[jj,:,None]*y[ii,None,:])
    return B
def arow(raw,pp,qq):
    row={}
    for r,a,b,sg in raw:
        i=(r*16+b)*16+qq;j=(r*16+a)*16+pp
        row[i]=row.get(i,0)+sg*int(T[r,a,pp]);row[j]=row.get(j,0)+sg*int(T[r,b,qq])
    return {i:x%P for i,x in row.items() if x%P}
recs=json.loads((ROOT/'auxiliary_tangent_output_block_0_imag.json').read_text())['rows'];piv={};last=None;start=time.time()
for number,(key,pp,qq) in enumerate(recs):
    if key!=last:raw=rawterms(key);B=rhs(raw);last=key
    row=arow(raw,pp,qq);v=B[:,pp,qq].copy()%P
    while row:
        k=min(row);z=row[k]
        if k not in piv:
            zi=pow(z,-1,P);piv[k]=({i:x*zi%P for i,x in row.items()},v*zi%P);break
        old,vv=piv[k];v=(v-z*vv)%P
        for i,x in old.items():
            zz=(row.get(i,0)-z*x)%P
            if zz:row[i]=zz
            elif i in row:del row[i]
    else:raise AssertionError('retained row lost independence')
    if number%500==0:print('Eliminated',number,'seconds',time.time()-start,flush=True)
assert len(piv)==3967
sol=np.zeros((4096,count),dtype=np.int64)
for k,(row,v) in sorted(piv.items(),reverse=True):
    val=v.copy()
    for i,x in row.items():
        if i!=k:val=(val-x*sol[i])%P
    sol[k]=val
sol=sol.reshape(16,16,16,count)
print('Mixed coefficient polynomial solved on retained rows',time.time()-start,flush=True)
forms={};form_records=[]
for ki,key in enumerate(product(range(5),repeat=4)):
    raw=rawterms(key);B=rhs(raw)%P
    AE=np.zeros((16,16,count),dtype=np.int64)
    for r,a,b,sg in raw:
        AE=(AE+sg*(T[r,a,:,None,None]*sol[r,b,None,:,:]+sol[r,a,:,None,:]*T[r,b,None,:,None]))%P
    residual=(B-AE.transpose(2,0,1))%P
    for pp,qq in product(range(16),repeat=2):
        v=residual[:,pp,qq].copy()
        if not np.any(v):continue
        original=v.copy()
        for k,old in sorted(forms.items()):
            if v[k]:v=(v-int(v[k])*old)%P
        nz=np.flatnonzero(v)
        if len(nz):
            k=int(nz[0]);v=v*pow(int(v[k]),-1,P)%P;forms[k]=v
            form_records.append({'word_key':list(key),'boundary_entry':[pp,qq],'pivot':k,'residual_coefficients':original.tolist()})
            print('New obstruction form',len(forms),'key',key,'entry',pp,qq,flush=True)
    if ki%50==0:print('Scanned keys',ki,'forms',len(forms),'seconds',time.time()-start,flush=True)
out={'status':'MODULAR_DISCOVERY_ONLY','prime':P,'retained_mixed_operator_rank':3967,'quotient_tangent_dimension':sum(len(g[2]) for g in groups),'same_typed_block_pair_columns':count,'independent_residual_forms':len(forms),'pairs':pairs,'forms':form_records,'reduced_forms':{str(k):v.tolist() for k,v in forms.items()},'seconds':time.time()-start,'scope':'Complete real XOR-zero word obstruction forms on the whole tangent space, modulo boundary-compatible directions; numerical field discovery requires exact rational certification.'}
(ROOT/'auxiliary_host_curvature_scout_checks.json').write_text(json.dumps(out,indent=2)+'\n')
np.savez_compressed(ROOT/'auxiliary_host_curvature_scout_solution.npz',solution=sol)
print('DONE',len(forms),'forms',time.time()-start,flush=True)
