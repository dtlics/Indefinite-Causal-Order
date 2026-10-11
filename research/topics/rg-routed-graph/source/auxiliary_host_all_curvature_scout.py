"""Discover mixed-word obstruction forms in any XOR and real/imaginary sector.

This finite-field output is exploratory. Exact rational dual lifting is required
before claiming new constraints. Boundary compatibility removes 511 directions.
"""
from pathlib import Path
from itertools import product
import json,time,sys,math
import numpy as np
from phase_endpoint_exact import row_tensor,WORDS
ROOT=Path(__file__).parent;P=1000003;T=row_tensor(4,1)
kappa=int(sys.argv[1]);mode=sys.argv[2] if len(sys.argv)>2 else 'real';parity=1 if mode=='real' else -1
meta=json.loads((ROOT/'auxiliary_host_compatibility_form_checks.json').read_text());src=np.load(ROOT/'auxiliary_host_compatibility_tangent_basis.npz')
vectors=[];labels=[];masks=[];kinds=[]
for key,labs in meta['basis_labels'].items():
    m=int(key.split('_')[0]);kind=key.split('_')[1]
    for idx,lab in enumerate(labs):
        if lab[0] in ['past','future']:continue
        vectors.append(src[key][idx].reshape(16,16,16));labels.append({'mask':m,'kind':kind,'typed_basis_index':idx,'label':lab});masks.append(m);kinds.append(int(kind=='imag'))
V=np.array(vectors,dtype=np.int64);masks=np.array(masks,dtype=np.int64);kinds=np.array(kinds,dtype=np.int64);assert len(V)==72
pairs=[];ii=[];jj=[];s1=[]
for i in range(72):
    for j in range(i,72):
        if masks[i]^masks[j]!=kappa or kinds[i]^kinds[j]!=int(mode=='imag'):continue
        pairs.append({'left':labels[i],'right':labels[j]});ii.append(i);jj.append(j);s1.append(-1 if kinds[i]==1 and kinds[j]==0 else 1)
ii=np.array(ii);jj=np.array(jj);s1=np.array(s1,dtype=np.int64);s2=parity*s1;n=len(ii)
print('TARGET',kappa,mode,'columns',n,flush=True)
if n==0:
    (ROOT/f'auxiliary_host_all_curvature_{kappa}_{mode}_checks.json').write_text(json.dumps({'status':'NO_NONBOUNDARY_PAIR_COLUMNS','mask':kappa,'mode':mode,'independent_residual_forms':0})+'\n');sys.exit()
opts=[]
for bit in [8,4,2,1]:
    if kappa&bit:opts.append([[(r,a,1-r,b,1)] for r,a,b in product(range(2),repeat=3)])
    else:opts.append([[(1,a,1,a,1) for a in range(2)]]+[[(0,a,0,b,1),(1,a,1,b,-1)] for a,b in product(range(2),repeat=2)])
def rawterms(key):
    out=[]
    for term in product(*[opts[i][key[i]] for i in range(4)]):
        r=sum(term[i][0]<<(3-i) for i in range(4));a=sum(term[i][1]<<(3-i) for i in range(4));t=sum(term[i][2]<<(3-i) for i in range(4));b=sum(term[i][3]<<(3-i) for i in range(4));sg=math.prod(x[4] for x in term);out.append((r,a,t,b,sg))
    return out
def rhs(raw):
    B=np.zeros((n,16,16),dtype=np.int64)
    for r,a,t,b,sg in raw:
        f=r^masks[ii];g=r^masks[jj]
        assert np.all((f^masks[jj])==t) and np.all((g^masks[ii])==t)
        x=V[ii,f,a,:];y=V[jj,f,b,:];w=V[jj,g,a,:];z=V[ii,g,b,:]
        B+=sg*(s1[:,None,None]*x[:,:,None]*y[:,None,:]+s2[:,None,None]*w[:,:,None]*z[:,None,:])
    return B
def arow(raw,pp,qq):
    row={}
    for r,a,t,b,sg in raw:
        i=(r*16+b)*16+qq;j=(t*16+a)*16+pp
        row[i]=row.get(i,0)+sg*int(T[r,a,pp]);row[j]=row.get(j,0)+sg*parity*int(T[t,b,qq])
    return {i:x%P for i,x in row.items() if x%P}
source=json.loads((ROOT/f'auxiliary_tangent_output_block_{kappa}_{"imag" if mode=="real" else "real"}.json').read_text());recs=source['rows'];piv={};last=None;start=time.time()
for number,(key,pp,qq) in enumerate(recs):
    if key!=last:raw=rawterms(key);B=rhs(raw);last=key
    row=arow(raw,pp,qq);v=B[:,pp,qq].copy()%P
    while row:
        k=min(row);zz=row[k]
        if k not in piv:
            zi=pow(zz,-1,P);piv[k]=({i:x*zi%P for i,x in row.items()},v*zi%P);break
        old,vv=piv[k];v=(v-zz*vv)%P
        for i,x in old.items():
            zzz=(row.get(i,0)-zz*x)%P
            if zzz:row[i]=zzz
            elif i in row:del row[i]
    else:raise AssertionError('retained rank row lost independence')
assert len(piv)==source['rank_lower_bound']
sol=np.zeros((4096,n),dtype=np.int64)
for k,(row,v) in sorted(piv.items(),reverse=True):
    val=v.copy()
    for i,x in row.items():
        if i!=k:val=(val-x*sol[i])%P
    sol[k]=val
sol=sol.reshape(16,16,16,n)
print('Retained rows solved, rank',len(piv),'seconds',time.time()-start,flush=True)
forms={};records=[]
for ki,key in enumerate(product(*[range(len(x)) for x in opts])):
    raw=rawterms(key);B=rhs(raw)%P;AE=np.zeros((16,16,n),dtype=np.int64)
    for r,a,t,b,sg in raw:
        AE=(AE+sg*(T[r,a,:,None,None]*sol[r,b,None,:,:]+parity*sol[t,a,:,None,:]*T[t,b,None,:,None]))%P
    residual=(B-AE.transpose(2,0,1))%P
    for pp,qq in product(range(16),repeat=2):
        vv=residual[:,pp,qq].copy()
        if not np.any(vv):continue
        original=vv.copy()
        for k,old in sorted(forms.items()):
            if vv[k]:vv=(vv-int(vv[k])*old)%P
        nz=np.flatnonzero(vv)
        if len(nz):
            k=int(nz[0]);vv=vv*pow(int(vv[k]),-1,P)%P;forms[k]=vv
            records.append({'word_key':list(key),'boundary_entry':[pp,qq],'pivot':k,'residual_coefficients':original.tolist()})
            print('New form',len(forms),'key',key,'entry',pp,qq,flush=True)
    if ki%200==0:print('Scanned',ki,'forms',len(forms),'seconds',time.time()-start,flush=True)
out={'status':'MODULAR_DISCOVERY_ONLY','mask':kappa,'mode':mode,'prime':P,'retained_mixed_rank':len(piv),'pair_columns':n,'independent_residual_forms':len(forms),'pairs':pairs,'forms':records,'seconds':time.time()-start,'scope':'Finite-field discovery of host-wide mixed-word forms; exact rational certification required.'}
(ROOT/f'auxiliary_host_all_curvature_{kappa}_{mode}_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('DONE',kappa,mode,len(forms),'forms','seconds',time.time()-start,flush=True)
