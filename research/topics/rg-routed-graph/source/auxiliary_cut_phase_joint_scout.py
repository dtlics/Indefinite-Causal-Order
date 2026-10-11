"""All-joint mixed-coefficient test for C4 with one full-M4-cut direction."""
from pathlib import Path
from itertools import product
import json,time,sys
import numpy as np
import sympy as s
from phase_endpoint_exact import row_tensor,WORDS
ROOT=Path(__file__).parent
P=1000003;T=row_tensor(4,1);C=np.zeros_like(T)
for r,o in enumerate(WORDS):
    for a,n in enumerate(WORDS):
        if o[1]==0 and ((n[0]==0 and n[3]==0)or(n[0]==1 and n[2]==0)):C[r,a]=T[r,a]
j=json.loads((ROOT/'auxiliary_host_compatibility_form_checks.json').read_text());labels=j['basis_labels']['0_real']
label=['cut12',int(sys.argv[1]) if len(sys.argv)>1 else 2,int(sys.argv[2]) if len(sys.argv)>2 else 2]
idx=labels.index(label);D=np.load(ROOT/'auxiliary_host_compatibility_tangent_basis.npz')['0_real'][idx].reshape(16,16,16)
opts=[[(1,a,1,a,1) for a in range(2)]]+[[(0,a,0,b,1),(1,a,1,b,-1)] for a,b in product(range(2),repeat=2)]
piv={};records=[];witness=None;start=time.time()
for key in product(range(5),repeat=4):
    raw=[];rhs=np.zeros((16,16),dtype=np.int64)
    for term in product(*[opts[key[i]] for i in range(4)]):
        r=sum(term[i][0]<<(3-i) for i in range(4));a=sum(term[i][1]<<(3-i) for i in range(4));b=sum(term[i][3]<<(3-i) for i in range(4));sg=int(np.prod([t[4] for t in term]));raw.append((r,a,b,sg))
        rhs+=sg*(np.outer(C[r,a],D[r,b])+np.outer(D[r,a],C[r,b]))
    for pp,qq in product(range(16),repeat=2):
        row={};v=int(rhs[pp,qq])%P;v0=v
        for r,a,b,sg in raw:
            ii=(r*16+b)*16+qq;jj=(r*16+a)*16+pp
            row[ii]=(row.get(ii,0)+sg*int(T[r,a,pp]))%P;row[jj]=(row.get(jj,0)+sg*int(T[r,b,qq]))%P
        row={a:b for a,b in row.items() if b}
        while row:
            k=min(row);z=row[k]
            if k not in piv:
                zi=pow(z,-1,P);piv[k]=({i:x*zi%P for i,x in row.items()},v*zi%P);records.append({'word_key':list(key),'row':pp,'column':qq,'rhs':v0});break
            old,vv=piv[k];v=(v-z*vv)%P
            for i,x in old.items():
                zz=(row.get(i,0)-z*x)%P
                if zz:row[i]=zz
                elif i in row:del row[i]
        else:
            if v:
                witness={'word_key':list(key),'row':pp,'column':qq,'rhs':v0,'reduced_rhs':v};records.append(witness);break
    if witness:break
    if len(records)%100==0:print('rank',len(piv),'seconds',time.time()-start,flush=True)
out={'status':'MODULAR_OBSTRUCTION_NEEDS_EXACT_DUAL' if witness else 'MIXED_EQUATION_CONSISTENT_MOD_P','cut_label':label,'zero_block_basis_index':idx,'prime':P,'witness':witness,'coefficient_rank':len(piv),'rank_rows':records,'seconds':time.time()-start,'scope':'Necessary mixed equation only; consistency does not prove joint complete filling.'}
stem=f'auxiliary_cut_phase_joint_{label[1]}_{label[2]}'
(ROOT/(stem+'_checks.json')).write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k!='rank_rows'},flush=True)
