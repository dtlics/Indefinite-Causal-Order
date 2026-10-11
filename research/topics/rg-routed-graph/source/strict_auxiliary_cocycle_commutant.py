"""Exact modular-rank lower certificate for strict-partition cocycle commutants."""
from pathlib import Path
from itertools import product
import json,time
import numpy as np
from phase_endpoint_exact import row_tensor,WORDS
ROOT=Path(__file__).parent;P=1000003;T=row_tensor(4,1);values={}
# I,X,Z,XZ; the last has row signs (-,+), all scalar phases cancel in the cocycle.
for choice in product(range(4),repeat=4):
    A=np.zeros((16,16),dtype=np.int64)
    for r,rw in enumerate(WORDS):
        nw=[];sg=1
        for i,o in enumerate(rw):
            gate=choice[i];nw.append(o^(gate in [1,3]));sg*=(-1 if(gate==2 and o==1)or(gate==3 and o==0)else 1)
        n=sum(a<<(3-i) for i,a in enumerate(nw));A[r]=sg*T[r,n]
    values[choice]=A
out=[]
for last in range(4):
    left=[i for i in range(4) if i!=last];piv={};recs=[];count=0;start=time.time()
    for choice in product(range(4),repeat=4):
        if sum(c!=0 for c in choice)<2:continue
        ll=tuple(c if i in left else 0 for i,c in enumerate(choice));rr=tuple(c if i not in left else 0 for i,c in enumerate(choice));C=values[rr].T@values[choice]@values[ll].T
        for a,b in product(range(16),repeat=2):
            row={}
            for k in range(16):
                col=16*k+b;row[col]=(row.get(col,0)+int(C[a,k]))%P
                col=16*a+k;row[col]=(row.get(col,0)-int(C[k,b]))%P
            row={k:v for k,v in row.items() if v}
            while row:
                col=min(row);z=row[col]
                if col not in piv:
                    inv=pow(z,-1,P);piv[col]={j:v*inv%P for j,v in row.items()};recs.append({'query_Pauli_indices':list(choice),'entry':[a,b]});break
                for j,v in piv[col].items():
                    zz=(row.get(j,0)-z*v)%P
                    if zz:row[j]=zz
                    elif j in row:del row[j]
            if len(piv)==255:break
        count+=1
        if len(piv)==255:break
    rec={'before_queries':[i+1 for i in left],'last_query':last+1,'prime':P,'commutator_rank_lower_bound':len(piv),'commutant_dimension_upper_bound':256-len(piv),'contexts_scanned':count,'rank_rows':recs,'seconds':time.time()-start}
    out.append(rec);print({k:v for k,v in rec.items() if k!='rank_rows'},flush=True)
(ROOT/'strict_auxiliary_cocycle_commutant_checks.json').write_text(json.dumps({'status':'EXACT_RANK_LOWER_CERTIFICATES','results':out,'scope':'If rank255, the known scalar kernel closes the characteristic-zero commutant dimension at1, excluding any nontrivial unital matrix auxiliary for that strict partition.'},indent=2)+'\n')
