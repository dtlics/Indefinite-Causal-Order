"""Exact original-query linearity tests for both full-cut/C4 active orders."""
from pathlib import Path
from itertools import product
import json
import numpy as np
import sympy as s
from phase_endpoint_exact import row_tensor,WORDS
ROOT=Path(__file__).parent
T=row_tensor(4,1)
mask=np.array([[int(o[1]==0 and((a[0]==0 and a[3]==0)or(a[0]==1 and a[2]==0)))for a in WORDS]for o in WORDS])
C=T*mask[:,:,None]
I=np.eye(2,dtype=np.int64);X=np.array([[0,1],[1,0]],dtype=np.int64);Z=np.diag([1,-1]);J=X@Z
PS=[I,X,Z,J]
q2=np.zeros((4,4),dtype=np.int64);q2[1,1]=q2[3,3]=1;q2[1,3]=q2[3,1]=-1


def kron(us):
    W=us[0]
    for u in us[1:]:W=np.kron(W,u)
    return W


def ev(t,us):
    W=kron(us)
    return np.array([W[r]@t[r]for r in range(16)])


def both(us,a2):
    f=ev(T,us);c=ev(C,us)
    g=kron([I,I]+us[2:])@a2@ev(T,us[:2]+[I,I])
    return [c@f.T@g,g@f.T@c]


found={}
# Prefer the very simple identity spectator contexts, then one/two Pauli Xs.
contexts=sorted(product(range(4),repeat=4),key=lambda v:(sum(x!=0 for x in v),v))
unit_pairs=[(2,2)]+[p for p in product(range(4),repeat=2) if p!=(2,2)]
for ab in unit_pairs:
    a=np.zeros((4,4),dtype=np.int64);a[ab]=1;a2=np.kron(a,q2)
    for ctx in contexts:
        if len(found)==2:break
        for i in range(4):
            if ctx[i]!=0:continue
            us=[PS[x] for x in ctx]
            vals=[]
            for u in [I,J,3*I+4*J]:
                vv=us.copy();vv[i]=u;vals.append(both(vv,a2))
            for order in range(2):
                if order in found:continue
                d=vals[2][order]-25*(3*vals[0][order]+4*vals[1][order])
                if np.any(d):
                    r,p=map(int,np.argwhere(d!=0)[0]);numerator=int(d[r,p])
                    entry=s.Rational(numerator,128*125)
                    found[order]={'order':'C4 Fdag Gactive'if order==0 else'Gactive Fdag C4',
                        'active_M4_matrix_unit':list(ab),'varied_query':i+1,
                        'spectator_Pauli_indices_I_X_Z_XZ':list(ctx),
                        'rotation':'(3 I +4 XZ)/5',
                        'linearity_defect_entry':[r,p,str(entry)],
                        'integer_defect_nonzero_entries':int(np.count_nonzero(d)),
                        'scaling':'stored matrix is 128*125 times E(rotation)-(3E(I)+4E(XZ))/5'}
                    print(found[order],flush=True)
    if len(found)==2:break
report={'status':'BOTH_ORDERS_FAIL'if len(found)==2 else'INCOMPLETE','witnesses':[found[k]for k in sorted(found)],
        'scope':'Exact failures of the two specified active orders. Exclusion of all joint extensions additionally requires the proper-block bipartite comparison and analytic-disjunction argument.'}
(ROOT/'auxiliary_cut_C4_order_scout_checks.json').write_text(json.dumps(report,indent=2)+'\n')
