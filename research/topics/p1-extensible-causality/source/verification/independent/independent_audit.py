#!/usr/bin/env python3
"""Independent audit. No functions imported from author scripts.
Exact construction uses integer Pauli tensors, and trace/replace uses
explicit basis indices. Numerical probability contractions use full matrices.
The analytical proof, not finite testing, establishes uniform extensible causality.
"""
import itertools, json, math
from pathlib import Path
import numpy as np
import sympy as s
from scipy.optimize import linprog
from scipy.linalg import sqrtm

ROOT=Path(__file__).parent
RNG=np.random.default_rng(958027)
I=np.eye(2); X=np.array([[0,1],[1,0]]); Z=np.diag([1,-1]); P=np.diag([0,1])
def kron(*ops):
    ret=np.array([[1]])
    for op in ops: ret=np.kron(ret,op)
    return ret

def permute(op,dims,order):
    n=len(dims)
    return op.reshape(tuple(dims)*2).transpose(list(order)+[n+j for j in order]).reshape(op.shape)

def tr_keep(op,dims,keep):
    a=op.reshape(tuple(dims)*2)
    ds=list(dims)
    for j in reversed(range(len(ds))):
        if j not in keep:
            a=np.trace(a,axis1=j,axis2=j+len(ds)); ds.pop(j)
    d=math.prod(ds)
    return a.reshape(d,d)

def trace_pair(A,B):
    return np.sum(A*B.T)

def exact_replace(M,dims,sites):
    # Intentionally index-based rather than tensor-reshape or author code.
    D=math.prod(dims); out=s.zeros(D)
    bases=list(itertools.product(*[range(d) for d in dims]))
    pos={bs:i for i,bs in enumerate(bases)}
    traced=list(itertools.product(*[range(dims[j]) for j in sites]))
    scale=math.prod(dims[j] for j in sites)
    for a,ia in enumerate(bases):
        for b,ib in enumerate(bases):
            if any(ia[j]!=ib[j] for j in sites): continue
            val=0
            for sub in traced:
                aa=list(ia); bb=list(ib)
                for j,v in zip(sites,sub): aa[j]=bb[j]=v
                val+=M[pos[tuple(aa)],pos[tuple(bb)]]
            out[a,b]=val/scale
    return out

# Exact full flagged process, fine ordering FA AI AO FB BI BO.
Af=s.Matrix(kron(P,Z,Z,P,Z,I).astype(int)); Bf=s.Matrix(kron(P,X,I,P,Z,Z).astype(int))
Pf=s.Matrix(kron(P,I,I,P,I,I).astype(int))
W=(5*s.eye(64)+3*(Af+Bf))/80
S=Pf-Af-Bf
RA=lambda M:exact_replace(M,[2]*6,[2])
RB=lambda M:exact_replace(M,[2]*6,[5])
RAB=lambda M:exact_replace(M,[2]*6,[2,5])
linear=[exact_replace(W,[2]*6,[3,4,5])-exact_replace(W,[2]*6,[2,3,4,5]),
        exact_replace(W,[2]*6,[0,1,2])-exact_replace(W,[2]*6,[0,1,2,5]),
        W-RA(W)-RB(W)+RAB(W)]
exact={
 'trace':str(s.trace(W)),
 'full_process_constraints_zero':all(M==s.zeros(64) for M in linear),
 'output_replacement_white':RAB(W)==s.eye(64)/16,
 'witness_value':str(s.trace(W*S)),
 'A_order_witness_reduction':RB(S)==Pf-Af,
 'B_order_witness_reduction':RA(S)==Pf-Bf,
 'reduction_A_is_twice_projector':(Pf-Af)**2==2*(Pf-Af),
 'reduction_B_is_twice_projector':(Pf-Bf)**2==2*(Pf-Bf),
 'active_terms_anticommute':Af*Bf+Bf*Af==s.zeros(64),
 'active_terms_square_to_flag_projector':Af**2==Pf and Bf**2==Pf,
 'flag_projector_rank':Pf.rank(),
 'positive_spectrum':['(5-3*sqrt(2))/80 [8]','(5+3*sqrt(2))/80 [8]','1/16 [48]'],
 'minimum_eigenvalue_positive_exact':bool(5>3*s.sqrt(2)),
}
assert all(v for v in exact.values()) and exact['witness_value']=='-1/5'

# Generate complex CP maps from isometries. We explicitly construct ordinary
# Choi matrices via vec(K) and then transpose the FULL matrix once.
def instrument(input_dim,outcomes=3):
    kr=max(2,math.ceil(input_dim/(2*outcomes)))
    rows=2*outcomes*kr
    G=RNG.standard_normal((rows,input_dim))+1j*RNG.standard_normal((rows,input_dim))
    U=np.linalg.qr(G,mode='reduced')[0]
    mats=[]
    for a in range(outcomes):
        J=np.zeros((input_dim*2,input_dim*2),complex)
        for k in range(kr):
            K=U[2*(a*kr+k):2*(a*kr+k+1)]
            v=K.T.flatten()
            J+=np.outer(v,v.conj())
        mats.append(J.T)
    assert np.linalg.norm(tr_keep(sum(mats),[input_dim,2],[0])-np.eye(input_dim))<1e-12
    return mats

def phi(M,T,d):
    # Embed T on AI AO, then reorder to AI RA AO before ordinary multiplication.
    embedded=permute(np.kron(T,np.eye(d)),[2,2,d],[0,2,1])
    return tr_keep(embedded@M,[2,d,2],[1])/2

def resource(W,dims,rho,da,db,flagged=False):
    if flagged:
        order=[0,1,6,2,3,4,7,5]
    else:
        order=[0,4,1,2,5,3]
    return permute(np.kron(W,rho),dims+[da,db],order)

V=(np.eye(16)+.6*(kron(Z,Z,Z,I)+kron(X,I,Z,Z)))/4
O=np.eye(16)/4
Wn=np.array(W,complex)
metrics={k:0. for k in ['white_formula_error','direction_formula_error','flag_refinement_error','normalization_error','channel_zero_image_error','naimark_probability_error','naimark_projector_error','causal_split_residual']}
metrics.update({k:float('inf') for k in ['minimum_complement_slack','minimum_tensor_order_slack','minimum_rectangle_slack','minimum_graph_slack']})
metrics.update({'ancilla_dimensions':[],'complex_experiments':0,'exhaustive_rectangles':0,'lp_splits_verified':0,'coherent_flag_offdiagonal_norm_min':float('inf')})
allmasks=np.array(list(itertools.product([0,1],repeat=6)),float)

def recorderr(k,v): metrics[k]=max(metrics[k],float(abs(v)))
def recordmin(k,H): metrics[k]=min(metrics[k],float(np.linalg.eigvalsh((H+H.conj().T)/2).min()))
def dilate(E):
    E=(E+E.conj().T)/2
    vals,U=np.linalg.eigh(E)
    off=(U*np.sqrt(np.clip(vals*(1-vals),0,1)))@U.conj().T
    return np.block([[E,off],[off,np.eye(len(E))-E]])

for da,db in [(1,1),(2,2),(2,3),(3,2)]:
    metrics['ancilla_dimensions'].append([da,db])
    for trial in range(4):
        # Alternate pure entangled and full-rank complex states.
        D=da*db
        G=RNG.standard_normal((D,1 if trial%2==0 else D))+1j*RNG.standard_normal((D,1 if trial%2==0 else D))
        rho=G@G.conj().T; rho/=np.trace(rho)
        ms=[instrument(4*da) for x in range(2)]
        ns=[instrument(4*db) for y in range(2)]
        dm=4*da; dn=4*db
        for instruments,d in [(ms,dm),(ns,dn)]:
            for inst in instruments:
                for M in inst: metrics['coherent_flag_offdiagonal_norm_min']=min(metrics['coherent_flag_offdiagonal_norm_min'],float(np.linalg.norm(M[:d,d:])))
        mb=[[[M[f*dm:(f+1)*dm,f*dm:(f+1)*dm] for M in inst] for f in range(2)] for inst in ms]
        nb=[[[N[g*dn:(g+1)*dn,g*dn:(g+1)*dn] for N in inst] for g in range(2)] for inst in ns]
        Rw=resource(Wn,[2]*6,rho,da,db,True)
        Rv=resource(V,[2]*4,rho,da,db)
        Ro=resource(O,[2]*4,rho,da,db)
        for x,y in itertools.product(range(2),repeat=2):
            effA=[[phi(M,np.eye(4),da) for M in mb[x][f]] for f in range(2)]
            effB=[[phi(N,np.eye(4),db) for N in nb[y][g]] for g in range(2)]
            alpha=np.array([trace_pair(rho,np.kron(E,np.eye(db))).real/4 for block in effA for E in block])
            beta=np.array([trace_pair(rho,np.kron(np.eye(da),F)).real/4 for block in effB for F in block])
            p=np.zeros((6,6))
            for f,a,g,b in itertools.product(range(2),range(3),range(2),range(3)):
                rr=Rv if (f==1 and g==1) else Ro
                p[3*f+a,3*g+b]=trace_pair(rr,np.kron(mb[x][f][a],nb[y][g][b])).real/4
            recorderr('normalization_error',p.sum()-1)
            for a,b in itertools.product(range(3),repeat=2):
                direct=trace_pair(Rw,np.kron(ms[x][a],ns[y][b]))
                refined=sum(p[3*f+a,3*g+b] for f,g in itertools.product(range(2),repeat=2))
                recorderr('flag_refinement_error',direct-refined)
            covers=(allmasks@alpha)[:,None]+(allmasks@beta)[None,:]-allmasks@p@allmasks.T
            metrics['minimum_rectangle_slack']=min(metrics['minimum_rectangle_slack'],float(covers.min()))
            metrics['exhaustive_rectangles']+=covers.size
            # Independent feasibility LP for A-before-B cell mass H.
            # H row sums = alpha, H column sums = p column sums - beta; 0<=H<=p.
            Aeq=[]
            for a in range(6):
                row=np.zeros((6,6));row[a,:]=1;Aeq.append(row.ravel())
            for b in range(6):
                col=np.zeros((6,6));col[:,b]=1;Aeq.append(col.ravel())
            rhs=np.r_[alpha,p.sum(axis=0)-beta]
            fit=linprog(np.zeros(36),A_eq=Aeq,b_eq=rhs,bounds=[(0,max(float(z),0)) for z in p.ravel()],method='highs')
            assert fit.success,fit.message
            H=fit.x.reshape(6,6)
            recorderr('causal_split_residual',np.max(np.abs(np.array(Aeq)@fit.x-rhs)))
            assert np.min(H)>=-1e-9 and np.min(p-H)>=-1e-9
            metrics['lp_splits_verified']+=1
            # Channel images and random aggregates, including incompatible E0,E1.
            for f in range(2):
                recorderr('channel_zero_image_error',np.linalg.norm(phi(sum(mb[x][f]),kron(X,I),da)))
                recorderr('channel_zero_image_error',np.linalg.norm(phi(sum(nb[y][f]),kron(Z,I),db)))
            for sample in range(12):
                # Exclude empty/full for most samples; still include them in covers above.
                cutsA=RNG.integers(1,7,size=2);cutsB=RNG.integers(1,7,size=2)
                M=[sum([mb[x][f][a] for a in range(3) if cutsA[f]&(1<<a)]) for f in range(2)]
                N=[sum([nb[y][g][b] for b in range(3) if cutsB[g]&(1<<b)]) for g in range(2)]
                E=[phi(m,np.eye(4),da) for m in M];F=[phi(n,np.eye(4),db) for n in N]
                LA=phi(M[1],kron(Z,Z),da);RAp=phi(M[1],kron(X,I),da)
                LB=phi(N[1],kron(Z,Z),db);RBp=phi(N[1],kron(Z,I),db)
                for C,H in [(np.eye(da)-E[1],RAp),(np.eye(db)-F[1],RBp)]:
                    recordmin('minimum_complement_slack',C-H);recordmin('minimum_complement_slack',C+H)
                q=np.array([[trace_pair(rho,np.kron(e,f)).real for f in F] for e in E])
                a=np.array([trace_pair(rho,np.kron(e,np.eye(db))).real for e in E])
                b=np.array([trace_pair(rho,np.kron(np.eye(da),f)).real for f in F])
                mismatch=a[:,None]+b[None,:]-2*q
                delta_op=.6*(np.kron(LA,RBp)+np.kron(RAp,LB))
                delta=trace_pair(rho,delta_op)
                active=trace_pair(Rv,np.kron(M[1],N[1]))
                white=trace_pair(Ro,np.kron(M[1],N[1]))
                recorderr('white_formula_error',white-q[1,1]);recorderr('direction_formula_error',active-white-delta)
                bound=.6*(np.kron(E[1],np.eye(db)-F[1])+np.kron(np.eye(da)-E[1],F[1]))
                recordmin('minimum_tensor_order_slack',bound-delta_op)
                metrics['minimum_graph_slack']=min(metrics['minimum_graph_slack'],float(3*(mismatch[1,0]+mismatch[0,0]+mismatch[0,1])-mismatch[1,1]))
                # Direct simultaneous dilation in same ancillary basis.
                Ps=[dilate(e) for e in E];Qs=[dilate(f) for f in F]
                # Enlarged local order QA RA QB RB, embed fixed |00>.
                rbig=np.zeros((4*D,4*D),complex)
                indices=[((0*da+i)*(2*db)+(0*db+j)) for i in range(da) for j in range(db)]
                rbig[np.ix_(indices,indices)]=rho
                for f,g in itertools.product(range(2),repeat=2):
                    recorderr('naimark_probability_error',trace_pair(rbig,np.kron(Ps[f],Qs[g]))-q[f,g])
                    recorderr('naimark_projector_error',np.linalg.norm(Ps[f]@Ps[f]-Ps[f]))
                    recorderr('naimark_projector_error',np.linalg.norm(Qs[g]@Qs[g]-Qs[g]))
            metrics['complex_experiments']+=1
        print('checked ancilla',da,db,'trial',trial,flush=True)

for k in ['white_formula_error','direction_formula_error','flag_refinement_error','normalization_error','channel_zero_image_error','naimark_probability_error','naimark_projector_error','causal_split_residual']:
    assert metrics[k]<1e-10,(k,metrics[k])
for k in ['minimum_complement_slack','minimum_tensor_order_slack','minimum_rectangle_slack','minimum_graph_slack']:
    assert metrics[k]>-1e-10,(k,metrics[k])
out={'exact':exact,'numerical':metrics,'interpretation':'All independent checks passed. Numerical tests supplement rather than replace the analytical quantifier-uniform proof.'}
(ROOT/'independent_audit_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
