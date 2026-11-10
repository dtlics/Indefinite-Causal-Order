#!/usr/bin/env python3
"""Symmetry-reduced two-call discrimination diagnostic (numpy/scipy only).

Numerical, NOT an exact rational/interval certificate. Compares one scalar
self-switch classifier with arbitrary two-call causal testers for a fixed
Haar-hidden dephaser versus its mean Lambda=(id+d Omega)/(d+1).
"""
from __future__ import annotations
import itertools, json, argparse
from pathlib import Path
import numpy as np
from scipy.linalg import null_space
from threadpoolctl import threadpool_limits


def permutation(d,k,p):
    D=d**k
    inds=np.indices((d,)*k).reshape(k,-1)
    dest=np.ravel_multi_index(tuple(inds[j] for j in p),(d,)*k)
    out=np.zeros((D,D));out[dest,np.arange(D)]=1
    return out


def pt(x,d,k,sites):
    axes=list(range(2*k))
    for i in sites: axes[i],axes[k+i]=axes[k+i],axes[i]
    return x.reshape((d,)*(2*k)).transpose(axes).reshape(d**k,d**k)


def invariant_basis(d,k,sites):
    ps=[permutation(d,k,p) for p in itertools.permutations(range(k))]
    mats=np.array([pt((p+p.T)/2,d,k,sites).ravel() for p in ps])
    _,s,vt=np.linalg.svd(mats,full_matrices=False)
    return vt[s>1e-9*s.max()].reshape(-1,d**k,d**k)


def haar_pair(d):
    ps=np.array([permutation(d,4,p) for p in itertools.permutations(range(4))])
    flat=ps.reshape(24,-1);gram=flat@flat.T
    diag=np.zeros(d**4)
    for i in range(d):
        for j in range(d):diag[np.ravel_multi_index((i,i,j,j),(d,)*4)]=1/d**2
    rhs=np.einsum('aii,i->a',ps,diag)
    coeff=np.linalg.pinv(gram,rcond=1e-12)@rhs
    twirl=np.einsum('a,aij->ij',coeff,ps)
    high=d*d*pt(twirl,d,4,(0,2))
    vec=np.eye(d).ravel();j_id=np.outer(vec,vec)
    j_lam=(j_id+np.eye(d*d))/(d+1)
    low=np.kron(j_lam,j_lam)
    return (high+high.T)/2,low


def solve(d):
    high,low=haar_pair(d);delta=high-low;D=d**4
    xi_basis=invariant_basis(d,3,(0,2))
    traced=np.array([np.trace(x.reshape(d*d,d,d*d,d),axis1=1,axis2=3).ravel() for x in xi_basis]).T
    ker=null_space(traced,rcond=1e-9)
    fs=np.einsum('ab,aij->bij',ker,xi_basis)
    gs=invariant_basis(d,4,(0,2))
    xs=np.array([.5*np.kron(f,np.eye(d)) for f in fs])
    aa=np.concatenate((xs,gs));bb=np.concatenate((xs,-gs))
    base=np.eye(D)/(2*d*d)
    c=np.einsum('ij,aji->a',delta,aa)
    z=np.zeros(len(c))
    def evaluate(z,mu,deriv=False):
        t=base+np.einsum('a,aij->ij',z,aa)
        s=base+np.einsum('a,aij->ij',z,bb)
        try:
            lt=np.linalg.cholesky(t);ls=np.linalg.cholesky(s)
        except np.linalg.LinAlgError:return None
        val=c@z+mu*2*(np.log(np.diag(lt)).sum()+np.log(np.diag(ls)).sum())
        if not deriv:return val
        it=np.linalg.solve(t,np.eye(D));ins=np.linalg.solve(s,np.eye(D))
        a=it@aa;b=ins@bb
        g=c+mu*(np.trace(a,axis1=1,axis2=2)+np.trace(b,axis1=1,axis2=2))
        h=mu*(np.einsum('aij,bji->ab',a,a)+np.einsum('aij,bji->ab',b,b))
        return val,g,(h+h.T)/2,t,s
    totaliter=0
    for mu in [10**(-i) for i in range(1,10)]:
        for _ in range(65):
            totaliter+=1
            val,g,h,t,s=evaluate(z,mu,True)
            direction=np.linalg.solve(h,g)
            if g@direction<1e-14:break
            step=1.
            for attempt in range(80):
                vv=evaluate(z+step*direction,mu)
                if vv is not None and vv>=val+.01*step*(g@direction):break
                step*=.5
            if step<1e-14:break
            z=z+step*direction
    val,g,h,t,s=evaluate(z,mu,True)
    objective=float(np.trace(delta@t))
    # Bound the variable-vector norm over the affine feasible set.
    radius=np.sqrt((d+1/np.sqrt(d))**2+(1.5*d*d)**2)
    analytic_gap=2*D*mu+(radius+np.linalg.norm(z))*np.linalg.norm(g)
    # This uses floating point and is therefore NOT a rigorous exact certificate.
    np.savez(Path(__file__).parent / f'two_call_candidate_d{d}.npz', Z=mu*np.linalg.inv(s), high=high, low=low, T=t, T1=s)
    return dict(d=d,variables=len(z),iterations=totaliter,
        ordinary_success_lower=.5+.5*objective,
        ordinary_success_residual_upper=.5+.5*(objective+analytic_gap),
        switch_control_success=.5+(d-1)/(4*(d+1)),
        serial_Bell_test_success=.5+(d-1)/(2*d*(d+1)),
        barrier_mu=mu,gradient_norm=float(np.linalg.norm(g)),
        tester_min_eigenvalue=float(min(np.linalg.eigvalsh(t).min(),np.linalg.eigvalsh(s).min())),
        high_trace=float(np.trace(high)),high_min_eigenvalue=float(np.linalg.eigvalsh(high).min()),
        normalization_high=float(np.trace((t+s)@high)),normalization_low=float(np.trace((t+s)@low)),
        note='Numerical symmetry-reduced causal tester optimization; upper value uses a floating-point barrier/residual bound, not interval-certified arithmetic.')


def main():
    pa=argparse.ArgumentParser();pa.add_argument('--dimensions',nargs='+',type=int,default=[2,3]);pa.add_argument('--output',type=Path,default=Path('two_call_results.json'));args=pa.parse_args()
    results=[]
    with threadpool_limits(limits=1):
        for d in args.dimensions:
            r=solve(d);results.append(r);print(json.dumps(r),flush=True)
    args.output.write_text(json.dumps(results,indent=2)+'\n')
if __name__=='__main__':main()
