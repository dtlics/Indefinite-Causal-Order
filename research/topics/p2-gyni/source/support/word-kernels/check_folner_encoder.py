#!/usr/bin/env python3
"""Independent finite-group and complex-matrix checks for the encoder proof."""
import json, math
from pathlib import Path
import numpy as np

def mul(g,h,N=None):
    k,b=g;l,c=h
    z=k+(-1)**b*l
    return (z if N is None else z%N,b^c)
def inv(g):
    k,b=g;return ((-1)**(b+1)*k,b)
def reducew(seq):
    a=[]
    for s in seq:
        if a and a[-1]==s:a.pop()
        else:a.append(s)
    return tuple(a)
def word(g):
    k,b=g
    return reducew(((0,1)*k if k>=0 else (1,0)*(-k))+((0,) if b else ()))
def encoder_data(M):
    N=2*M+1
    reps=[(k,b) for b in (0,1) for k in range(-M,M+1)]
    ids={(k%N,b):i for i,(k,b) in enumerate(reps)}
    f=np.sqrt(2/(M+1))*np.sin(np.pi*(np.arange(M)+1)/(M+1))
    eta=np.zeros(2*N)
    for k in range(M):
        eta[ids[(k,0)]]=f[k]/np.sqrt(2)
        eta[ids[((-k)%N,1)]]=f[k]/np.sqrt(2)
    lam=[]
    for s in ((0,1),(-1,1)):
        L=np.zeros((2*N,2*N))
        for j,g in enumerate(reps):L[ids[mul(s,g,N)],j]=1
        lam.append(L)
    return N,reps,eta,lam

def run():
    report=[]
    rng=np.random.default_rng(20260930)
    max_alias=0;maxdegree=0;tests=0
    for M in (1,2,3,4,6,9):
        N,reps,eta,L=encoder_data(M)
        for a,s in enumerate(((0,1),(-1,1))):
            agg={}
            for i,h in enumerate(reps):
                for j,g in enumerate(reps):
                    coef=eta[i]*L[a][i,j]*eta[j]
                    if abs(coef)<1e-15:continue
                    z=mul(h,inv(g))
                    agg[z]=agg.get(z,0)+coef
                    assert z==s,(M,s,g,h,z)
            expected=1 if a==0 else math.cos(math.pi/(M+1))
            assert abs(agg.get(s,0)-expected)<1e-14,(M,a,agg,expected)
            tests+=1
        degree=max(len(word(mul(h,inv(g)))) for h in reps for j,g in enumerate(reps) if eta[j]!=0)
        assert degree<=4*M,(M,degree)
        maxdegree=max(maxdegree,degree)
        for d in (1,2,3,5):
            # Arbitrary complex involutions, including scalar and unequal ranks.
            q,_=np.linalg.qr(rng.normal(size=(d,d))+1j*rng.normal(size=(d,d)))
            R0=q@np.diag(rng.choice([-1,1],size=d))@q.conj().T
            q,_=np.linalg.qr(rng.normal(size=(d,d))+1j*rng.normal(size=(d,d)))
            R1=q@np.diag(rng.choice([-1,1],size=d))@q.conj().T
            U=R0@R1
            pi=lambda g:np.linalg.matrix_power(U,g[0])@(R0 if g[1] else np.eye(d))
            V=np.vstack([a*pi(inv(g)) for a,g in zip(eta,reps)])
            errs=[np.linalg.norm(V.conj().T@V-np.eye(d))]
            for a,R in enumerate((R0,R1)):
                expected=R if a==0 else math.cos(math.pi/(M+1))*R
                errs.append(np.linalg.norm(V.conj().T@np.kron(L[a],np.eye(d))@V-expected))
            assert max(errs)<1e-11,(M,d,errs)
            tests+=3
            report.append({'M':M,'dimension':d,'max_error':max(errs),'max_word_length':degree})
    # Exact symbolic coefficient comparisons of error diagonal majorant.
    import sympy as sp
    delta=sp.Symbol('delta',positive=True)
    sums=[0,delta/4,delta/4,(4*delta-delta**2)/8]
    de=sp.factor(sum(v*v for v in sums))
    assert sp.expand(de-delta**2*(24-8*delta+delta**2)/64)==0
    out={'status':'passed','checks':tests,'max_matrix_error':max(x['max_error'] for x in report),'error_channel_scale':str(de),'details':report,
         'scope':'Numerical matrix identities plus exact group support checks and symbolic error-scale identity; these are checks of the written proof, not an optimized upper certificate.'}
    p=Path(__file__).with_name('folner_encoder_checks.json');p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':run()
