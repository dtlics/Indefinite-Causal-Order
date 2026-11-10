#!/usr/bin/env python3
"""Finite-dimensional numerical checks for the accompanying research note.

Requires Python >=3.10, numpy, scipy. These checks verify selected algebraic
identities, not the source repository's adaptive lower bound or asymptotic
proofs. Run: python verify_results.py --output checks.json
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import numpy as np
from scipy.linalg import eigh


def kraus_apply(ks, x):
    return sum((k @ x @ k.conj().T for k in ks), np.zeros_like(x, dtype=complex))


def choi(ks):
    d = ks[0].shape[0]
    return sum((np.outer(k.reshape(-1, order='F'), k.reshape(-1, order='F').conj()) / d for k in ks), np.zeros((d*d, d*d), complex))


def superop(ks):
    return sum((np.kron(k.conj(), k) for k in ks), np.zeros((ks[0].size, ks[0].size), complex))


def visibility(a, b):
    d = a[0].shape[0]
    return float(np.real(sum(np.trace(x.conj().T @ y.conj().T @ x @ y) for x in a for y in b))/d)


def fidelity(ks):
    d = ks[0].shape[0]
    return float(sum(abs(np.trace(k))**2 for k in ks)/d**2)


def unitarity(ks):
    d = ks[0].shape[0]
    v = np.eye(d).reshape(-1, order='F')/np.sqrt(d)
    proj = np.eye(d*d) - np.outer(v, v)
    t = proj @ superop(ks) @ proj
    return float(np.linalg.norm(t, 'fro')**2/(d*d-1))


def haar(d, rng):
    q,r = np.linalg.qr(rng.normal(size=(d,d))+1j*rng.normal(size=(d,d)))
    phase=np.diag(r); phase=phase/np.abs(phase)
    return q @ np.diag(phase)


def pinch(d, u):
    return [np.outer(u[:,i],u[:,i].conj()) for i in range(d)]


def depol(d):
    out=[]
    for i in range(d):
        for j in range(d):
            k=np.zeros((d,d),complex);k[i,j]=1/np.sqrt(d);out.append(k)
    return out


def diluted(ks, p):
    d=ks[0].shape[0]
    return [np.sqrt(1-p)*np.eye(d)]+[np.sqrt(p)*k for k in ks]


def state_td(a,b):
    h=(a-b+(a-b).conj().T)/2
    return float(np.sum(np.abs(np.linalg.eigvalsh(h)))/2)


def switch_state(a,b,rho):
    out=np.zeros((2*rho.shape[0],2*rho.shape[0]),complex)
    for x in a:
        for y in b:
            p=y@x; q=x@y
            out += .5*np.block([[p@rho@p.conj().T,p@rho@q.conj().T],[q@rho@p.conj().T,q@rho@q.conj().T]])
    return out


def run():
    rng=np.random.default_rng(20261026)
    rows=[]
    maxerr=0.
    for d in (2,4,8):
        u=haar(d,rng); ps=pinch(d,u); om=depol(d)
        for p in (.02,.2,.75,1.0):
            q=p*d/(d+1); alpha=1-q
            e=diluted(ps,p); m=diluted(om,q)
            vals={
                'f_equal':abs(fidelity(e)-fidelity(m)),
                'f_formula':abs(fidelity(e)-(1-p+p/d)),
                'v_pinching':abs(visibility(e,e)-1),
                'v_model':abs(visibility(m,m)-(1-p*p*(d-1)/(d+1))),
                'u_difference':abs((unitarity(e)-unitarity(m))-p*p*d/(d+1)**2),
                'choi_distance':abs(state_td(choi(e),choi(m))-p*(d-1)/(d+1)),
            }
            for length in (1,2,5):
                ek=diluted(ps,1-(1-p)**length)
                mk=diluted(om,1-alpha**length)
                dist=(1-1/d)*(1-alpha**length)
                vals[f'power_choi_{length}']=abs(state_td(choi(ek),choi(mk))-dist)
                vals[f'power_state_{length}']=abs(state_td(kraus_apply(ek,ps[0]),kraus_apply(mk,ps[0]))-dist)
                # M^{-length} is a signed linear map, NOT generally a channel.
                out=kraus_apply(ek,ps[0]); corrected=out/alpha**length+(1-alpha**(-length))*np.eye(d)/d
                vals[f'PEC_residual_{length}']=abs(state_td(corrected,ps[0])-(alpha**(-length)-1)*(1-1/d))
            err=max(vals.values()); maxerr=max(maxerr,err)
            assert err<1e-9,(d,p,vals)
            rows.append({'d':d,'p':p,'max_identity_error':err,'f':fidelity(e),'v_pinching':visibility(e,e),'v_model':visibility(m,m),'distance':p*(d-1)/(d+1)})
    # Susceptibility on generic nondegenerate Hamiltonians.
    susceptibility=[]
    for d in (2,4,6):
        h=np.diag(np.arange(d,dtype=float))
        z=rng.normal(size=(d,d))+1j*rng.normal(size=(d,d)); V=(z+z.conj().T)/2
        V=V/np.linalg.norm(V,2)
        chi=sum(abs(V[j,i])**2/(i-j)**2 for i in range(d) for j in range(d) if j!=i)/d
        vals=[]
        for lam in (.02,.01,.005):
            pp=[]
            for sign in (-1,1):
                _,u=eigh(h+sign*lam*V)
                v=float(np.sum(np.abs(u)**4)/d)
                pp.append((1-v)/2)
            estimate=sum(pp)/(2*lam**2)
            vals.append({'lambda':lam,'estimate':estimate,'error':abs(estimate-chi)})
        assert vals[-1]['error']<max(1e-7,.08*vals[0]['error'])
        susceptibility.append({'d':d,'chi':float(chi),'symmetric_estimates':vals})
    # Random channel pairs: known-unitary pre/post compiler equals the switch.
    compiler=[]
    for d in (2,3,4):
        u=haar(d,rng)
        raw=rng.normal(size=(3*d,d))+1j*rng.normal(size=(3*d,d)); iso,_=np.linalg.qr(raw)
        bs=[iso[i*d:(i+1)*d,:] for i in range(3)]
        z=rng.normal(size=(d,d))+1j*rng.normal(size=(d,d)); rho=z@z.conj().T;rho/=np.trace(rho)
        p0=np.diag([1.,0.]);p1=np.diag([0.,1.]); ident=np.eye(d)
        pre=np.kron(p0,u)+np.kron(p1,ident)
        post=np.kron(p0,ident)+np.kron(p1,u)
        inp=np.kron(np.ones((2,2))/2,rho)
        result=sum((post@np.kron(np.eye(2),b)@pre@inp@pre.conj().T@np.kron(np.eye(2),b).conj().T@post.conj().T for b in bs),np.zeros((2*d,2*d),complex))
        err=float(np.linalg.norm(result-switch_state([u],bs,rho),'fro'))
        assert err<1e-10
        compiler.append({'d':d,'error':err})
    return {'status':'all numerical assertions passed','scope':'Finite checks of explicit identities only; no independent C5/C6 proof audit.', 'max_matched_model_identity_error':maxerr,'matched_model_tests':rows,'susceptibility_tests':susceptibility,'known_arm_compiler_tests':compiler}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('checks.json'))
    args=parser.parse_args()
    data=run();args.output.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in data.items() if k not in ('matched_model_tests','susceptibility_tests','known_arm_compiler_tests')},indent=2))
    print(f'Wrote {args.output.resolve()}')
if __name__=='__main__':main()
