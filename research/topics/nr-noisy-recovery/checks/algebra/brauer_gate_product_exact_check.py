"""Complete exact finite-D gate-product converse replay (Python stdlib only).

Rebuilds the averaged objectives, checks their coefficients by the exact Gram
matrix, rebuilds every causal dual slack, and verifies diagram SOS positivity.
The certificate's supplied slacks and search diagnostics are never trusted.
"""
from __future__ import annotations
if not __debug__:
    raise RuntimeError('Exact certificate replay requires Python without -O; assertions are proof checks.')
import argparse
from fractions import Fraction as F
from functools import reduce
import json
import math
from pathlib import Path
import time
from brauer_exact_replay import ExactBrauerAlgebra as Algebra
from brauer_objective import objective_vector,operator_coefficients
from brauer_sos_certificate import (certify_psd,exact_coefficients,
    insert_identity_coefficients as insert,partial_trace_coefficients as trace)

HERE=Path(__file__).resolve().parent

def add(x,y,scale=F(1)):
    return tuple(a+scale*b for a,b in zip(x,y))

def verify_objective(algebra,D,gamma,label,kind,gram):
    f=objective_vector(algebra,D,gamma,label,kind)
    w=tuple(operator_coefficients(algebra,D,gamma,label,kind))
    denominator=reduce(math.lcm,(v.denominator for v in w),1)
    integers=[int(v*denominator) for v in w]
    # Independently check ALL Gram equations, rather than trust the routine
    # that inverted the central convolution kernel.
    for i,row in enumerate(gram):
        lhs=sum(a*b for a,b in zip(row,integers))
        assert F(lhs,denominator)==f[algebra.star[i]],('Gram equation',i)
    assert all(w[i]==w[algebra.star[i]] for i in range(algebra.size))
    return w

def verify_file(path):
    started=time.time()
    cert=json.loads(Path(path).read_text())
    assert cert['schema']=='brauer_exact_dual_v1'
    meta=cert['metadata'];D=meta['D'];gamma=F(meta['gamma']);mode=meta['mode']
    assert D==8 and gamma==F(1,10),'This certificate fixes D8, gamma1/10.'
    assert mode in ('heralded','deterministic')
    p=1-gamma+(1-F(1,D*D))*gamma*gamma/2
    q=(1-gamma)**2+(2*gamma-F(3,2)*gamma*gamma)/(D*D)
    assert F(meta['probability_requirement'])==p
    a5=Algebra((-1,1,-1,1,-1));a3=Algebra((-1,1,-1))
    witness=cert['witness']
    z=exact_coefficients(a3,witness['Z']);t=F(witness['T']);lam=F(witness['Lambda'])
    a4,zi=insert(a3,z,3,1);a2,zt=trace(a3,D,z,2)
    last=list(-v for v in zt);last[a2.identity]+=t
    gram=None;expected=[];objectives=0
    labels=('A','B') if mode=='deterministic' else ('B',)
    for label in labels:
        y=exact_coefficients(a5,witness[f'Y_{label}'])
        a6,yi=insert(a5,y,5,1)
        if gram is None:gram=a6.gram(D)
        of=verify_objective(a6,D,gamma,label,'fidelity',gram);objectives+=1
        if mode=='heralded':
            op=verify_objective(a6,D,gamma,label,'probability',gram);objectives+=1
            expected.append((f'{label}_YI',a6,yi))
            expected.append((f'{label}_performance',a6,add(add(yi,op,lam),of,F(-1))))
        else:
            assert lam==0
            expected.append((f'{label}_performance',a6,add(yi,of,F(-1))))
        _,yt=trace(a5,D,y,4)
        expected.append((f'{label}_prefix',a4,add(zi,yt,F(-1))))
    expected.append(('last_prefix',a2,tuple(last)))
    assert len(cert['slacks'])==len(expected)
    reports=[]
    for row,(name,algebra,slack) in zip(cert['slacks'],expected):
        assert row['name']==name and tuple(row['signature'])==algebra.signature
        assert exact_coefficients(algebra,row['slack'])==slack,('slack mismatch',name)
        report=certify_psd(algebra,D,slack,row['factors'])
        assert report.verified,('PSD certificate failed',name)
        reports.append({'name':name,'verified':True,'margin':str(report.margin)})
    claimed=F(meta['claimed_bound'])
    if mode=='heralded':
        assert lam>=F(2,D*D) and D*t>0
        assert claimed==lam+D*t/p==F(102,125)
        switch_value=q/p
        scope='all ordinary adaptive protocols with at most two total calls; averaged Bell-input success at least p'
        switch_error=1-switch_value
    else:
        assert claimed==D*t==F(813,1000)
        switch_value=q+(gamma-gamma*gamma/2)/(D*D-1)
        scope='all ordinary adaptive trace-preserving protocols with at most two total calls'
        switch_error=1-switch_value
    result={'status':'passed','arithmetic':'Python standard library; exact integers and Fractions',
            'D':D,'gamma':str(gamma),'mode':mode,'scope':scope,
            'objective_Gram_equations_checked':objectives*a6.size,
            'slacks_rebuilt_and_verified':reports,'ordinary_upper':str(claimed),
            'switch_fidelity':str(switch_value),'strict_fidelity_gap':str(switch_value-claimed),
            'switch_half_diamond_error':str(switch_error),
            'ordinary_some_frame_Bell_error_lower':str(1-claimed),
            'switch_probability':str(p) if mode=='heralded' else '1',
            'affine_lambda':str(lam),'affine_intercept':str(D*t),
            'seconds':time.time()-started}
    assert switch_value>claimed
    return result

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('certificate',nargs='?',
        default=str(HERE/'brauer_exact_certificate_D8_g1_10_heralded.json'))
    parser.add_argument('--output')
    args=parser.parse_args();result=verify_file(args.certificate)
    if args.output:Path(args.output).write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))
