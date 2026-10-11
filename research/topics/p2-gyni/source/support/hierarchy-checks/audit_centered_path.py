#!/usr/bin/env python3
"""Exact centered-path audit, independent of the author's path checker."""
import json
from pathlib import Path
from collections import defaultdict
import sympy as S
from independent_exact_checks import word_of,affine,cancel,ball


def g(j):
    return word_of(-j//2,0) if j%2==0 else word_of((j-1)//2,1)


def case(N):
    labels=range(-N+1,N+1)
    supp=range(-N+2,N)
    E={j:g(j) for j in labels}
    invE={w:j for j,w in E.items()}
    assert all(len(w)==abs(j) for j,w in E.items())
    q=[(affine(w)[0]%N,affine(w)[1]) for w in E.values()]
    assert len(set(q))==2*N
    for j in range(-2*N,2*N+1):
        k,b=affine(g(j)); kp,bp=affine(g(j+2*N))
        assert (k%N,b)==(kp%N,bp)
    edges=defaultdict(int)
    for s in (0,1):
        for j in supp:
            image=cancel((s,)+E[j])
            assert image in invE
            actual=invE[image]
            step=1 if j%2==0 else -1
            expected=j+(step if s==0 else -step)
            assert actual==expected
            assert cancel(image+tuple(reversed(E[j])))==(s,)
            if actual in supp: edges[tuple(sorted((j,actual)))]+=1
    assert dict(edges)=={(j,j+1):2 for j in range(-N+2,N-1)}
    degree=max(len(cancel(h+tuple(reversed(E[j])))) for h in E.values() for j in supp)
    assert degree<=2*N-1
    Q=4*N-1
    words=ball(4*N-2)
    images=[(affine(w)[0]%Q,affine(w)[1]) for w in words]
    assert len(set(images))==len(images)
    return {'N':N,'representatives':2*N,'interior_vertices':2*N-2,
            'max_lifted_degree':degree,'claimed_degree':2*N-1,
            'fresh_probe_cyclic_order':Q,'probe_word_count':len(images)}


def recurrence():
    z=S.symbols('z',nonzero=True)
    f=lambda j:z**j-z**(-j)
    for j in range(1,81):
        assert S.expand(f(j-1)+f(j+1)-(z+1/z)*f(j))==0
    return 'Exact Laurent recurrence verified for j=1,...,80; z=exp(i*pi/(m+1)) gives the analytic sine eigenvector with zero endpoints'


if __name__=='__main__':
    data={'verdict':'passed','arithmetic':'Exact words, integers and Laurent polynomials; no author code imports',
          'cases':[case(N) for N in range(2,61)],'sine_recurrence':recurrence(),
          'conclusion':'b_(2N-1) <= c_N sec^4(pi/(4N-2))'}
    Path(__file__).with_suffix('.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:v for k,v in data.items() if k!='cases'},indent=2))
