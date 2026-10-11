#!/usr/bin/env python3
"""Exact independent checks of the full-decoder and GYNI-twirl refinement."""
import json
from pathlib import Path
import sympy as S
from independent_exact_checks import cancel, word_of, affine, ball


def supported_images(M):
    E={word_of(k,b) for k in range(-M,M+1) for b in (0,1)}
    support={word_of(k,0) for k in range(M)} | {word_of(-k,1) for k in range(M)}
    checks=0
    for s in (0,1):
        for g in support:
            h=cancel((s,)+g)
            assert h in E,(M,s,g,h)
            assert cancel(h+tuple(reversed(g)))==(s,)
            checks+=1
    return {'M':M,'all_supported_generator_images_in_E':True,'checked_images':checks}


def winning(x,y):
    return {( ((x,) if a else ()),((y,) if b else ())):
            S.Rational((-1)**(a*y+b*x),8)
            for a in (0,1) for b in (0,1)}


def transformed(p,a,b):
    out={}
    for (u,v),coef in p.items():
        pu=tuple(s^a for s in u)
        pv=tuple(s^b for s in v)
        out[pu,pv]=coef*(-1)**(b*len(u)+a*len(v))
    return out


def check_twirl():
    for x in (0,1):
        for y in (0,1):
            for a in (0,1):
                for b in (0,1):
                    assert transformed(winning(x^a,y^b),a,b)==winning(x,y)
    # Explicit equivariance of the reduced overlap map under every local
    # signed generator permutation. This is the NS coefficient interface.
    words=ball(12)
    for swap in (0,1):
        for sign in (0,1):
            for u in words:
                for v in words:
                    pu=tuple(s^swap for s in u)
                    pv=tuple(s^swap for s in v)
                    w=cancel(tuple(reversed(v))+u)
                    pw=tuple(s^swap for s in w)
                    assert cancel(tuple(reversed(pv))+pu)==pw
                    assert (-1)**(sign*(len(u)+len(v)))==(-1)**(sign*len(w))
    lam=S.symbols('lambda',real=True)
    alpha=[S.Integer(1),(1+lam)/2]
    beta=(3+lam)**2/16
    for x in (0,1):
        for y in (0,1):
            avg=sum(alpha[x^a]*alpha[y^b] for a in (0,1) for b in (0,1))/4
            assert S.expand(avg-beta)==0
    # Exact Choi Gram identity for the whole decoded projector branch.
    for eps in (-1,1):
        gram=S.Matrix([[1,eps*lam],[eps*lam,1]])/4
        p=S.Matrix([1,eps])/2
        opposite=S.Matrix([1,-eps])/2
        rhs=(1+lam)/2*(p*p.T)+(1-lam)/2*(opposite*opposite.T)
        assert all(S.expand(z)==0 for z in gram-rhs)
    delta=S.symbols('delta',real=True)
    beta_delta=(1-delta/4)**2
    assert S.expand(1-beta_delta-delta/2+delta**2/16)==0
    assert S.factor(1/beta_delta-1-delta*(8-delta)/(4-delta)**2)==0
    return {'winning_kraus_relabellings':16,
            'signed_overlap_equivariance':'passed for all reduced word pairs of length at most12',
            'full_projector_gram_identity':'passed for both outcomes',
            'twirled_correct_branch_coefficient':str(beta),
            'completion_bound':'b_(4M) <= 16 c_M/(3+lambda)^2',
            'relative_upper_error':'delta(8-delta)/(4-delta)^2',
            'finite_SDP_gap':'omega-c_M <= omega(delta/2-delta^2/16)'}


if __name__=='__main__':
    result={'verdict':'passed','arithmetic':'exact integers and symbolic polynomials; no floating matrices or SDP',
            'support_cases':[supported_images(M) for M in range(1,41)],
            'twirl':check_twirl()}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'verdict':result['verdict'],'twirl':result['twirl']},indent=2))
