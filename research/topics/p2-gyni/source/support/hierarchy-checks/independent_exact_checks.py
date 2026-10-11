#!/usr/bin/env python3
"""Exact finite algebra audit; does not import the author's code or use an SDP."""
import json
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
import sympy as S


def cancel(word):
    ans=[]
    for letter in word:
        if ans and ans[-1] == letter: ans.pop()
        else: ans.append(letter)
    return tuple(ans)


def word_of(k,b):
    return cancel(((0,1)*k if k>=0 else (1,0)*(-k)) + ((0,) if b else ()))


def affine(word):
    # R0(t)=-t and R1(t)=-t-1; compose in written operator order.
    sign,shift=1,0
    for letter in word:
        shift-=sign*letter
        sign=-sign
    return shift, 0 if sign==1 else 1


def ball(radius):
    return [()] + [tuple((start+j)%2 for j in range(n))
                   for n in range(1,radius+1) for start in (0,1)]


def symbolic_encoder(M):
    N=2*M+1
    representatives=[word_of(k,b) for b in (0,1) for k in range(-M,M+1)]
    support={}
    for k in range(M):
        for w in (word_of(k,0),word_of(-k,1)):
            shift,b=affine(w)
            support[(shift%N,b)]=(w,k)
    assert len(support)==2*M
    for generator in (0,1):
        monomials=defaultdict(Fraction)
        for w,k in support.values():
            sh,b=affine((generator,)+w)
            if (sh%N,b) not in support: continue
            h,j=support[(sh%N,b)]
            actual_word=cancel(h+tuple(reversed(w)))
            assert actual_word==(generator,), (M,generator,w,h,actual_word)
            monomials[tuple(sorted((j,k)))]+=Fraction(1,2)
        expected=({(k,k):Fraction(1) for k in range(M)} if generator==0
                  else {(k,k+1):Fraction(1) for k in range(M-1)})
        assert dict(monomials)==expected,(M,generator,monomials,expected)
    # Exact bound for every Kraus monomial, not only a winning branch.
    degree=max(len(cancel(h+tuple(reversed(w))))
               for h in representatives for w,k in support.values())
    assert degree<=4*M
    # A NEW quotient is injective on all coefficient overlap words.
    Q=8*M+1
    overlap_ball=ball(8*M)
    images=[(affine(w)[0]%Q,affine(w)[1]) for w in overlap_ball]
    assert len(set(images))==len(overlap_ball)
    return {'M':M,'source_order':2*N,'max_local_degree':degree,
            'probe_order':2*Q,'distinct_overlap_words':len(images)}


def exact_error_sos():
    delta=S.symbols('delta',real=True)
    errors=[S.Matrix([0]),S.Matrix([delta/8,-delta/8]),
            S.Matrix([delta/8,-delta/8]),
            S.Matrix([-delta/8,-delta/8,(2*delta-delta**2)/8])]
    # Absolute values on 0<=delta<=1.
    signs=[[1],[1,-1],[1,-1],[-1,-1,1]]
    scales=[]
    for e,sgn in zip(errors,signs):
        masses=[S.expand(sgn[i]*e[i]) for i in range(len(e))]
        s=sum(masses)
        D=S.diag(*[s*a for a in masses])
        residual=D-e*e.T
        pairs=S.zeros(len(e))
        for i in range(len(e)):
            for j in range(i+1,len(e)):
                direction=S.zeros(len(e),1)
                direction[i]=sgn[i]
                direction[j]=-sgn[j]
                pairs+=masses[i]*masses[j]*(direction*direction.T)
        assert all(S.expand(z)==0 for z in residual-pairs)
        scales.append(S.expand(S.trace(D)))
    total=S.factor(sum(scales))
    assert S.expand(total-delta**2*(24-8*delta+delta**2)/64)==0
    # (3/8)delta^2-total = delta^3(8-delta)/64 >=0.
    assert S.expand(3*delta**2/S.Integer(8)-total-delta**3*(8-delta)/64)==0
    return {'scale':str(total),'excess_below_3delta2_over8':str(S.factor(3*delta**2/S.Integer(8)-total)),
            'diagonal_minus_rank_one':'Verified exact sum over pairs for every flag'}


if __name__=='__main__':
    data={'verdict':'passed','arithmetic':'Exact integers, rational polynomial coefficients, symbolic identities; no numerical solver or author imports',
          'encoder_and_probe_cases':[symbolic_encoder(M) for M in range(1,41)],
          'error_sos':exact_error_sos(),
          'scope':'Finite checks of all structural formulas up to M=40; general analytic proof is in audit.md'}
    Path(__file__).with_name('independent_exact_checks.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:v for k,v in data.items() if k!='encoder_and_probe_cases'},indent=2))
