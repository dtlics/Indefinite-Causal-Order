#!/usr/bin/env python3
"""Exact formal-word/Fourier check; supplementary to the uniform proof.

The words in a_i commute only with each other. L and Ld remain free until
explicitly imposing Ld=-L and a_i L=-L a_i. Fractions are exact throughout.
"""
from fractions import Fraction
from itertools import product
from pathlib import Path
import json

# Exact Gaussian rational coefficients as (real, imaginary).
ZERO=(Fraction(0),Fraction(0))
ONE=(Fraction(1),Fraction(0))
I=(Fraction(0),Fraction(1))
def add(x,y): return x[0]+y[0],x[1]+y[1]
def mul(x,y): return x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0]
def scale(x,r): return x[0]*r,x[1]*r
def conj(x): return x[0],-x[1]
def ipow(k): return (ONE,I,scale(ONE,-1),scale(I,-1))[k%4]
def put(poly,word,coef):
    value=add(poly.get(word,ZERO),coef)
    if value==ZERO: poly.pop(word,None)
    else: poly[word]=value

def char(mask,eps):
    v=1
    for i,e in enumerate(eps):
        if mask>>i&1: v*=e
    return v

def check(n):
    full=(1<<n)-1
    # Distinct exact Pythagorean pairs ensure that no equality relies on c=s.
    pairs=[(3,4,5),(5,12,13),(8,15,17),(7,24,25),(20,21,29),(12,35,37)]
    cs=[Fraction(c,d) for c,s,d in pairs[:n]]
    ss=[Fraction(s,d) for c,s,d in pairs[:n]]
    t=Fraction(1)
    for s in ss: t*=s
    terms=[]
    for S in range(1<<n):
        scalar=Fraction(1)
        word=[]
        for j in range(n):
            if S>>j&1:
                scalar*=ss[j]
                word.append('a'+str(j+1))
            else: scalar*=cs[j]
        terms.append((full^S,tuple(word),scale(ipow(S.bit_count()),scalar)))
    # Build defect evaluations directly, then inverse Fourier transform.
    # We already know G*G=I, since each commuting reflection factor is unitary.
    values=[]
    for eps in product((-1,1),repeat=n):
        defect={}
        for mask,word,z in terms:
            z=scale(z,char(mask,eps))
            put(defect,word+('L',),scale(conj(z),t))
            put(defect,('Ld',)+word,scale(z,t))
        put(defect,('Ld','L'),(t*t,Fraction(0)))
        values.append((eps,defect))
    fourier={}
    for mask in range(1<<n):
        coefficient={}
        for eps,defect in values:
            factor=Fraction(char(mask,eps),1<<n)
            for word,z in defect.items(): put(coefficient,word,scale(z,factor))
        fourier[mask]=coefficient
    # Check the three coefficient types quoted in the proof exactly.
    prodc=Fraction(1)
    for c in cs: prodc*=c
    assert fourier[full]=={('L',):(t*prodc,Fraction(0)),('Ld',):(t*prodc,Fraction(0))}
    for j in range(n):
        pref=t*ss[j]
        for k in range(n):
            if k!=j: pref*=cs[k]
        assert fourier[full^(1<<j)]=={
            ('a'+str(j+1),'L'):(Fraction(0),-pref),
            ('Ld','a'+str(j+1)):(Fraction(0),pref)}
    A=tuple('a'+str(j+1) for j in range(n))
    expected={A+('L',):scale(ipow(-n),t*t),('Ld',)+A:scale(ipow(n),t*t),('Ld','L'):(t*t,Fraction(0))}
    assert fourier[0]==expected
    # Impose exactly the inferred relations, normal form A_S L or L*L.
    # Ld A_S = -L A_S = -(-1)^|S| A_S L.
    reduced={}
    for word,z in fourier[0].items():
        if word==('Ld','L'): put(reduced,('Ld','L'),z)
        elif word[0]=='Ld':
            aset=word[1:]
            put(reduced,aset+('L',),scale(z,-((-1)**len(aset))))
        else: put(reduced,word,z)
    assert reduced=={('Ld','L'):(t*t,Fraction(0))}
    # Also check cancellation in every nonconstant coefficient after these
    # relations; this catches missing parity/conjugation signs uniformly.
    for mask,coefficient in fourier.items():
        if mask==0: continue
        reduced={}
        for word,z in coefficient.items():
            if word[0]=='Ld':
                aset=word[1:]
                put(reduced,aset+('L',),scale(z,-((-1)**len(aset))))
            else: put(reduced,word,z)
        assert not reduced
    return {'n':n,'sign_tuples':1<<n,'fourier_characters':1<<n,
            'full_character_skewness':'PASS',
            'all_but_one_anticommutation':'PASS',
            'constant_positive_square':'PASS',
            'all_mixed_terms_cancel':'PASS'}

if __name__=='__main__':
    report={'arithmetic':'exact Gaussian rational formal-word Fourier transform',
            'status':'PASS','checks':[check(n) for n in range(2,7)],
            'scope':'Supplementary finite verification; the all-n result is proved analytically in commuting_phase_rigidity_proof.md.'}
    out=Path(__file__).with_name('signed_reflection_coefficient_checks.json')
    out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
