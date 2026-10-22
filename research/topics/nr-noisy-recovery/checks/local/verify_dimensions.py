"""Independent stdlib Weyl and dimension-bound audit for mixed(3,3).

No SymPy flags or expression strings are used. Closed factorizations are
checked against the symbolic Weyl cross-factor formula by integer polynomial
cross-multiplication, and against direct highest-weight Weyl products.
"""
from pathlib import Path
from fractions import Fraction as F
from math import comb,factorial,lcm
from itertools import product
import json

if not __debug__:raise RuntimeError('Exact audit requires Python without -O.')


def trim(p):
    p=list(p)
    while len(p)>1 and p[-1]==0:p.pop()
    return tuple(p)
def add(a,b):return trim([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def scale(a,k):return trim([x*k for x in a])
def mul(a,b):
    p=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):p[i+j]+=x*y
    return trim(p)
def factors(offsets):
    p=(1,)
    for offset in offsets:p=mul(p,(offset,1))
    return p
def shifted(p,s=8):
    out=[0]*len(p)
    for n,c in enumerate(p):
        for k in range(n+1):out[k]+=c*comb(n,k)*s**(n-k)
    return trim(out)
def evaluate(p,D):return sum(c*D**i for i,c in enumerate(p))


PARTS={0:[()],1:[(1,)],2:[(2,),(1,1)],3:[(3,),(2,1),(1,1,1)]}
EXPLICIT={}
def register(lam,mu,offsets,den):
    EXPLICIT[lam,mu]=(factors(offsets),den)
    EXPLICIT[mu,lam]=(factors(offsets),den)
register((),(),[],1)
register((1,),(1,),[-1,1],1)
register((2,),(2,),[0,0,-1,3],4)
register((2,),(1,1),[-2,-1,1,2],4)
register((1,1),(1,1),[0,0,-3,1],4)
register((3,),(3,),[0,0,-1,1,1,5],36)
register((3,),(2,1),[0,0,-2,-1,2,4],18)
register((3,),(1,1,1),[-3,-2,-1,1,2,3],36)
register((2,1),(2,1),[-3,-1,-1,1,1,3],9)
register((2,1),(1,1,1),[0,0,-4,-2,1,2],18)
register((1,1,1),(1,1,1),[0,0,-5,-1,-1,1],36)


def hooks(lam):
    return [row-j+1+sum(z>=j for z in lam[i:])
            for i,row in enumerate(lam,1) for j in range(1,row+1)]
def symmetric_group_dimension(lam):
    h=1
    for v in hooks(lam):h*=v
    return factorial(sum(lam))//h


def symbolic_weyl(lam,mu):
    num=(1,);den=(1,)
    for shape in (lam,mu):
        for i,row in enumerate(shape,1):
            for j in range(1,row+1):
                hook=row-j+1+sum(z>=j for z in shape[i:])
                num=mul(num,(j-i,1));den=scale(den,hook)
    for i,a in enumerate(lam,1):
        for j,b in enumerate(mu,1):
            t=1-i-j
            num=mul(num,factors([t,t+a+b]));den=mul(den,factors([t+a,t+b]))
    return num,den


def direct_weyl(lam,mu,D):
    weight=lam+(0,)*(D-len(lam)-len(mu))+tuple(-x for x in reversed(mu))
    result=F(1)
    for i in range(D):
        for j in range(i+1,D):result*=F(weight[i]-weight[j]+j-i,j-i)
    return result


def main():
    rows=[];physical=(0,);commutant=0
    for k in range(4):
        r=3-k
        for lam,mu in product(PARTS[r],repeat=2):
            polynomial,den=EXPLICIT[lam,mu]
            wn,wd=symbolic_weyl(lam,mu)
            assert scale(wn,den)==mul(polynomial,wd),('Weyl identity',lam,mu)
            for D in (8,9,16):
                assert direct_weyl(lam,mu,D)==F(evaluate(polynomial,D),den)
            multiplicity=comb(3,k)**2*factorial(k)*symmetric_group_dimension(lam)*symmetric_group_dimension(mu)
            commutant+=multiplicity**2
            physical=add(physical,scale(polynomial,multiplicity*(36//den)))
            row=dict(k=k,lambda_partition=lam,mu_partition=mu,multiplicity=multiplicity,
                     dimension_numerator_coefficients=list(polynomial),dimension_denominator=den)
            if r in (2,3):
                minimum,mden=EXPLICIT[PARTS[r][-1],PARTS[r][-1]]
                difference=add(scale(polynomial,mden),scale(minimum,-den))
                positive=shifted(difference)
                assert all(x>=0 for x in positive)
                row['dimension_minus_minimum_shifted_numerator']=list(positive)
            rows.append(row)
    expected=(0,0,0,0,0,0,36)
    assert physical==expected and commutant==720 and len(rows)==15
    lower=[]
    for r,divisor in ((2,8),(3,128)):
        polynomial,den=EXPLICIT[PARTS[r][-1],PARTS[r][-1]]
        monomial=(0,)*(2*r)+(1,)
        numerator=add(scale(polynomial,divisor),scale(monomial,-den))
        positive=shifted(numerator)
        assert all(x>=0 for x in positive) and positive[0]>0
        lower.append(dict(degree=2*r,bound=f'D^{2*r}/{divisor}',
            shifted_cleared_numerator=list(positive),all_coefficients_nonnegative=True))
    out=dict(status='passed',arithmetic='stdlib exact integer polynomial and Fraction products',
        symbolic_weyl_identities=15,direct_highest_weight_checks=45,
        physical_dimension_identity='sum multiplicity*irrep_dimension=D^6 exactly',
        commutant_dimension=commutant,sectors=rows,lower_bounds=lower,
        scope='dimension formulas/completeness arithmetic; does NOT certify projection weights or fidelity remainder norm')
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2))
    print(json.dumps({k:v for k,v in out.items() if k not in ('sectors',)},indent=2))


if __name__=='__main__':main()
