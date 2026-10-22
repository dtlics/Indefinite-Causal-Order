"""Independent integer-polynomial replay of the CORRECT acceptance dual.

No SymPy, NumPy, Boolean flags, irreps, or search caches are used. Rebuilds
Delta from canonical moments and ALL symbolic Gram equations, reconstructs
the physical singlet/traceless-cup Gram forms, expands all principal minors
at D=8+x, and checks the correctly directed tester causal-prefix equalities.
"""
from pathlib import Path
if not __debug__:
    raise RuntimeError('Exact certificate replay requires Python without -O; assertions are proof checks.')
from itertools import combinations,permutations,product
from math import comb
import json
import sys

sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'algebra'))

from brauer_exact_replay import ExactBrauerAlgebra as Algebra
from brauer_objective import II,XX,YY,_mmul,_transpose,_gadd,_gmul,_mconj,ONE

HERE=Path(__file__).resolve().parent
SHARP=True


class Poly:
    def __init__(self,c=0):
        if isinstance(c,Poly):self.c=c.c;return
        if isinstance(c,int):c=(c,)
        c=list(c)
        while len(c)>1 and c[-1]==0:c.pop()
        self.c=tuple(c or [0])
    def __add__(self,o):
        o=Poly(o);n=max(len(self.c),len(o.c))
        return Poly([(self.c[i] if i<len(self.c) else 0)+(o.c[i] if i<len(o.c) else 0) for i in range(n)])
    __radd__=__add__
    def __neg__(self):return Poly([-x for x in self.c])
    def __sub__(self,o):return self+-Poly(o)
    def __rsub__(self,o):return Poly(o)+-self
    def __mul__(self,o):
        o=Poly(o);c=[0]*(len(self.c)+len(o.c)-1)
        for i,a in enumerate(self.c):
            for j,b in enumerate(o.c):c[i+j]+=a*b
        return Poly(c)
    __rmul__=__mul__
    def __pow__(self,k):
        assert type(k)is int and k>=0
        out=Poly(1)
        for _ in range(k):out=out*self
        return out
    def __eq__(self,o):return self.c==Poly(o).c
    def shifted(self,shift):
        result=[0]*len(self.c)
        for n,c in enumerate(self.c):
            for k in range(n+1):result[k]+=c*comb(n,k)*shift**(n-k)
        return Poly(result)


D=Poly((0,1));DEN=(D**2-1)*(D**2-9)
ALG=Algebra((1,-1,1,-1))
A_INDICES={0,3,4,7,8,11,12,15,16,19,20,23}
CUPS=[(0,1),(0,3),(2,1),(2,3)]
SING=[[(0,1),(2,3)],[(0,3),(2,1)]]
GOOD_CUPS=[ALG.index_by_permutation[p] for p in ((1,0,2,3),(3,1,2,0),(0,1,3,2))]


class Union:
    def __init__(self,n):self.p=list(range(n))
    def root(self,i):
        while self.p[i]!=i:self.p[i]=self.p[self.p[i]];i=self.p[i]
        return i
    def join(self,a,b):self.p[self.root(a)]=self.root(b)


def physical_gram_entry(partner,r,s,sector):
    u=Union(8)
    for a,b in enumerate(partner):
        if a<b:u.join(a,b)
    pins=[]
    for shift,label in ((0,r),(4,s)):
        pairs=SING[label] if sector=='singlet' else [CUPS[label]]
        for a,b in pairs:u.join(shift+a,shift+b)
        if sector=='adjoint':
            cup=CUPS[label]
            plus=next(i for i in (0,2) if i not in cup)
            minus=next(i for i in (1,3) if i not in cup)
            pins.extend(((shift+plus,0),(shift+minus,1)))
    fixed={}
    for vertex,value in pins:
        root=u.root(vertex)
        if root in fixed and fixed[root]!=value:return Poly(0)
        fixed[root]=value
    exponent=len({u.root(i) for i in range(8)})-len(fixed)
    return D**exponent


def moment(on_first,on_second):
    edges=[];erasures=0
    for incoming,outgoing,on,mat in ((0,1,on_first,XX),(2,3,on_second,YY)):
        if on:edges.extend(((4+outgoing,4+incoming,_mconj(mat)),(outgoing,incoming,mat)))
        else:
            edges.extend(((incoming,4+incoming,II),(outgoing,4+outgoing,II)));erasures+=1
    answers=[]
    for partner in ALG.pairs:
        all_edges=[(i,j,II) for i,j in enumerate(partner) if i<j]+edges
        adjacent=[[] for _ in range(8)]
        for k,(u,v,mat) in enumerate(all_edges):adjacent[u].append(k);adjacent[v].append(k)
        assert all(len(row)==2 for row in adjacent)
        visited=set();answer=ONE;cycles=0
        for start in range(8):
            if all(k in visited for k in adjacent[start]):continue
            current=start;matrix=II;cycles+=1
            while True:
                edge=next(k for k in adjacent[current] if k not in visited);visited.add(edge)
                u,v,mat=all_edges[edge]
                if current==u:matrix=_mmul(matrix,mat);current=v
                else:matrix=_mmul(matrix,_transpose(mat));current=u
                if current==start:break
            tr=_gadd(matrix[0],matrix[3])
            assert tr[0]%2==tr[1]%2==0
            answer=_gmul(answer,(tr[0]//2,tr[1]//2))
        assert answer[1]==0 and len(visited)==8
        # Return D^2 times the physical moment, clearing even the double-
        # replacement Laurent term without introducing rational functions.
        answers.append(answer[0]*D**(cycles-erasures+2) if answer[0] else Poly(0))
    return answers


def delta_numerators(which):
    # All three Delta coefficients have common denominator D^2 DEN.
    ci={6,17,22} if which=='first' else {1,17,22}
    if which=='double':ci={6,17,22}
    out=[D*(D if i in A_INDICES else (-(D**2-6) if i in ci else Poly(-3))) for i in range(24)]
    if which=='double':
        out[ALG.identity]+=D**2-9
        out[ALG.index_by_permutation[(0,1,3,2)]]-=D*(D**2-9)
    return out


def cycle_count(p):
    seen=set();count=0
    for i in range(len(p)):
        if i in seen:continue
        count+=1;j=i
        while j not in seen:seen.add(j);j=p[j]
    return count


def objective_identity(which):
    ideal=moment(True,True)
    noisy=moment(which not in ('first','double'),which not in ('second','double'))
    f=[x-y for x,y in zip(ideal,noisy)];cn=delta_numerators(which)
    assert all(cn[i]==cn[ALG.star[i]] for i in range(24))
    for i,p in enumerate(ALG.permutations):
        inv=tuple(p.index(k) for k in range(4));lhs=Poly(0)
        for j,q in enumerate(ALG.permutations):
            lhs+=D**cycle_count(tuple(inv[q[k]] for k in range(4)))*cn[j]
        assert lhs==DEN*f[ALG.star[i]],('symbolic Gram identity',which,i)
    return cn


def scaled_slack(which,sign):
    # Frozen sharp positive denominator 10D^3 DEN, for P+sign*Delta/2.
    c=[Poly(0) for _ in range(24)]
    if SHARP:
        c[ALG.identity]=8*DEN
        for q,w in zip(GOOD_CUPS,(1,5,1)):c[q]+=w*D*DEN
        factor=5
    else:
        c[ALG.identity]=3*DEN
        for q in GOOD_CUPS:c[q]+=2*D*DEN
        factor=2
    return [v+sign*factor*D*z for v,z in zip(c,delta_numerators(which))]


def determinant(matrix):
    n=len(matrix);result=Poly(0)
    for p in permutations(range(n)):
        inversions=sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
        term=Poly((-1)**inversions)
        for i in range(n):term*=matrix[i][p[i]]
        result+=term
    return result


def coefficient_trace(algebra,coeff,wire):
    target,indices,loops=algebra.partial_trace_map(wire)
    out=[Poly(0) for _ in range(target.size)]
    for c,i,k in zip(coeff,indices,loops):out[i]+=c*D**k
    return target,out


def coefficient_insert(algebra,coeff,position,sign):
    target,indices=algebra.insert_identity_map(position,sign)
    out=[Poly(0) for _ in range(target.size)]
    for c,i in zip(coeff,indices):out[i]+=c
    return target,out


def causal_identities(which):
    # H=P+Delta/2, scaled by the frozen sharp L=10D^3 DEN.
    c=scaled_slack(which,1);a3,tr_h=coefficient_trace(ALG,c,3)
    z=Algebra((1,-1));Q=z.index_by_permutation[(1,0)]
    # Sharp Z_P=7I/(5D^2)+Q01/(10D). Add R/2 for first erasure,
    # R=(I-DQ01)/(D(D^2-1)); its output partial trace is zero.
    zn=[Poly(0) for _ in range(2)]
    zn[z.identity]=(14 if SHARP else 7)*D*DEN
    zn[Q]=(1 if SHARP else 2)*D**2*DEN
    if which in ('first','double'):
        zn[z.identity]+=(5 if SHARP else 2)*D**2*(D**2-9)
        zn[Q]-=(5 if SHARP else 2)*D**3*(D**2-9)
    _,zi=coefficient_insert(z,zn,2,1)
    assert tr_h==zi,('correct tester first prefix',which)
    a1,tr_z=coefficient_trace(z,zn,1)
    assert tr_z==[(15 if SHARP else 9)*D**2*DEN],('correct tester final prefix',which)
    # Right side is L*3/(2D). This checks the scalar cost, with no missing D.
    return True


def main():
    source='acceptance_correct_dual_sharp_certificate.json' if SHARP else 'acceptance_correct_dual_independent_certificate.json'
    cert=json.loads((HERE/source).read_text())
    records={(r['which'],r['sign'],r['sector']):r for r in cert['rows']}
    reports=[];count=0
    for which in ('first','second','double'):
        objective_identity(which);causal_identities(which)
        for sign in (-1,1):
            coeff=scaled_slack(which,sign)
            for sector,n in (('singlet',2),('adjoint',4)):
                matrix=[[sum((c*physical_gram_entry(p,r,s,sector) for c,p in zip(coeff,ALG.pairs)),Poly(0))
                         for s in range(n)] for r in range(n)]
                assert matrix==list(map(list,zip(*matrix)))
                supplied={tuple(t['indices']):t for t in records[which,sign,sector]['principal_minors']}
                expected_indices={ix for k in range(1,n+1) for ix in combinations(range(n),k)}
                assert set(supplied)==expected_indices
                for ix in sorted(expected_indices,key=lambda z:(len(z),z)):
                    det=determinant([[matrix[r][s] for s in ix] for r in ix])
                    shifted=det.shifted(8)
                    assert all(c>=0 for c in shifted.c) and shifted.c[0]>0,(which,sign,sector,ix)
                    assert list(reversed(shifted.c))==[int(x) for x in supplied[ix]['shifted_coefficients']]
                    count+=1
                reports.append(dict(which=which,sign=sign,sector=sector,
                    minors=len(expected_indices),all_shifted_integer_coefficients_nonnegative=True,
                    all_constant_coefficients_strictly_positive=True))
    bulk_count=0
    supplied={(b['which'],b['sign'],b['s'],b['t']):b for b in cert['bulk']}
    for which in ('single','double'):
        for sign in (-1,1):
            for s,t in product((-1,1),repeat=2):
                factor=5 if SHARP else 2
                polynomial=(8 if SHARP else 3)*DEN+sign*(factor*D**3*(1+s*t)-
                    3*factor*D**2*(s+t)+(factor*D*(D**2-9) if which=='double' else 0))
                shifted=polynomial.shifted(8)
                assert all(c>=0 for c in shifted.c) and shifted.c[0]>0
                assert list(reversed(shifted.c))==[int(x) for x in supplied[which,sign,s,t]['shifted_coefficients']]
                bulk_count+=1
    out=dict(status='passed',arithmetic='Python standard library; integer polynomial arrays only',
        objective_symbolic_Gram_equations=72,principal_minors_rebuilt=count,bulk_characters_rebuilt=bulk_count,
        correct_causal_prefix_equalities='verified all3patterns; scalar tester cost'+('3/(2D)' if SHARP else '9/(4D)'),
        denominator=('10' if SHARP else '4')+' D^3 (D^2-1)(D^2-9)>0 for D>=8',
        certificate_flags_trusted=False,rows=reports,
        scope='correct adaptive acceptance tester dual; physical-sector completeness audited separately')
    target=HERE/('acceptance_correct_sharp_stdlib_replay.json' if SHARP else 'acceptance_correct_stdlib_replay.json')
    target.write_text(json.dumps(out,indent=2))
    print(json.dumps(out,indent=2))


if __name__=='__main__':main()
