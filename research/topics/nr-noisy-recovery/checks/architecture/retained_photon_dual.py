"""Exact, optimizer-free certificate for the retained-photon two-CZ dual.

Uses only the standard library. Coefficients lie in Q(sqrt(2),i), and
four real formal variables obey sa^2=1-ca^2, sb^2=1-cb^2. Factors of
sqrt(3) are cleared before multiplication. This checks the displayed
matrix and polynomial identities; the Gram positivity, unitary dilation,
and physical-access scope are analytic arguments in the accompanying proof.
Import is silent; verify() returns a report and writes no files.
"""

from fractions import Fraction as F
from math import comb
import json

if not __debug__:
    raise SystemExit("Run without -O: exact replay uses assertions.")


class E:
    """(r+s sqrt(2)) + i(u+v sqrt(2)), exactly."""
    def __init__(self, r=0, s=0, u=0, v=0):
        if isinstance(r, E):
            self.c = r.c
        else:
            self.c = tuple(F(x) for x in (r, s, u, v))

    def __add__(self, other):
        if isinstance(other, P):
            return NotImplemented
        other = E(other)
        return E(*(x+y for x,y in zip(self.c,other.c)))
    __radd__ = __add__

    def __neg__(self):
        return E(*(-x for x in self.c))

    def __sub__(self, other):
        if isinstance(other, P):
            return NotImplemented
        return self + (-E(other))

    def __rsub__(self, other):
        return E(other) - self

    def __mul__(self, other):
        if isinstance(other, P):
            return NotImplemented
        other = E(other)
        a,b,c,d = self.c
        e,f,g,h = other.c
        return E(a*e+2*b*f-c*g-2*d*h,
                 a*f+b*e-c*h-d*g,
                 a*g+2*b*h+c*e+2*d*f,
                 a*h+b*g+c*f+d*e)
    __rmul__ = __mul__

    def __truediv__(self, value):
        value = F(value)
        return E(*(x/value for x in self.c))

    def conj(self):
        a,b,c,d = self.c
        return E(a,b,-c,-d)

    def __eq__(self, other):
        if isinstance(other, P):
            return NotImplemented
        return self.c == E(other).c

    def __bool__(self):
        return any(self.c)


class P:
    """A polynomial in (ca,sa,cb,sb), with exact E coefficients."""
    def __init__(self, value=0):
        if isinstance(value,P):
            self.d = value.d.copy()
        elif isinstance(value,dict):
            self.d = {k:E(v) for k,v in value.items() if E(v)}
        else:
            self.d = {(0,0,0,0):E(value)} if E(value) else {}

    def __add__(self, other):
        out = self.d.copy()
        for k,v in P(other).d.items():
            out[k] = out.get(k,E()) + v
        return P(out)
    __radd__ = __add__

    def __neg__(self):
        return P({k:-v for k,v in self.d.items()})

    def __sub__(self, other):
        return self + (-P(other))

    def __rsub__(self, other):
        return P(other) - self

    def __mul__(self, other):
        out = {}
        for k,v in self.d.items():
            for m,w in P(other).d.items():
                z = tuple(a+b for a,b in zip(k,m))
                out[z] = out.get(z,E()) + v*w
        return P(out)
    __rmul__ = __mul__

    def __truediv__(self, value):
        return P({k:v/value for k,v in self.d.items()})

    def conj(self):
        return P({k:v.conj() for k,v in self.d.items()})

    def reduced(self):
        out = {}
        for (ia,ja,ib,jb),v in self.d.items():
            ka,kb = ja//2,jb//2
            for ua in range(ka+1):
                for ub in range(kb+1):
                    key = ia+2*ua,ja%2,ib+2*ub,jb%2
                    factor = (-1)**(ua+ub)*comb(ka,ua)*comb(kb,ub)
                    out[key] = out.get(key,E()) + v*factor
        return P(out)

    def __eq__(self, other):
        return self.reduced().d == P(other).reduced().d


def var(k):
    powers = [0]*4
    powers[k] = 1
    return P({tuple(powers):E(1)})


def mat(rows):
    return [[P(x) for x in row] for row in rows]


def eye(n):
    return mat([[int(i==j) for j in range(n)] for i in range(n)])


def add(A,B):
    return [[a+b for a,b in zip(ar,br)] for ar,br in zip(A,B)]


def scale(A,x):
    return [[a*x for a in row] for row in A]


def mul(A,B):
    return [[sum((A[i][k]*B[k][j] for k in range(len(B))),P())
             for j in range(len(B[0]))] for i in range(len(A))]


def adj(A):
    return [[A[j][i].conj() for j in range(len(A))] for i in range(len(A[0]))]


def tensor(A,B):
    return [[a*b for a in ar for b in br] for ar in A for br in B]


def block(A,B,C,D):
    return [ar+br for ar,br in zip(A,B)] + [cr+dr for cr,dr in zip(C,D)]


def trace(A):
    return sum((A[i][i] for i in range(len(A))),P())


def equal(A,B):
    return len(A)==len(B) and all(a==b for ar,br in zip(A,B) for a,b in zip(ar,br))


def subblock(A,i,j):
    return [row[2*j:2*j+2] for row in A[2*i:2*i+2]]


def verify():
    """Check the exact identities and return their scoped certificate report."""
    i = E(0,0,1,0)
    rt2 = E(0,1)
    I = eye(2)
    X = mat([[0,1],[1,0]])
    Y = mat([[0,-i],[i,0]])
    Z = mat([[1,0],[0,-1]])
    O = mat([[0,0],[0,0]])
    I4 = eye(4)
    for pauli in (X,Y,Z):
        assert equal(mul(pauli,pauli),I)
        assert equal(adj(pauli),pauli)
    assert equal(add(mul(X,Z),mul(Z,X)),O)
    ca,sa,cb,sb = (var(k) for k in range(4))
    q,r = ca*ca,cb*cb
    a0,b0 = (E(2)+rt2)/2,(E(2)-rt2)/2
    assert a0*a0+b0*b0 == 3 and 2*a0*b0 == 1

    # Original-basis Gram-factor squares: each factor K is Ktilde/sqrt(3).
    KA = add(scale(I4,a0),scale(tensor(Y,add(scale(I,-sa),scale(Z,2*ca))),b0))
    KB = add(scale(I4,a0),scale(tensor(Y,add(scale(I,sb),scale(X,-2*cb))),b0))
    assert equal(KA,adj(KA)) and equal(KB,adj(KB))
    HA = add(scale(I,1+b0*b0*q),scale(Z,-F(4,3)*b0*b0*sa*ca))
    HB = add(scale(I,1+b0*b0*r),scale(X,-F(4,3)*b0*b0*sb*cb))
    for factor,H in ((KA,HA),(KB,HB)):
        square = scale(mul(factor,factor),F(1,3))
        assert equal(subblock(square,0,0),H)
        assert equal(subblock(square,1,1),H)
    D = trace(HA)+trace(HB)
    assert D == 4+2*b0*b0*(q+r)

    UL = block(I,O,O,scale(X,i))
    UR = block(I,O,O,scale(Z,i))
    assert equal(mul(adj(UL),UL),I4) and equal(mul(adj(UR),UR),I4)
    C0 = block(I,scale(Z,-i),scale(X,-i),O)  # actual C0 is this/sqrt(3)
    F0 = mat([[1,1],[1,0]])
    O0 = add(Z,scale(X,rt2))  # actual O is this/sqrt(3)
    assert equal(mul(O0,O0),scale(I,3))
    assert equal(mul(mul(UL,C0),UR),tensor(F0,I))
    V0 = mul(mul(adj(UL),tensor(O0,I)),adj(UR))
    assert equal(mul(adj(V0),V0),scale(I4,3))

    # Exact Pauli conjugation by exp(i alpha tauX); identities are modulo
    # ca^2+sa^2=cb^2+sb^2=1, without selecting any angle signs.
    Arot = add(scale(I4,a0),scale(tensor(add(scale(Y,ca),scale(Z,-sa)),
                                        add(scale(I,-sa),scale(Z,2*ca))),b0))
    Brot = add(scale(I4,a0),scale(tensor(add(scale(Y,cb),scale(Z,sb)),
                                        add(scale(I,sb),scale(X,-2*cb))),b0))
    MA = mul(mul(adj(UR),Arot),UR)
    MB = mul(mul(UL,Brot),adj(UL))
    M = lambda x:add(scale(I,a0),scale(add(scale(X,2*x),scale(Z,1-x)),b0))
    Gindex = add(X,scale(Z,2))
    assert equal(MA,add(tensor(M(q),I),scale(tensor(Gindex,Z),-b0*sa*ca)))
    assert equal(MB,add(tensor(M(r),I),scale(tensor(Gindex,X),-b0*sb*cb)))

    # Four cleared sqrt(3) factors produce denominator 9.
    T = trace(mul(mul(mul(O0,M(r)),F0),M(q)))/9
    ell = trace(mul(mul(mul(tensor(O0,I),MB),tensor(F0,I)),MA))/9
    assert ell == 2*T and ell == ell.conj()
    L = (10*rt2-13)/3
    N = (68*rt2-93)/6
    positive_polynomial = P(L)*(q*(1-r)+r*(1-q))+P(N)*q*r
    assert 3*T-D == positive_polynomial
    assert 200>169 and 9248>8649  # L,N positive; q,r are each in [0,1].

    # Exact balanced attainment: actual Cbalanced=Dmat/(2sqrt(3)), t=3/4.
    Dmat = block(add(add(I,X),Z),scale(add(add(I,X),scale(Z,-1)),i),
                 scale(add(add(I,scale(X,-1)),Z),i),add(add(scale(I,-1),X),Z))
    A0,A1 = add(scale(I,F(1,2)),scale(Z,F(1,4))),add(scale(I,F(1,2)),scale(Z,F(-1,4)))
    B0,B1 = add(scale(I,F(1,2)),scale(X,F(1,4))),add(scale(I,F(1,2)),scale(X,F(-1,4)))
    A = block(A0,O,O,A1)
    B = block(B0,O,O,B1)
    Binv = block(add(scale(I,F(8,3)),scale(X,F(-4,3))),O,O,
                 add(scale(I,F(8,3)),scale(X,F(4,3))))
    assert equal(mul(B,Binv),I4)
    assert equal(scale(mul(mul(adj(Dmat),Binv),Dmat),F(3,64)),A)
    assert equal(add(A0,A1),I) and equal(add(B0,B1),I)

    return {
        'status':'PASS',
        'arithmetic':'exact Q(sqrt(2),i) polynomial identities; standard library',
        'phase_relations':'sa^2=1-ca^2; sb^2=1-cb^2',
        'dual_cost':'D=4+6 b^2(q+r), b=(2-sqrt(2))/(2sqrt(3))',
        'cross_overlap':'ell=2T',
        'positive_identity':'3T-D=L[q(1-r)+r(1-q)]+Nqr',
        'positive_coefficients':{'L':'(10sqrt(2)-13)/3','N':'(68sqrt(2)-93)/6'},
        'sharp_amplitude':'3/4','sharp_probability':'9/16',
        'attainment':'balanced phases; exact zero Schur complement',
        'scope':'One exact fine success flag; fixed CZ order, arbitrary clean photonic ancilla and declared spin Z phases. Gram positivity, sector-compatible Halmos completion and reference extension are proved analytically. No optimizer, several-corrected-flag bound, arbitrary-spin-control bound, hardware claim or priority claim.'
    }


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
