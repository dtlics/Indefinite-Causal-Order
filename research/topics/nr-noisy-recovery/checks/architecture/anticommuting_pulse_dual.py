"""Exact replay of a uniform ordinary two-query causal dual.

Only Python's standard library is needed.  The stored witness belongs to
Q(sqrt(2)); no numerical solver, floating point tolerance, sampled angle,
or external scientific package participates in verification.
"""
from fractions import Fraction as F
from pathlib import Path
from itertools import product
import json
import hashlib

HERE = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


class R:
    """The ordered field Q(sqrt(2)), with exact rational coefficients."""
    def __init__(self, a=0, b=0):
        if isinstance(a, R):
            self.a, self.b = a.a, a.b
        else:
            self.a, self.b = F(a), F(b)
    def __add__(self, x):
        x = R(x)
        return R(self.a+x.a, self.b+x.b)
    __radd__ = __add__
    def __neg__(self):
        return R(-self.a, -self.b)
    def __sub__(self, x):
        return self+-R(x)
    def __rsub__(self, x):
        return R(x)+-self
    def __mul__(self, x):
        x = R(x)
        return R(self.a*x.a+2*self.b*x.b, self.a*x.b+self.b*x.a)
    __rmul__ = __mul__
    def __truediv__(self, x):
        x = R(x)
        den = x.a*x.a-2*x.b*x.b
        require(den != 0, 'nonzero field denominator')
        return self*R(x.a/den, -x.b/den)
    def __eq__(self, x):
        x = R(x)
        return self.a == x.a and self.b == x.b
    def sign(self):
        if not self.b:
            return (self.a > 0)-(self.a < 0)
        if not self.a:
            return (self.b > 0)-(self.b < 0)
        if self.a > 0 and self.b > 0:
            return 1
        if self.a < 0 and self.b < 0:
            return -1
        d = self.a*self.a-2*self.b*self.b
        return ((d > 0)-(d < 0))*(1 if self.a > 0 else -1)
    def encode(self):
        return [str(self.a), str(self.b)]


def zero(n, m=None):
    return [[F(0) for _ in range(n if m is None else m)] for _ in range(n)]


def identity(n, scale=F(1)):
    return [[scale if i == j else F(0) for j in range(n)] for i in range(n)]


def unlower(values, n, convert=F):
    require(len(values) == n*(n+1)//2, 'lower triangle length')
    out = zero(n)
    k = 0
    for i in range(n):
        for j in range(i+1):
            out[i][j] = out[j][i] = convert(values[k])
            k += 1
    return out


def lower(matrix, convert=str):
    return [convert(matrix[i][j]) for i in range(len(matrix)) for j in range(i+1)]


def subtract(a, b):
    return [[x-y for x,y in zip(row,other)] for row,other in zip(a,b)]


def trace_first(a):
    n = len(a)//2
    return [[a[i][j]+a[n+i][n+j] for j in range(n)] for i in range(n)]


def kron_identity(a):
    n = len(a)
    return [[a[i%n][j%n] if i//n == j//n else F(0)
             for j in range(2*n)] for i in range(2*n)]


def exact_positive_definite(a, label):
    """Exact LDL^T elimination, returning positive diagonal pivot count."""
    n = len(a)
    require(all(a[i][j] == a[j][i] for i in range(n) for j in range(n)),
            label+' symmetric')
    a = [row[:] for row in a]
    for k in range(n):
        pivot = a[k][k]
        positive = pivot.sign() > 0 if isinstance(pivot,R) else pivot > 0
        require(positive, label+' exact positive pivot '+str(k))
        for i in range(k+1,n):
            for j in range(i,n):
                value = a[i][j]-a[i][k]*a[j][k]/pivot
                a[i][j] = a[j][i] = value
    return n


def permutation(n, p):
    a = zero(2**n)
    for i in range(2**n):
        bits = [(i>>(n-1-k))&1 for k in range(n)]
        j = sum(bits[p[k]]<<(n-1-k) for k in range(n))
        a[j][i] = 1
    return a


def physical_permutation_basis(n, p):
    """Conjugate P+P.T by sigma_y on positions 0,2,4,... ."""
    pmat = permutation(n,p)
    mask = sum(1<<(n-1-k) for k in range(0,n,2))
    signs = [(-1)**((i&mask).bit_count()) for i in range(2**n)]
    return [[signs[i]*signs[j]*(pmat[i^mask][j^mask]+pmat[j^mask][i^mask])
             for j in range(2**n)] for i in range(2**n)]


# Gaussian-integer Pauli entries represented as (real, imaginary).
P = [((1,0),(0,0),(0,0),(1,0)),
     ((0,0),(1,0),(1,0),(0,0)),
     ((0,0),(0,-1),(0,1),(0,0)),
     ((1,0),(0,0),(0,0),(-1,0))]


def cmul(a,b):
    return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])


def conjugate(a):
    return (a[0],-a[1])


def pair_tensor(external,bquery,aquery):
    out = [(0,0)]*64
    for f,p,bo,bi,ao,ai in product(range(2),repeat=6):
        index = ((((f*2+bo)*2+bi)*2+ao)*2+ai)*2+p
        out[index] = cmul(cmul(external[2*f+p],bquery[2*bo+bi]),aquery[2*ao+ai])
    return out


def add_vectors(vectors):
    return [(sum(v[i][0] for v in vectors),sum(v[i][1] for v in vectors))
            for i in range(64)]


def support_vectors():
    ei = pair_tensor(P[0],P[0],P[0])
    eb = add_vectors([pair_tensor(P[k],tuple(map(conjugate,P[k])),P[0]) for k in (1,2,3)])
    ea = add_vectors([pair_tensor(P[k],P[0],tuple(map(conjugate,P[k]))) for k in (1,2,3)])
    ns = [add_vectors([pair_tensor(P[o],tuple(map(conjugate,P[k])),tuple(map(conjugate,P[k])))
                       for k in (1,2,3)]) for o in range(4)]
    return [ei,eb,ea],ns


def literal_link(vector,bquery,aquery):
    out = []
    for f,p in product(range(2),repeat=2):
        real = 0; imag = 0
        for bo,bi,ao,ai in product(range(2),repeat=4):
            index = ((((f*2+bo)*2+bi)*2+ao)*2+ai)*2+p
            value = cmul(cmul(vector[index],bquery[2*bo+bi]),aquery[2*ao+ai])
            real += value[0]; imag += value[1]
        out.append((real,imag))
    return tuple(out)


def literal_link_guards():
    """Derive the support normalization from explicit Pauli contractions."""
    e,ns = support_vectors()
    empty = ((0,0),)*4
    def times_four(pauli):
        return tuple((4*r,4*i) for r,i in pauli)
    for mu,nu in product(range(4),repeat=2):
        expected = [times_four(P[0]) if mu == nu == 0 else empty,
                    times_four(P[mu]) if mu != 0 and nu == 0 else empty,
                    times_four(P[nu]) if mu == 0 and nu != 0 else empty]
        for vector,target in zip(e,expected):
            require(literal_link(vector,P[mu],P[nu]) == target,
                    'literal proper Pauli contraction')
        for o,vector in enumerate(ns):
            target = times_four(P[o]) if mu == nu and mu != 0 else empty
            require(literal_link(vector,P[mu],P[nu]) == target,
                    'literal invisible Pauli contraction')
    # Each proper contribution has the same formal pulse monomial
    # cA*sA*cB*sB.  The literal contractions above give factor4, while
    # the vector weights are (1/sqrt(2),1/2,1/2), exactly the target's
    # (I,-iB,-iA) coefficients. Hence K(E')=4cA*sA*cB*sB U.
    target = [R(0,F(1,2)),R(F(1,2)),R(F(1,2))]
    linked = [4*value for value in target]
    amplitude = linked[0]/target[0]
    require(all(value == amplitude*weight for value,weight in zip(linked,target)),
            'common proper target amplitude')
    require(amplitude == 4 and amplitude*amplitude == 16,
            'proper probability objective factor16')
    return amplitude*amplitude


def inner(left,y,right):
    """left^dagger (I_F tensor y) right, as a Gaussian-rational pair."""
    real = F(0); imag = F(0)
    for f in range(2):
        for i in range(32):
            li = conjugate(left[32*f+i])
            if li == (0,0):
                continue
            for j in range(32):
                if y[i][j] and right[32*f+j] != (0,0):
                    prod = cmul(li,right[32*f+j])
                    real += prod[0]*y[i][j]
                    imag += prod[1]*y[i][j]
    return real,imag


def add_poly(a, key, value):
    a[key] = a.get(key,R(0))+value


def multiply(a,b):
    out = {}
    for (i,j),v in a.items():
        for (k,l),w in b.items():
            add_poly(out,(i+k,j+l),v*w)
    return out


AT = [(1,0),(0,1),(1,1),(2,0),(0,2),(2,1),(1,2),(2,2)]
AB = [(0,0),(1,0),(0,1),(1,1)]


def targets(y):
    objective_factor = literal_link_guards()
    e,ns = support_vectors()
    h = [[inner(ei,y,ej) for ej in e] for ei in e]
    hh = [inner(ei,y,ns[0]) for ei in e]
    nn = inner(ns[0],y,ns[0])
    require(all(v[1] == 0 for row in h for v in row)
            and all(v[1] == 0 for v in hh) and nn[1] == 0,
            'singlet compression real')
    require(all(inner(v,y,n) == (0,0) for v in e+[ns[0]] for n in ns[1:]),
            'singlet/triplet compression vanishes exactly')
    h = [[v[0] for v in row] for row in h]
    hh = [v[0] for v in hh]; nn = nn[0]
    d = {(0,0):R(1),(2,0):R(1),(0,2):R(1),(2,2):R(1)}
    wp = [{(1,1):R(0,F(1,2))},{(1,0):R(F(1,2))},{(0,1):R(F(1,2))}]
    top = {}; off = {}
    for i in range(3):
        for j in range(3):
            for key,value in multiply(d,multiply(wp[i],wp[j])).items():
                add_poly(top,key,value*h[i][j])
        for key,value in multiply(d,wp[i]).items():
            add_poly(off,key,value*hh[i])
    add_poly(top,(2,2),-objective_factor)
    bottom = {key:value*nn for key,value in d.items()}
    return top,off,bottom


def gram(q,rows,cols,ro,co):
    out = {}
    for i,(a,b) in enumerate(rows):
        for j,(c,d) in enumerate(cols):
            add_poly(out,(a+c,b+d),q[ro+i][co+j])
    return out


def replay(path=HERE/'anticommuting_pulse_dual.json'):
    from anticommuting_pulse_support import verify as verify_support
    support = verify_support()
    raw = path.read_bytes()
    data = json.loads(raw)
    require(data['bound'] == '13/20', 'specified probability bound')
    y = unlower(data['Y'],32)
    z = unlower(data['Z'],8)
    w = identity(2,F(13,40))
    q = unlower(data['Q'],12,lambda v:R(F(v[0]),F(v[1])))
    first = subtract(kron_identity(z),trace_first(y))
    second = subtract(kron_identity(w),trace_first(z))
    pivots = {
        'Y':exact_positive_definite(y,'Y'),
        'first_causal_slack':exact_positive_definite(first,'first causal slack'),
        'second_causal_slack':exact_positive_definite(second,'second causal slack'),
        'SOS_Gram':exact_positive_definite(q,'SOS Gram')}
    expected = targets(y)
    actual = (gram(q,AT,AT,0,0),gram(q,AT,AB,0,8),gram(q,AB,AB,8,8))
    coefficients = 0
    for a,b in zip(actual,expected):
        for key in set(a)|set(b):
            require(a.get(key,R(0)) == b.get(key,R(0)),
                    'exact polynomial coefficient '+str(key))
            coefficients += 1
    return {'status':'passed','bound':'13/20','positive_LDL_pivots':pivots,
            'necessary_support_rank':support['rank'],
            'literal_Pauli_link_guards':112,
            'exact_matrix_polynomial_coefficients':coefficients,
            'certificate_sha256':hashlib.sha256(raw).hexdigest(),
            'field':'Q(sqrt(2))','floating_point_operations':0,
            'scope':'Uniform causal dual for all real nondegenerate pulse angles; adaptive and boundary inclusion supplied by separate proof.'}


if __name__ == '__main__':
    print(json.dumps(replay(),sort_keys=True))
