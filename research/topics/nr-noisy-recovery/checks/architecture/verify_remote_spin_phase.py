"""Exact finite replay of NR-R11's detected remote-spin phase instruments.

Arithmetic is in Q[exp(i*pi/8)] with standard-library fractions. All spin
matrix-unit coefficients and explicit unequal-module loss histories are
checked. Gaussian rationals also guard the scalar-concurrence determinant
factorization; the rational Bell-yield witness and known-gate compilers are
replayed exactly. A full-rank fixed-marginal reduction and an eight-outcome
helper POVM with local-filter failure accounting guard the arbitrary-helper
assistance proof. Coherent frequency guards also check the constant-control
four-mode normal form and coefficient-independent eigen-source survivor
compiler. The native port, calibration, timing and general scattering/RUS
comparisons remain analytic scope, not certified by finite replay.
Import is silent; no files are written.
"""
from fractions import Fraction as F
from itertools import product
import json

if not __debug__:
    raise SystemExit("Run without -O: exact replay uses assertions.")

ZERO = (F(0),) * 8
ONE = (F(1),) + (F(0),) * 7


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def scale(a, b):
    return tuple(x * b for x in a)


def mul(a, b):
    out = [F(0)] * 8
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    k = i + j
                    out[k % 8] += x * y * (1 if k < 8 else -1)
    return tuple(out)


def root(k):
    k %= 16
    out = [F(0)] * 8
    out[k % 8] = F(1 if k < 8 else -1)
    return tuple(out)


def conj(a):
    out = [F(0)] * 8
    out[0] = a[0]
    for k in range(1, 8):
        out[8 - k] = -a[k]
    return tuple(out)


def sum_field(xs):
    out = ZERO
    for x in xs:
        out = add(out, x)
    return out


def inner(a, b):
    return sum_field(mul(conj(x), y) for x, y in zip(a, b))


INV_SQRT2 = scale(add(root(2), root(-2)), F(1, 2))
COS = scale(add(root(1), root(-1)), F(1, 2))
SIN = mul(scale(add(root(1), scale(root(-1), -1)), F(1, 2)), root(-4))
AB = tuple(product((0, 1), repeat=2))


def sign(z):
    return -1 if z & 1 else 1


def cp_coefficients(k):
    """Every matrix-unit coefficient of the diagonal-Kraus CP map.

    These are all nonzero entries of its full Choi matrix. Equalities
    therefore apply to all spin inputs with arbitrary passive references.
    """
    return tuple(mul(x, conj(y)) for x in k for y in k)


def require_cp(k, desired, weight=F(1)):
    assert cp_coefficients(k) == tuple(scale(z, weight) for z in cp_coefficients(desired))


def switch_carrier(a, b):
    plus = [INV_SQRT2, INV_SQRT2]
    # C0: Z^b X^a |+>; C1: X^a Z^b |+>.
    first = [scale(plus[d ^ a], sign(b * d)) for d in (0, 1)]
    second = [scale(plus[d ^ a], sign(b * (d ^ a))) for d in (0, 1)]
    return [mul(INV_SQRT2, x) for x in first + second]


def replay_switch_and_one_bus():
    count = 0
    states = [switch_carrier(a, b) for a, b in AB]
    for d, s in product((0, 1), (1, -1)):
        ybra = [INV_SQRT2, mul(scale(root(-4), s), INV_SQRT2)]
        k_switch = [sum_field(mul(ybra[c], state[2 * c + d]) for c in (0, 1))
                    for state in states]
        desired = [scale(root(4 * s * a * b), sign(b * d)) for a, b in AB]
        require_cp(k_switch, desired, F(1, 4))
        assert all(mul(k, conj(k)) == scale(ONE, F(1, 4)) for k in k_switch)
        # Ordinary parity-bus outcome y=-s, followed by local spin phases.
        y = -s
        k_ordinary = []
        for a, b in AB:
            state = [COS, scale(SIN, sign(a + b))]
            amp = mul(INV_SQRT2, add(state[0], mul(scale(root(-4), y), state[1])))
            phase = root(y * (sign(a) + sign(b)))
            corrected = mul(phase, amp)
            # Independent fair d coin and raw-switch Z_B^d phase.
            k_ordinary.append(scale(mul(INV_SQRT2, corrected), sign(b * d)))
        assert cp_coefficients(k_switch) == cp_coefficients(k_ordinary)
        count += 1
    return count, states


def bell(a, b):
    out = [ZERO] * 4
    for c in (0, 1):
        d = c ^ a
        out[2 * c + d] = scale(INV_SQRT2, sign(b * d))
    return out


def replay_four_mode():
    betas = [bell(a, b) for a, b in AB]
    assert all(inner(v, w) == (ONE if i == j else ZERO)
               for i, v in enumerate(betas) for j, w in enumerate(betas))
    diagonal_cases = [
        [root(4 * a * b) for a, b in AB],  # CS
        [root(2 * a * b) for a, b in AB],  # controlled pi/4 phase
        [root(1), root(3), root(5), root(7)],
        [root(0), root(4), root(-4), root(8)],
    ]
    count = 0
    for desired in diagonal_cases:
        basis = []
        for u, v in AB:
            m = [sum_field(scale(mul(conj(z), beta[j]), F(sign(u * a + v * b), 2))
                           for (a, b), z, beta in zip(AB, desired, betas))
                 for j in range(4)]
            basis.append(m)
            k = [inner(m, beta) for beta in betas]
            expected_raw = [scale(z, F(sign(u * a + v * b), 2))
                            for (a, b), z in zip(AB, desired)]
            assert k == expected_raw
            corrected = [scale(z, sign(u * a + v * b)) for (a, b), z in zip(AB, k)]
            require_cp(corrected, desired, F(1, 4))
            count += 1
        assert all(inner(v, w) == (ONE if i == j else ZERO)
                   for i, v in enumerate(basis) for j, w in enumerate(basis))
    return count


def replay_loss_boundary(states):
    # No photon readout => no conditional spin phase corrections.
    gs = [[inner(a, b) for b in states] for a in states]
    ordinary = [[COS, scale(SIN, sign(a + b))] for a, b in AB]
    go = [[inner(a, b) for b in ordinary] for a in ordinary]
    assert gs[0][2] == ONE  # |00> versus |10>: b=0, so the switch bus is unchanged.
    assert mul(go[0][2], conj(go[0][2])) == scale(ONE, F(1, 2))
    assert go[0][2] != gs[0][2]
    assert gs[1][3] == ZERO  # b=1 distinguishes a through the order flag.
    # This proves unequal no-click/lost-carrier completions, not superiority.
    return 1


def loss_pol_plus():
    return [INV_SQRT2, INV_SQRT2]


def loss_sx(state, a):
    return [state[d ^ a] for d in (0, 1)]


def loss_sz(state, b):
    return [scale(state[d], (-1) ** (b * d)) for d in (0, 1)]


def loss_sh(state, b):
    if not b:
        return state
    return [mul(INV_SQRT2, add(state[0], state[1])),
            mul(INV_SQRT2, add(state[0], scale(state[1], -1)))]


def loss_gram(states):
    return [[inner(b, a) for b in states] for a in states]


def loss_add_weighted(out, weight, states):
    for i, row in enumerate(loss_gram(states)):
        for j, x in enumerate(row):
            out[i][j] = add(out[i][j], scale(x, weight))


def loss_direct_loss(t0, ta, tb, tl, td):
    gs = [[ZERO] * 4 for _ in range(4)]
    gf = [[ZERO] * 4 for _ in range(4)]
    src = [loss_pol_plus() for _ in AB]
    loss_add_weighted(gs, 1 - t0, src)
    loss_add_weighted(gf, 1 - t0, src)
    # Switch loss records carry the orthogonal route label and are traced.
    for arm in (0, 1):
        first, second = (ta, tb) if arm == 0 else (tb, ta)
        first_states, last_states = [], []
        for a, b in AB:
            if arm == 0:
                one = loss_sx(loss_pol_plus(), a)
                two = loss_sz(one, b)
            else:
                one = loss_sz(loss_pol_plus(), b)
                two = loss_sx(one, a)
            first_states.append(one)
            last_states.append(two)
        loss_add_weighted(gs, t0 * (1 - first) / 2, first_states)
        loss_add_weighted(gs, t0 * first * (1 - tl) / 2, first_states)
        loss_add_weighted(gs, t0 * first * tl * (1 - second) / 2, last_states)
        loss_add_weighted(gs, t0 * first * tl * second * (1 - td) / 2, last_states)
    # Ordinary B-first controlled H, then A controlled X, with same per-module losses.
    first_states = [loss_sh(loss_pol_plus(), b) for a, b in AB]
    last_states = [loss_sx(loss_sh(loss_pol_plus(), b), a) for a, b in AB]
    loss_add_weighted(gf, t0 * (1 - tb), first_states)
    loss_add_weighted(gf, t0 * tb * (1 - tl), first_states)
    loss_add_weighted(gf, t0 * tb * tl * (1 - ta), last_states)
    loss_add_weighted(gf, t0 * tb * tl * ta * (1 - td), last_states)
    return gs, gf


def loss_reject_ratio(t0, ta, tb, tl, td):
    numerator = 1 - t0 + t0 * (1 - ta * tl) / 2
    a = 1 - t0
    b = t0 * (1 - ta * tb * tl * td)
    denominator = add(scale(ONE, a), scale(INV_SQRT2, b))
    if a == b == 0:
        return ONE, numerator, denominator
    norm = a * a - b * b / 2
    assert norm != 0  # rational a/b cannot equal the irrational 1/sqrt2
    ratio = scale(add(scale(ONE, a), scale(INV_SQRT2, -b)), numerator / norm)
    assert mul(ratio, denominator) == scale(ONE, numerator)
    # Exact positivity decomposition for denominator - numerator.
    d = 1 - ta * tl
    e = ta * tl - ta * tb * tl * td
    assert d >= 0 and e >= 0
    difference = scale(add(scale(add(INV_SQRT2, scale(ONE, F(-1, 2))), d),
                           scale(INV_SQRT2, e)), t0)
    assert add(denominator, scale(ONE, -numerator)) == difference
    return ratio, numerator, denominator


def loss_replay_failures():
    count = 0
    for t0, ta, tb, tl, td in product((F(1), F(3, 4)), (F(0), F(1, 2), F(1)),
                                      (F(0), F(1, 2), F(1)), (F(1), F(2, 3)),
                                      (F(1), F(4, 5))):
        success = t0 * ta * tb * tl * td
        fail = 1 - success
        h = 1 - t0 * tb * tl
        gs, gf = loss_direct_loss(t0, ta, tb, tl, td)
        ratio, scross, fcross = loss_reject_ratio(t0, ta, tb, tl, td)
        for i, (a, b) in enumerate(AB):
            for j, (ap, bp) in enumerate(AB):
                if b != bp:
                    assert gs[i][j] == scale(ONE, scross)
                    assert gf[i][j] == fcross
                    assert mul(ratio, gf[i][j]) == gs[i][j]
                    for estimated_r in (F(0), F(1, 2), F(1)):
                        residual = add(scale(gf[i][j], estimated_r),
                                       scale(gs[i][j], -1))
                        assert residual == add(scale(fcross, estimated_r),
                                               scale(ONE, -scross))
                else:
                    expected = fail if b == 0 or a == ap else h
                    assert gs[i][j] == gf[i][j] == scale(ONE, expected)
        count += 1
    # Certain loss before the first visit is a separate exact boundary.
    boundary = (F(0), F(2, 3), F(3, 5), F(4, 5), F(1))
    gs, gf = loss_direct_loss(*boundary)
    assert gs == gf == [[ONE] * 4 for _ in range(4)]
    assert loss_reject_ratio(*boundary)[0] == ONE
    return count + 1


def loss_replay_detected():
    states = [switch_carrier(a, b) for a, b in AB]
    count = 0
    for d, s in product((0, 1), (1, -1)):
        y = -s
        swbra = [INV_SQRT2, mul(scale(root(-4), s), INV_SQRT2)]
        ks = [sum_field(mul(swbra[c], state[2 * c + d]) for c in (0, 1)) for state in states]
        kf = []
        for a, b in AB:
            carrier = loss_sx(loss_sh(loss_pol_plus(), b), a)
            raw = mul(INV_SQRT2, add(carrier[0], mul(scale(root(-4), y), carrier[1])))
            corrected = mul(root(-2 * y * b), raw)
            kf.append(scale(mul(INV_SQRT2, corrected), (-1) ** (b * d)))
        require_cp(kf, ks)
        count += 1
    return count



def cavity_resonant_parameters():
    return ((F(38, 5), F(5, 2), F(23, 10), F(3)),
            (F(38, 5), F(14, 5), F(12, 5), F(3)))


def cavity_coefficients(station, z, zp, polarization):
    g, kappa, kr, gamma = cavity_resonant_parameters()[station]
    gz = g if z == 1 and polarization == 0 else F(0)
    gp = g if zp == 1 and polarization == 0 else F(0)
    den = kappa * gamma + gz * gz
    dep = kappa * gamma + gp * gp
    return (1 - 2 * kr * gamma / den, 1 - 2 * kr * gamma / dep,
            4 * kr * (kappa - kr) * gamma * gamma / (den * dep),
            4 * gz * gp * kr * gamma / (den * dep))


def cavity_matmul(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(2))
                       for j in range(2)) for i in range(2))


def cavity_h_conjugate(m):
    h = ((F(1), F(1)), (F(1), F(-1)))
    return tuple(tuple(x / 2 for x in row)
                 for row in cavity_matmul(cavity_matmul(h, m), h))


def cavity_route(first, label, label_prime):
    """One declared completion: distinct lost station/route/time modes.
    It is not inferred from the reported scalar reflectivities.
    """
    m = ((F(1, 2), F(1, 2)), (F(1, 2), F(1, 2)))
    lost = F(0)
    emitted = F(0)
    for station in (first, 1 - first):
        if station == 0:
            m = cavity_h_conjugate(m)
        coeff = [cavity_coefficients(station, label[station],
                                    label_prime[station], p) for p in range(2)]
        lost += sum(m[p][p] * (coeff[p][2] + coeff[p][3]) for p in range(2))
        emitted += sum(m[p][p] * coeff[p][3] for p in range(2))
        m = tuple(tuple(m[p][q] * coeff[p][0] * coeff[q][1]
                        for q in range(2)) for p in range(2))
        if station == 0:
            m = cavity_h_conjugate(m)
    return sum(m[p][p] for p in range(2)), lost, emitted


def cavity_replay():
    normalization_cases = 0
    for g, kappa, kr, gamma in cavity_resonant_parameters():
        for z, pol, omega in product((0, 1), (0, 1),
                                    (F(-3), F(-1, 3), F(0), F(2, 5), F(7))):
            gg = g if z == 1 and pol == 0 else F(0)
            # Dc*Da+g^2 = u+i*v for resonant nodes at detuning omega.
            u = kappa * gamma - omega * omega + gg * gg
            v = -(kappa + gamma) * omega
            den = u * u + v * v
            # r numerator = (u-2kr gamma)+i(v+2kr omega).
            rn = (u - 2 * kr * gamma)**2 + (v + 2 * kr * omega)**2
            ln = 4 * kr * (kappa - kr) * (gamma * gamma + omega * omega)
            en = 4 * gg * gg * kr * gamma
            assert rn + ln + en == den
            normalization_cases += 1
    reflected = []
    rejected = []
    emission = []
    for label in AB:
        grow, rrow, erow = [], [], []
        for label_prime in AB:
            a = cavity_route(0, label, label_prime)
            b = cavity_route(1, label, label_prime)
            grow.append((a[0] + b[0]) / 2)
            rrow.append((a[1] + b[1]) / 2)
            erow.append((a[2] + b[2]) / 2)
        reflected.append(grow)
        rejected.append(rrow)
        emission.append(erow)
    for k in range(4):
        assert reflected[k][k] + rejected[k][k] == 1
    assert rejected[0][0] != rejected[3][3]
    w = sum(emission[k][k] for k in range(4)) / 4
    p = sum(rejected[k][k] for k in range(4)) / 4
    assert w == F(8766022309695204, 44601684337881125)
    assert 1 - p == F(16118512411044049, 44601684337881125)
    assert rejected[0][2] == F(432624, 3997175)
    assert 0 < w <= p
    # Representative bright projection: rank two on the four-dimensional
    # data. Its unnormalized identity-Choi overlap is exactly p/2.
    bright = (F(0), F(0), F(1), F(1))
    probability = sum(x*x for x in bright) / 4
    overlap = sum(bright)**2 / 16
    assert probability == F(1, 2) and overlap == probability / 2
    return normalization_cases


def factory_replay():
    # The ideal fixed-order parity factory, including both X-readout records.
    for x in (0, 1):
        state = [scale(ONE, F(1, 2)) if (a ^ b) == x else ZERO for a, b in AB]
        corrected = [state[2 * a + (b ^ x)] for a, b in AB]
        assert corrected == [scale(ONE, F(1, 2)), ZERO, ZERO,
                             scale(ONE, F(1, 2))]
        assert inner(state, state) == scale(ONE, F(1, 2))
    # Every matrix entry of the remote controlled-S Kraus operators. The
    # Bell term surviving the a=measurement outcome fixes b=A xor m.
    online = 0
    for m, n in product((0, 1), repeat=2):
        kraus = []
        for a, b in AB:
            bell_bit = m ^ a
            bob_bit = bell_bit ^ m
            amp = mul(INV_SQRT2, INV_SQRT2)
            amp = mul(amp, root(4 * bob_bit * b))
            amp = scale(amp, (-1) ** (n * bob_bit + n * a))
            kraus.append(amp)
        target = [scale(root(4 * a * b), F(1, 2)) for a, b in AB]
        assert kraus == target
        require_cp(kraus, target)
        online += 1
    for b, data in AB:
        # T_b,T_B,CNOT,T_Bdagger,CNOT.
        exponent = 2 * (b + data - (b ^ data))
        assert root(exponent) == root(4 * b * data)
    # Known-state conversion: the Bell-pair POVM has completeness and equal
    # outcome probabilities; outcome1 followed by X⊗X equals outcome0.
    assert add(mul(COS, COS), mul(SIN, SIN)) == ONE
    t = [COS, ZERO, ZERO, SIN]
    for outcome in (0, 1):
        raw = [mul(INV_SQRT2, COS if outcome == 0 else SIN), ZERO, ZERO,
               mul(INV_SQRT2, SIN if outcome == 0 else COS)]
        assert inner(raw, raw) == scale(ONE, F(1, 2))
        if outcome:
            raw = list(reversed(raw))
        assert raw == [mul(INV_SQRT2, x) for x in t]
    # CS|++> has the same two Schmidt eigenvalues: trace1, determinant1/8.
    target_state = [scale(root(4*a*b), F(1, 2)) for a, b in AB]
    determinant = add(mul(target_state[0], target_state[3]),
                      scale(mul(target_state[1], target_state[2]), -1))
    assert inner([determinant], [determinant]) == scale(ONE, F(1, 8))
    assert mul(mul(COS, COS), mul(SIN, SIN)) == scale(ONE, F(1, 8))
    inverse_state = [scale(root(-4*a*b), F(1, 2)) for a, b in AB]
    corrected = [mul(root(4*b), inverse_state[2*(a ^ 1)+b]) for a, b in AB]
    assert corrected == target_state
    return online

class ConcG:
    __slots__=('r','i')
    def __init__(self,r=0,i=0):self.r=F(r);self.i=F(i)
    def __add__(self,o):
        o=conc_cast(o);return ConcG(self.r+o.r,self.i+o.i)
    __radd__=__add__
    def __neg__(self):return ConcG(-self.r,-self.i)
    def __sub__(self,o):return self+-conc_cast(o)
    def __rsub__(self,o):return conc_cast(o)+-self
    def __mul__(self,o):
        o=conc_cast(o);return ConcG(self.r*o.r-self.i*o.i,self.r*o.i+self.i*o.r)
    __rmul__=__mul__
    def __truediv__(self,o):
        o=conc_cast(o);n=o.r*o.r+o.i*o.i
        return self*ConcG(o.r/n,-o.i/n)
    def __eq__(self,o):
        o=conc_cast(o);return self.r==o.r and self.i==o.i
    def conj(self):return ConcG(self.r,-self.i)
    def conc_norm2(self):return self.r*self.r+self.i*self.i

def conc_cast(x):return x if isinstance(x,ConcG) else ConcG(x)
def conc_ident(n):return [[ConcG(int(i==j)) for j in range(n)] for i in range(n)]
def conc_mv(a,v):return [sum(x*y for x,y in zip(row,v)) for row in a]
def conc_mm(a,b):return [[sum(a[i][k]*b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]
def conc_adj(a):return [[a[j][i].conj() for j in range(len(a))] for i in range(len(a[0]))]
def conc_inner(v,w):return sum(x.conj()*y for x,y in zip(v,w))
def conc_norm2(v):return sum(x.conc_norm2() for x in v)
def conc_det(a):return a[0]*a[3]-a[1]*a[2]

def conc_u2(a=ConcG(F(3,5)),b=ConcG(0,F(4,5))):return [[a,b],[-b.conj(),a.conj()]]
def conc_native(a,alpha,delta):return [[alpha+a*delta,ConcG()], [ConcG(),alpha]]
def conc_unitary(a):assert conc_mm(conc_adj(a),a)==conc_ident(len(a))
def conc_plane(n,i,j,c=F(3,5),s=F(4,5)):
    u=conc_ident(n);u[i][i]=u[j][j]=ConcG(c);u[i][j]=ConcG(s);u[j][i]=ConcG(-s);return u

def conc_full_vectors(alpha,delta,beta,epsilon,source,wrappers):
    vectors=[]
    for a,b in product((0,1),repeat=2):
        amat=conc_mm(conc_mm(wrappers[0][1],conc_native(a,alpha,delta)),wrappers[0][0])
        bmat=conc_mm(conc_mm(wrappers[1][1],conc_native(b,beta,epsilon)),wrappers[1][0])
        vectors.append(conc_mv(conc_mm(bmat,amat),source[:2])+conc_mv(conc_mm(amat,bmat),source[2:]))
    return vectors

def conc_readouts():
    u=conc_mm(conc_plane(4,0,3),conc_plane(4,1,2,F(5,13),F(12,13)))
    phases=conc_ident(4);phases[1][1]=ConcG(0,1);phases[3][3]=ConcG(0,-1)
    v=conc_mm(conc_mm(conc_plane(4,0,2),phases),conc_plane(4,1,3))
    for x in (u,v):conc_unitary(x)
    # Eight rank-one POVM vectors; two different orthonormal bases, weights
    #9/25 and16/25. Bra rows suffice and satisfy sum |row><row|=I.
    rows=[[x*F(3,5) for x in row] for row in u]+[[x*F(4,5) for x in row] for row in v]
    effect=[[sum(row[i].conj()*row[j] for row in rows) for j in range(4)] for i in range(4)]
    assert effect==conc_ident(4)
    return rows

def conc_spectral_counterexample():
    # Frequency0 couples only A; frequency1 couples only B. Both conc_native
    #slots are visited and commute. Per-frequency contrast products vanish.
    assert (-2)*0 == 0*(-2) == 0
    total_probability=F(0)
    total_weighted_concurrence=F(0)
    for y in (1,-1):
        k=[F((-1)**a+y*(-1)**b,2) for a,b in product((0,1),repeat=2)]
        probability=sum(x*x for x in k)/4
        determinant=k[0]*k[3]-k[1]*k[2]
        weighted_concurrence=abs(determinant)/2
        assert probability==weighted_concurrence==F(1,2)
        total_probability+=probability
        total_weighted_concurrence+=weighted_concurrence
    assert total_probability==total_weighted_concurrence==1
    return 2


def conc_verify():
    A=conc_u2();B=[[ConcG(1),ConcG()],[ConcG(),ConcG(0,1)]];C=conc_u2(ConcG(F(5,13)),ConcG(F(12,13)))
    for u in (A,B,C):conc_unitary(u)
    wrappers=[((conc_ident(2),conc_ident(2)),(conc_ident(2),conc_ident(2))),
              ((A,B),(C,A)),((B,C),(A,B))]
    sources=[[ConcG(1),ConcG(0,1),ConcG(-1),ConcG(1)], [ConcG(1),ConcG(1),ConcG(1),ConcG(-1)],
             [ConcG(2),ConcG(),ConcG(),ConcG()]]
    sources=[[z/2 for z in source] for source in sources]
    for source in sources:assert conc_norm2(source)==1
    parameters=[(ConcG(F(-3,5),F(1,5)),ConcG(F(4,5),F(-2,5)),
                 ConcG(F(1,3),F(1,2)),ConcG(F(-3,4),F(1,7))),
                (ConcG(-1),ConcG(2),ConcG(-1),ConcG(2)),
                (ConcG(),ConcG(F(1,2)),ConcG(F(1,2)),ConcG(F(1,4))),
                (ConcG(F(1,3)),ConcG(),ConcG(F(1,2)),ConcG(F(1,3))),
                (ConcG(F(-21,25)),ConcG(F(2573,3263))+ConcG(F(21,25)),
                 ConcG(F(-5,7)),ConcG(F(647,827))+ConcG(F(5,7)))]
    rows=conc_readouts();branch_cases=0
    for pars,wrap,source in product(parameters,wrappers,sources):
        v=conc_full_vectors(*pars,source,wrap)
        vi=conc_full_vectors(ConcG(1),ConcG(-2),ConcG(1),ConcG(-2),source,wrap)
        D=pars[0]*pars[1]*pars[2]*pars[3]
        ideal_probability=F(0)
        for row in rows:
            k=[sum(x*y for x,y in zip(row,w)) for w in v]
            ki=[sum(x*y for x,y in zip(row,w)) for w in vi]
            assert conc_det(k)==D/4*conc_det(ki)
            # Every pure two-spin branch obeys p*C<=p. We compare the
            #squares exactly, then use the analytic scaling argument.
            assert 4*conc_det(ki).conc_norm2()<=conc_norm2(ki)**2
            ideal_probability+=conc_norm2(ki)/4
            branch_cases+=1
        assert ideal_probability==1
    ordinary_cases=0
    for pars,u in product(parameters,(conc_ident(2),A,B,C)):
        alpha,delta,beta,epsilon=pars
        D=alpha*delta*beta*epsilon
        for y in (1,-1):
            # Balanced source and Y readout are both unnormalized here.
            #The actual k is this vector/2 and the comm input adds1/2.
            k=[]
            for a,b in product((0,1),repeat=2):
                vv=conc_mv(conc_mm(conc_native(b,beta,epsilon),conc_mm(u,conc_native(a,alpha,delta))),[ConcG(1),ConcG(1)])
                k.append(vv[0]+ConcG(0,-y)*vv[1])
            expected=D*(u[0][0]*u[1][1]-u[0][1]*u[1][0])*ConcG(0,-y)
            assert conc_det(k)==expected
            # Two branches each give |D|/8 weighted concurrence, hence
            #total |D|/4; exact norm-squared identity avoids any floats.
            assert conc_det(k).conc_norm2()==D.conc_norm2()
            ordinary_cases+=1
    d=F(863246304,2361188375)
    pars=parameters[-1]
    D=pars[0]*pars[1]*pars[2]*pars[3]
    assert D.conc_norm2()/16==d*d
    return {'status':'passed','coherent_order_branch_factorizations':branch_cases,
            'ordinary_saturation_branches':ordinary_cases,
            'coherent_spectral_erasure_counterexample_branches':conc_spectral_counterexample(),
            'scope':'finite exact Gaussian-rational guards for scalar elastic concurrence closure; no full-instrument simulation, Bell-yield optimum or finite-bandwidth proof'}



def phase_field_matmul(a, b):
    return [[sum_field(mul(a[i][k], b[k][j]) for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def phase_field_adjoint(a):
    return [[conj(a[j][i]) for j in range(len(a))] for i in range(len(a[0]))]


def phase_two_cz_replay():
    count = 0
    for m, outcome in product((1, -1), (0, 1)):
        kraus = []
        for a, b in AB:
            parity = (-1)**(a + b)
            if outcome == 0:
                amp = add(COS, scale(mul(root(4), SIN), parity))
            else:
                amp = add(scale(SIN, -m), scale(mul(root(4), COS), m*parity))
                amp = scale(amp, parity)  # the local Z_A Z_B correction
            amp = mul(root(2*(a+b)), scale(amp, F(1, 2)))
            kraus.append(amp)
        target = [scale(root(4*a*b), F(1, 2)) for a, b in AB]
        require_cp(kraus, target)
        count += 1
    return count


def phase_known_switch_replay():
    eye = [[ONE, ZERO], [ZERO, ONE]]
    x = [[ZERO, ONE], [ONE, ZERO]]
    y = [[ZERO, root(-4)], [root(4), ZERO]]
    z = [[ONE, ZERO], [ZERO, scale(ONE, -1)]]
    cases = 0
    for p, q in ((z, x), (x, y), (y, z)):
        r = [[mul(INV_SQRT2, add(eye[i][j], mul(root(-4), p[i][j])))
              for j in range(2)] for i in range(2)]
        qr = phase_field_matmul(q, r)
        rq = phase_field_matmul(r, q)
        relative = phase_field_matmul(phase_field_adjoint(qr), rq)
        expected = [[mul(root(4), p[i][j]) for j in range(2)] for i in range(2)]
        assert relative == expected
        compiled = phase_field_matmul(qr, p)
        assert [[mul(root(4), v) for v in row] for row in compiled] == rq
        cases += 1
    return cases


def phase_bell_witness():
    # Real opposite-phase resonant model. This is an attainable nearby
    #rational preparation using the cited helper theorem and local filters,
    #not an assertion that nearly mixed marginals already give exact Bell.
    a, b, c, d = F(21, 25), F(2573, 3263), F(5, 7), F(647, 827)
    u = x = F(499457255181911835, 10**18)
    v = F(4135, 8664)
    assert v == c/(c+d)
    t = a*a+(b*b-a*a)*u*x
    h = a*a*(a+b)**2*u*(1-u)*x*(1-x)
    z = v*t
    probability = c*c*t+v*(d*d-c*c)*z
    da = h*c*c*(c*c+v*(d*d-c*c))
    db = v*(1-v)*c*c*(c+d)**2*z*(t-z)
    assert 0 < u < 1 and 0 < v < 1 and 0 < x < 1
    assert 0 <= z <= t and h <= z*(t-z)
    assert da <= db and probability**2 >= 4*da
    lower = F(36521957, 10**8)
    assert probability > lower
    assert 4*min(da, db) > 2*probability*lower-lower*lower
    cap = a*c*(a+b)*(c+d)/4
    assert cap == F(863246304, 2361188375)
    assert cap-lower < F(379, 10**6)
    assert (cap-lower)/lower < F(13, 12500)
    return {"ordinary_Bell_yield_strict_lower": str(lower),
            "scalar_switch_Bell_yield_upper": str(cap),
            "absolute_improvement_strict_upper": "379/1000000",
            "relative_improvement_strict_upper": "13/12500"}


# Exact full-rank example of fixed-marginal splitting and helper extraction.
helper_ZERO=ConcG()
helper_ONE=ConcG(1)


def helper_zeros(r,c):
    return [[helper_ZERO for _ in range(c)] for _ in range(r)]


def helper_eye(n):
    out=helper_zeros(n,n)
    for j in range(n): out[j][j]=helper_ONE
    return out


def helper_diag(vals):
    out=helper_zeros(len(vals),len(vals))
    for j,v in enumerate(vals): out[j][j]=conc_cast(v)
    return out


def helper_add(a,b):
    return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]


def helper_scale(a,s):
    return [[x*s for x in row] for row in a]


def helper_dag(a):
    return [[a[j][i].conj() for j in range(len(a))] for i in range(len(a[0]))]


def helper_mul(a,b):
    return [[sum((a[i][k]*b[k][j] for k in range(len(b))),helper_ZERO)
             for j in range(len(b[0]))] for i in range(len(a))]


def helper_kron(a,b):
    return [[a[i//len(b)][j//len(b[0])]*b[i%len(b)][j%len(b[0])]
             for j in range(len(a[0])*len(b[0]))]
            for i in range(len(a)*len(b))]


def helper_vec(vals):
    return [[conc_cast(x)] for x in vals]


def helper_outer(v):
    return helper_mul(v,helper_dag(v))


def helper_trace(a):
    return sum((a[j][j] for j in range(len(a))),helper_ZERO)


def helper_rank(a):
    b=[row[:] for row in a]
    r=0
    for col in range(len(b[0])):
        piv=next((j for j in range(r,len(b)) if b[j][col]!=helper_ZERO),None)
        if piv is None: continue
        b[r],b[piv]=b[piv],b[r]
        den=b[r][col]
        b[r]=[x/den for x in b[r]]
        for j in range(len(b)):
            if j!=r and b[j][col]!=helper_ZERO:
                v=b[j][col]
                b[j]=[x-v*y for x,y in zip(b[j],b[r])]
        r+=1
        if r==len(b): break
    return r


def helper_ptr_a(a):
    return [[sum((a[2*i+j][2*i+k] for i in range(2)),helper_ZERO)
             for k in range(2)] for j in range(2)]


def helper_ptr_b(a):
    return [[sum((a[2*i+j][2*k+j] for j in range(2)),helper_ZERO)
             for k in range(2)] for i in range(2)]


def helper_require(condition,message):
    if not condition: raise AssertionError(message)


def helper_real_trace(a):
    t=helper_trace(a)
    helper_require(t.i==0,'helper_trace must be real')
    return t.r


def helper_conjugate(a,u):
    return helper_mul(helper_mul(u,a),helper_dag(u))


def helper_verify():
    if not __debug__:
        raise RuntimeError('Do not run exact replay with Python optimization enabled')
    d=[F(4,25),F(1,25),F(4,25),F(16,25)]
    rho=helper_diag(d)
    xe=helper_zeros(4,4); xe[0][3]=xe[3][0]=ConcG(F(8,25))
    xo=helper_zeros(4,4); xo[1][2]=ConcG(0,F(2,25)); xo[2][1]=xo[1][2].conj()
    helper_require(helper_ptr_a(xe)==helper_ptr_b(xe)==helper_zeros(2,2),'even perturbation marginals')
    helper_require(helper_ptr_a(xo)==helper_ptr_b(xo)==helper_zeros(2,2),'odd perturbation marginals')
    helper_require(helper_rank(rho)==4,'initial helper_rank four')
    rank2={}
    rank3={}
    for s in (-1,1):
        rs=helper_add(rho,helper_scale(xe,s)); rank3[s]=rs
        helper_require(helper_rank(rs)==3,'first endpoint helper_rank three')
        # Support containment of the second perturbation, in exact row helper_rank.
        helper_require(helper_rank([a+b for a,b in zip(rs,xo)])==3,'second direction in support')
        for t in (-1,1):
            rst=helper_add(rs,helper_scale(xo,t)); rank2[s,t]=rst
            e=helper_vec([F(2,5),0,0,s*F(4,5)])
            o=helper_vec([0,F(1,5),ConcG(0,-t*F(2,5)),0])
            helper_require(rst==helper_add(helper_outer(e),helper_outer(o)),'positive helper_rank-two factorization')
            helper_require(helper_rank(rst)==2,'helper_rank-two endpoint')
            helper_require(helper_ptr_a(rst)==helper_ptr_a(rho) and helper_ptr_b(rst)==helper_ptr_b(rho),
                    'both endpoint marginals preserved')
        helper_require(helper_scale(helper_add(rank2[s,-1],rank2[s,1]),F(1,2))==rs,
                'second endpoint average')
    helper_require(helper_scale(helper_add(rank3[-1],rank3[1]),F(1,2))==rho,'first endpoint average')
    # Both directions have maximal endpoints at +/-1: beyond them the
    # relevant 2x2 principal determinant is negative.
    for direction,pair in ((xe,(0,3)),(xo,(1,2))):
        beyond=helper_add(rho,helper_scale(direction,2)); i,j=pair
        determinant=beyond[i][i]*beyond[j][j]-beyond[i][j]*beyond[j][i]
        helper_require(determinant.i==0 and determinant.r<0,'maximal endpoint witness')
    comm=helper_add(helper_mul(rank2[1,1],rank2[-1,1]),helper_scale(helper_mul(rank2[-1,1],rank2[1,1]),-1))
    helper_require(comm!=helper_zeros(4,4),'example includes noncommuting helper_rank-two pieces')

    # Rational non-Clifford rotations make the A marginal complex and the
    # B marginal nondiagonal, while preserving all preceding properties.
    ua=[[ConcG(F(3,5)),ConcG(0,F(4,5))],[ConcG(0,F(4,5)),ConcG(F(3,5))]]
    ub=[[ConcG(F(5,13)),ConcG(F(12,13))],[ConcG(-F(12,13)),ConcG(F(5,13))]]
    helper_require(helper_mul(helper_dag(ua),ua)==helper_eye(2) and helper_mul(helper_dag(ub),ub)==helper_eye(2),'local unitaries')
    u=helper_kron(ua,ub); rotated=helper_conjugate(rho,u)
    helper_require(helper_ptr_b(rotated)==helper_conjugate(helper_diag([F(1,5),F(4,5)]),ua),'A spectrum')
    helper_require(helper_ptr_a(rotated)==helper_conjugate(helper_diag([F(8,25),F(17,25)]),ub),'B spectrum')
    helper_require(helper_ptr_b(rotated)[0][1].i!=0 and helper_ptr_a(rotated)[0][1]!=helper_ZERO,
            'nontrivial complex/nondiagonal marginals')
    helper_require(helper_rank(rotated)==4,'helper_rank unchanged by local rotations')

    # A fixed purification has coefficient matrix W=U sqrt(D). Its helper
    # measurement vector m creates the AB vector W helper_conjugate(m).
    w=helper_mul(u,helper_diag([F(2,5),F(1,5),F(2,5),F(4,5)]))
    effect_sum=helper_zeros(4,4); ensemble_sum=helper_zeros(4,4)
    filtered_sum=helper_zeros(4,4); success=F(0); count=0
    fa=helper_conjugate(helper_diag([1,F(1,2)]),ua); ff=helper_kron(fa,helper_eye(2))
    for s in (-1,1):
        for t in (-1,1):
            ms=[helper_vec([F(1,2),0,0,s*F(1,2)]),
                helper_vec([0,F(1,2),ConcG(0,t*F(1,2)),0])]
            targets=[helper_vec([F(1,5),0,0,s*F(2,5)]),
                     helper_vec([0,F(1,10),ConcG(0,-t*F(1,5)),0])]
            for m,target in zip(ms,targets):
                effect_sum=helper_add(effect_sum,helper_outer(m))
                mv=helper_vec([r[0].conj() for r in m])
                v=helper_mul(w,mv)
                helper_require(v==helper_mul(u,target),'HJW conditional vector')
                ensemble_sum=helper_add(ensemble_sum,helper_outer(v))
                bell=helper_mul(ff,v); br=helper_outer(bell); weight=helper_real_trace(br)
                helper_require(weight>0,'nonzero accepted branch')
                helper_require(helper_ptr_a(br)==helper_scale(helper_eye(2),weight/2) and
                        helper_ptr_b(br)==helper_scale(helper_eye(2),weight/2),'exact Bell branch')
                filtered_sum=helper_add(filtered_sum,br); success+=weight; count+=1
    helper_require(count==8 and effect_sum==helper_eye(4),'complete eight-outcome POVM')
    helper_require(ensemble_sum==rotated,'complete pure ensemble reconstruction')
    helper_require(success==F(2,5),'marginal-bound Bell extraction attained')
    helper_require(filtered_sum==helper_conjugate(rotated,ff),'filter success map normalization')
    # Filter failure is explicitly charged; F^dagger F plus its positive
    # complement equals identity. The complement has known factorization.
    fcomp=helper_conjugate(helper_diag([0,F(3,4)]),ua)
    helper_require(helper_add(helper_mul(helper_dag(fa),fa),fcomp)==helper_eye(2),'filter contraction/complement')
    failure=helper_real_trace(helper_mul(helper_kron(fcomp,helper_eye(2)),rotated))
    helper_require(failure==F(3,5) and success+failure==1,'all-launch accounting')
    return {'status': 'passed', 'arithmetic': 'Gaussian rational, stdlib',
            'initial_rank': 4, 'rank3_endpoints': 2, 'rank2_pieces': 4,
            'helper_povm_outcomes_on_occupied_support': count,
            'bell_probability': str(success),
            'filter_failure_probability': str(failure)}




# Constant-control four-mode normal form, including coherent frequency.
def bus_transpose(a):
    return [list(row) for row in zip(*a)]


def bus_block(a,b,c,d):
    return [ar+br for ar,br in zip(a,b)]+[cr+dr for cr,dr in zip(c,d)]


def bus_rows_of_vectors(vs):
    return [[v[j][0] for j in range(len(v))] for v in vs]


def bus_native_projector():
    return helper_diag([1,0,1,0])


def bus_dilation(root_k,root_complement):
    w=bus_block(root_k,helper_scale(root_complement,-1),root_complement,root_k)
    helper_require(helper_mul(helper_dag(w),w)==helper_eye(4),'four-mode Naimark unitary')
    # Native bright columns are 0 and 2, while w's first two columns span Q.
    reordered=[[row[j] for j in (0,2,1,3)] for row in w]
    phase=helper_diag([1,ConcG(0,1),1,1])
    uf=helper_mul(phase,reordered)
    between=helper_dag(uf)
    q=helper_conjugate(bus_native_projector(),uf)
    helper_require(helper_mul(q,q)==q and helper_dag(q)==q and helper_rank(q)==2,'helper_rank-two physical projector')
    helper_require(helper_mul(helper_dag(between),between)==helper_eye(4),'native intermediate unitary')
    return between,q,phase


def bus_node(alpha,bright_a,beta,bright_b,a,b,x,sx,root_k,root_complement):
    pn=bus_native_projector();between,q,phase=bus_dilation(root_k,root_complement)
    k=helper_mul(root_k,root_k)
    helper_require(helper_add(k,helper_mul(root_complement,root_complement))==helper_eye(2),'effect complement')
    helper_require(helper_mul(root_k,root_complement)==helper_mul(root_complement,root_k),'commuting roots')
    dd=helper_diag([x,1-x]);ss=helper_diag(sx)
    y=helper_mul(helper_mul(ss,bus_transpose(k)),ss)
    cy=helper_mul(ss,bus_transpose(root_k));cc=helper_mul(ss,bus_transpose(root_complement))
    helper_require(bus_outer_columns(cy)==y,'positive Y factorization')
    helper_require(bus_outer_columns(cc)==helper_add(dd,helper_scale(y,-1)),'positive D-Y factorization')
    source=helper_mul(phase,helper_vec([sx[0],sx[1],0,0]))
    helper_require(helper_trace(helper_outer(source))==helper_ONE,'normalized pure four-mode source')
    aa=[helper_scale(helper_eye(4),alpha),helper_add(helper_scale(helper_eye(4),alpha),helper_scale(pn,bright_a-alpha))]
    bb=[helper_scale(helper_eye(4),beta),helper_add(helper_scale(helper_eye(4),beta),helper_scale(pn,bright_b-beta))]
    outputs=[]
    for ai in range(2):
        for bi in range(2):
            outputs.append(helper_scale(helper_mul(bb[bi],helper_mul(between,helper_mul(aa[ai],source))),a[ai]*b[bi]))
    actual=helper_mul(bus_rows_of_vectors(outputs),helper_dag(bus_rows_of_vectors(outputs)))
    n=[[a[0]*alpha,a[0]*alpha],[a[1]*bright_a,a[1]*alpha]]
    t=helper_conjugate(dd,n);xx=helper_conjugate(y,n)
    phi0=helper_vec([beta*b[0],beta*b[1]])
    phi1=helper_vec([beta*b[0],bright_b*b[1]])
    predicted=helper_add(helper_kron(helper_add(t,helper_scale(xx,-1)),helper_outer(phi0)),helper_kron(xx,helper_outer(phi1)))
    helper_require(actual==predicted,'full 4x4 spin state equals affine normal form')
    # This nontrivial example must actually test the complex bus_transpose.
    wrong_y=helper_mul(helper_mul(ss,k),ss)
    wrong_x=helper_conjugate(wrong_y,n)
    wrong=helper_add(helper_kron(helper_add(t,helper_scale(wrong_x,-1)),helper_outer(phi0)),helper_kron(wrong_x,helper_outer(phi1)))
    if k[0][1].i and 0<x<1:
        helper_require(wrong!=actual,'bus_transpose convention detected')
    if x in (0,1):
        helper_require(helper_rank(t)<=1,'singular occupancy handled pointwise')
    # First-encounter Schmidt determinant, including all spin/source weights.
    det=t[0][0]*t[1][1]-t[0][1]*t[1][0]
    expected=(a[0]*a[1]*alpha*(bright_a-alpha))
    expected=expected*expected.conj()*x*(1-x)
    helper_require(det==expected,'local Schmidt determinant formula')
    return outputs,actual,predicted


def bus_outer_columns(a):
    return helper_mul(a,helper_dag(a))


def bus_verify():
    if not __debug__:
        raise RuntimeError('Do not run exact replay with Python optimization enabled')
    v=[[ConcG(F(3,5)),ConcG(0,F(4,5))],[ConcG(0,F(4,5)),ConcG(F(3,5))]]
    helper_require(helper_mul(helper_dag(v),v)==helper_eye(2),'effect eigenbasis unitary')
    roots=[(helper_zeros(2,2),helper_eye(2)),(helper_eye(2),helper_zeros(2,2)),
           (helper_conjugate(helper_diag([F(3,5),F(5,13)]),v),
            helper_conjugate(helper_diag([F(4,5),F(12,13)]),v))]
    occupancies=[(F(0),(F(0),F(1))),
                 (F(9,25),(F(3,5),F(4,5))),
                 (F(1),(F(1),F(0)))]
    a=[ConcG(F(5,13)),ConcG(0,F(12,13))]
    b=[ConcG(F(8,17)),ConcG(0,F(15,17))]
    response=[(ConcG(-F(4,5),F(1,10)),ConcG(F(3,5),-F(1,5)),
               ConcG(-F(2,3),F(1,6)),ConcG(F(3,4),F(1,8))),
              (ConcG(-F(3,5),-F(1,5)),ConcG(F(2,3),F(1,6)),
               ConcG(-F(5,7),-F(1,7)),ConcG(F(4,5),-F(1,10)))]
    for rr in response:
        for amp in rr:
            norm=amp*amp.conj()
            helper_require(norm.i==0 and norm.r<=1,'passive scalar response')
    spectral=[ConcG(F(3,5)),ConcG(0,F(4,5))]
    count=0;full_count=0
    for root_k,root_complement in roots:
        for x,sx in occupancies:
            outs=[];formula=helper_zeros(4,4)
            for amps,f in zip(response,spectral):
                output,actual,predicted=bus_node(*amps,a,b,x,sx,root_k,root_complement)
                outs.append(output)
                weight=f*f.conj()
                formula=helper_add(formula,helper_scale(predicted,weight));count+=1
            full_vectors=[]
            for j in range(4):
                full_vectors.append(outs[0][j]+outs[1][j])
                full_vectors[-1]=[[spectral[h]*outs[h][j][k][0]]
                                  for h in range(2) for k in range(4)]
            full_rows=bus_rows_of_vectors(full_vectors)
            reduced=helper_mul(full_rows,helper_dag(full_rows))
            helper_require(reduced==formula,'coherent two-frequency state integrated formula')
            # The global output really retains frequency coherence; this
            # helper_rank-one vector is not a classical mixture of bus_node states.
            global_vector=helper_vec([entry for row in full_rows for entry in row])
            global_state=helper_outer(global_vector)
            helper_require(helper_rank(global_state)==1,'pure global pulse output')
            helper_require(any(global_state[8*j+k][8*l+4+m]!=helper_ZERO
                        for j in range(4) for l in range(4)
                        for k in range(4) for m in range(4)),
                    'nonzero cross-frequency coherences')
            if x==0:
                helper_require(helper_rank(helper_ptr_b(reduced))==1,'dark source leaves A pure even for pulse')
            full_count+=1
    return {'status': 'passed', 'arithmetic': 'Gaussian rational, stdlib',
            'single_frequency_full_state_comparisons': count,
            'coherent_two_frequency_examples': full_count,
            'effect_cases': len(roots), 'occupancy_cases': len(occupancies),
            'checks': ['Naimark rank/unitarity', 'complex transpose',
                       'singular occupancy', 'Schmidt determinant',
                       'all 4x4 spin entries', 'cross-frequency coherence']}




# Coefficient-independent eigen-source survivor compiler.
def eigen_scale(c, a):
    return helper_scale(a, c)


def eigen_outer(v):
    return [[x*y.conj() for y in v] for x in v]


def eigen_inner(v,w):
    return sum(x.conj()*y for x,y in zip(v,w))


def eigen_difference(v,w):
    return [x-y for x,y in zip(v,w)]


def eigen_iszero(v):
    return all(x==0 for x in v)


def eigen_orthogonal_remainder(v,basis):
    out=v[:]
    for b in basis:
        norm=eigen_inner(b,b)
        assert norm.i==0 and norm.r>0
        coefficient=eigen_inner(b,out)/norm
        out=[x-coefficient*y for x,y in zip(out,b)]
    return out


def eigen_orthogonal_basis(vectors):
    basis=[]
    for v in vectors:
        r=eigen_orthogonal_remainder(v,basis)
        if not eigen_iszero(r):
            basis.append(r)
    return basis


def eigen_padded_projector(contain,exclude,dimension=4,rank=2):
    """Project onto `contain`, avoid `exclude`, pad to the specified rank.

    Every normalization divides by a rational squared norm; square roots are
    unnecessary. The theorem supplies orthogonality and the available space.
    """
    rb=eigen_orthogonal_basis(contain)
    eb=eigen_orthogonal_basis(exclude)
    assert len(rb)<=rank and all(eigen_inner(r,e)==0 for r in rb for e in eb)
    for k in range(dimension):
        if len(rb)==rank:
            break
        v=[ConcG(i==k) for i in range(dimension)]
        r=eigen_orthogonal_remainder(v,rb+eb)
        if not eigen_iszero(r):
            rb.append(r)
    assert len(rb)==rank
    p=[[ConcG() for _ in range(dimension)] for _ in range(dimension)]
    for b in rb:
        p=helper_add(p,eigen_scale(ConcG(1)/eigen_inner(b,b),eigen_outer(b)))
    assert p==helper_dag(p) and helper_mul(p,p)==p and helper_trace(p)==rank
    for v in contain:
        assert conc_mv(p,v)==v
    for v in exclude:
        assert eigen_iszero(conc_mv(p,v))
    return p


def eigen_build_compiler(P,Q,psi,control,eigenvalue):
    assert conc_mv(P,psi)==[eigenvalue*x for x in psi]
    assert eigen_inner(psi,psi)==1 and eigen_inner(control,control)==1
    x=[c*d for c in control for d in psi]
    qpsi=conc_mv(Q,psi)
    z=[c*d for c in control for d in qpsi]
    # The two switch branches are QP psi and PQ psi in order.
    w=[control[0]*d for d in conc_mv(Q,conc_mv(P,psi))]+[control[1]*d for d in conc_mv(P,qpsi)]
    if eigenvalue==1:
        contain,exclude=[x,w],[eigen_difference(z,w)]
    else:
        assert eigenvalue==0
        contain,exclude=[w],[x,eigen_difference(z,w)]
    PP=eigen_padded_projector(contain,exclude)
    QQ=helper_kron(helper_eye(2),Q)
    assert helper_mul(QQ,QQ)==QQ and QQ==helper_dag(QQ) and helper_trace(QQ)==2
    assert conc_mv(PP,x)==[eigenvalue*d for d in x]
    assert conc_mv(QQ,x)==z and conc_mv(PP,z)==w
    return x,PP,QQ


def eigen_switch_vector(P,Q,psi,control,coefficients,a,b):
    alpha,alpha1,beta,beta1=coefficients
    A=helper_add(eigen_scale(alpha,helper_eye(2)),eigen_scale((alpha1-alpha)*a,P))
    B=helper_add(eigen_scale(beta,helper_eye(2)),eigen_scale((beta1-beta)*b,Q))
    return [control[0]*z for z in conc_mv(helper_mul(B,A),psi)]+[control[1]*z for z in conc_mv(helper_mul(A,B),psi)]


def eigen_ordinary_vector(PP,QQ,source,coefficients,a,b):
    alpha,alpha1,beta,beta1=coefficients
    A=helper_add(eigen_scale(alpha,helper_eye(4)),eigen_scale((alpha1-alpha)*a,PP))
    B=helper_add(eigen_scale(beta,helper_eye(4)),eigen_scale((beta1-beta)*b,QQ))
    return conc_mv(helper_mul(A,B),source)


def eigen_verify():
    P=helper_diag([1,0])
    qs=[[ConcG(1),ConcG()],[ConcG(),ConcG(1)],[ConcG(F(3,5)),ConcG(F(4,5))],
        [ConcG(F(3,5)),ConcG(0,F(4,5))]]
    projectors=[eigen_outer(q) for q in qs]
    controls=[[ConcG(1),ConcG()],[ConcG(),ConcG(0,1)],[ConcG(F(3,5)),ConcG(F(4,5))],
              [ConcG(F(3,5)),ConcG(0,F(4,5))],[ConcG(0,F(5,13)),ConcG(F(12,13))]]
    coefficients=[(ConcG(-1),ConcG(1),ConcG(-1),ConcG(1)),
                  (ConcG(-F(3,5),F(1,5)),ConcG(F(2,5),-F(1,5)),ConcG(F(3,10),F(2,5)),ConcG(-F(1,2),F(1,10))),
                  (ConcG(-F(21,25)),ConcG(F(2573,3263)),ConcG(-F(5,7)),ConcG(F(647,827))),
                  (ConcG(),ConcG(F(1,2)),ConcG(F(2,5)),ConcG(0,F(3,5))),
                  (ConcG(F(3,10),F(2,5)),ConcG(F(3,10),F(2,5)),ConcG(-F(4,5)),ConcG(F(1,5),F(1,10))),
                  (ConcG(F(1,3)),ConcG(0,F(2,3)),ConcG(),ConcG(F(3,5),F(1,5)))]
    for values in coefficients:
        assert all(eigen_inner([v],[v]).r<=1 for v in values)
    mode_amplitudes=[ConcG(F(3,5)),ConcG(0,F(4,5))]
    assert eigen_inner(mode_amplitudes,mode_amplitudes)==1
    state_cases=0;coherent_cases=0;projector_cases=0
    for eigenvalue in (0,1):
        psi=[ConcG(eigenvalue),ConcG(1-eigenvalue)]
        for Q in projectors:
            assert helper_mul(Q,Q)==Q and Q==helper_dag(Q) and helper_trace(Q)==1
            for control in controls:
                source,PP,QQ=eigen_build_compiler(P,Q,psi,control,eigenvalue)
                projector_cases+=1
                for values in coefficients:
                    for a in (0,1):
                        for b in (0,1):
                            target=eigen_switch_vector(P,Q,psi,control,values,a,b)
                            actual=eigen_ordinary_vector(PP,QQ,source,values,a,b)
                            assert target==actual
                            norm=eigen_inner(target,target)
                            assert norm.i==0 and 0<=norm.r<=1
                            state_cases+=1
                # Two coherent spectral labels with different COMPLEX responses.
                # The same PP,QQ are used for both labels. This compares full
                # amplitudes, rather than tracing the labels before comparison.
                targets=[];actuals=[]
                for a in (0,1):
                    for b in (0,1):
                        tv=[];av=[]
                        for amp,values in zip(mode_amplitudes,(coefficients[1],coefficients[2])):
                            tv += [amp*z for z in eigen_switch_vector(P,Q,psi,control,values,a,b)]
                            av += [amp*z for z in eigen_ordinary_vector(PP,QQ,source,values,a,b)]
                        assert tv==av
                        targets.append(tv);actuals.append(av)
                        coherent_cases+=1
                # Check every input matrix unit's cross-frequency block. Vector
                # equality above already proves all ABR inputs by linearity;
                # this guard prevents accidentally dephasing the frequency flag.
                for v,w,vv,ww in zip([v for v in targets for _ in targets],targets*len(targets),
                                     [v for v in actuals for _ in actuals],actuals*len(actuals)):
                    left=[[v[i]*w[j+4].conj() for j in range(4)] for i in range(4)]
                    right=[[vv[i]*ww[j+4].conj() for j in range(4)] for i in range(4)]
                    assert left==right
    return {'status':'passed','exact_rank_two_compiler_projectors':projector_cases,
            'full_survivor_spin_basis_cases':state_cases,
            'coherent_two_frequency_spin_basis_cases':coherent_cases,
            'scope':'coefficient-independent reverse-word coherent survivor compiler for both A-projector eigenspaces, declared four-mode preserved ports and known wrappers; no loss/emission completion or router-clock validation'}




def verify():
    assert mul(INV_SQRT2, INV_SQRT2) == scale(ONE, F(1, 2))
    assert add(mul(COS, COS), mul(SIN, SIN)) == ONE
    switch_branches, carrier_states = replay_switch_and_one_bus()
    concurrence = conc_verify()
    return {"status": "passed", "switch_one_bus_full_choi_branches": switch_branches,
            "four_mode_full_choi_branches": replay_four_mode(),
            "lost_carrier_scope_obstructions": replay_loss_boundary(carrier_states),
            "all_loss_parameter_cases": loss_replay_failures(),
            "all_loss_detected_full_choi_branches": loss_replay_detected(),
            "cavity_kernel_normalization_cases": cavity_replay(),
            "entanglement_first_online_full_choi_branches": factory_replay(),
            "scalar_concurrence_branch_factorizations": concurrence["coherent_order_branch_factorizations"],
            "ordinary_concurrence_saturation_branches": concurrence["ordinary_saturation_branches"],
            "coherent_spectral_erasure_branches": concurrence["coherent_spectral_erasure_counterexample_branches"],
            "two_CZ_online_full_choi_branches": phase_two_cz_replay(),
            "known_local_switch_compiler_cases": phase_known_switch_replay(),
            "exact_scalar_Bell_yield_witness": phase_bell_witness(),
            "arbitrary_helper_rank_reduction_example": helper_verify(),
            "constant_control_four_mode_normal_form": bus_verify(),
            "eigen_source_survivor_compiler": eigen_verify(),
            "scope": "exact detected/aggregate-vacuum spin instruments under declared reciprocal post-unitary erasures, plus scalar concurrence/Bell-yield, cavity/rank-loss/factory and known-gate identities, a full-rank helper POVM/filter example, constant-control coherent-frequency normal forms and eigen-source survivor compilers; universal proofs, native ports, calibration and clocks remain analytic"}


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True))
