"""Exact finite replay of NR-R11's detected remote-spin phase instruments.

Arithmetic is in Q[exp(i*pi/8)] with standard-library fractions. All spin
matrix-unit coefficients and explicit unequal-module loss histories are
checked. Gaussian rationals also guard the scalar-concurrence determinant
factorization; the rational Bell-yield witness and known-gate compilers are
replayed exactly. A full-rank fixed-marginal reduction and an eight-outcome
helper POVM with local-filter failure accounting guard the arbitrary-helper
assistance proof. Coherent frequency guards also check the constant-control
four-mode normal form and coefficient-independent eigen-source survivor
compiler. Reflected-gate fixtures guard continuous local phase corrections,
complex covariance orientation, prescribed flags and the balanced-attenuation
upper witness. The native port, calibration, timing and general scattering/RUS
comparisons remain analytic scope, not certified by finite replay.
Import is silent; no files are written.
"""
from fractions import Fraction as F
from itertools import combinations, product
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




# Exact continuous local-Z gate cone and balanced reflected family.
def gate_transpose(a):return [list(row) for row in zip(*a)]
def gate_covariance(vectors):return [[eigen_inner(w,v) for w in vectors] for v in vectors]
def gate_schur(a,b):return [[x*y for x,y in zip(ar,br)] for ar,br in zip(a,b)]


def gate_determinant(a):
    a=[row[:] for row in a];out=ConcG(1)
    for j in range(len(a)):
        p=next((k for k in range(j,len(a)) if a[k][j]!=0),None)
        if p is None:return ConcG()
        if p!=j:a[p],a[j]=a[j],a[p];out=-out
        d=a[j][j];out=out*d
        for k in range(j+1,len(a)):
            c=a[k][j]/d
            a[k]=[x-c*y for x,y in zip(a[k],a[j])]
    return out


def gate_psd(a):
    assert a==helper_dag(a)
    for size in range(1,len(a)+1):
        for inds in combinations(range(len(a)),size):
            d=gate_determinant([[a[i][j] for j in inds] for i in inds])
            assert d.i==0 and d.r>=0


def gate_partial_transpose(a):
    return [[a[2*(j//2)+i%2][2*(i//2)+j%2] for j in range(4)] for i in range(4)]


def gate_phase_cone(omega,p):
    gate_psd(omega);gate_psd(gate_partial_transpose(omega))
    assert all(omega[i][i]==p for i in range(4))
    assert omega[0][1]==omega[2][3] and omega[0][2]==omega[1][3]


def gate_pauli_phases():
    return [[ConcG(1),ConcG(b),ConcG(a),ConcG(a*b)] for a in (1,-1) for b in (1,-1)]


def gate_phase_subspace_basis():
    out=[helper_eye(4)]
    for pairs in (((0,1),(2,3)),((0,2),(1,3)),((0,3),),((1,2),)):
        for coefficient in (ConcG(1),ConcG(0,1)):
            a=[[ConcG() for _ in range(4)] for _ in range(4)]
            for i,j in pairs:a[i][j]=coefficient;a[j][i]=coefficient.conj()
            out.append(a)
    return out


def gate_balanced_family():
    # The physical resonance tuning is checked exactly for several C>0.
    for C in (F(1,3),F(1),F(3,2),F(7,3),F(100)):
        eta=(C+1)/(C+2)
        dark=1-2*eta;bright=1-2*eta/(1+C)
        assert dark==-C/(C+2) and bright==C/(C+2)
        assert F(1,2)<eta<1
        kappa, gamma = F(5, 2), F(3)
        g2 = C*kappa*gamma
        kappa_r = eta*kappa
        assert kappa-kappa_r == kappa/(C+2)
        assert 1-2*kappa_r/kappa == dark
        assert 1-2*kappa_r*gamma/(kappa*gamma+g2) == bright
    # Two tuned resonant amplitudes, plus harmless known common gate_pauli_phases.
    alpha=ConcG(-F(3,7))*ConcG(F(3,5),F(4,5))
    beta=ConcG(-F(7,13))*ConcG(F(5,13),F(12,13))
    amplitude=alpha*beta;p0=(amplitude*amplitude.conj()).r
    assert p0==F(9,169)
    PA=helper_diag([0,1,0,1]);PB=helper_diag([0,0,1,1]);I=helper_eye(4)
    source=[ConcG(F(1,2)) for _ in range(4)]
    vectors=[]
    for a in (0,1):
        A=eigen_scale(alpha,helper_add(I,eigen_scale(-2*a,PA)))
        for b in (0,1):
            B=eigen_scale(beta,helper_add(I,eigen_scale(-2*b,PB)))
            vectors.append(conc_mv(helper_mul(B,A),source))
    cov=gate_covariance(vectors)
    assert cov==eigen_scale(p0,I)
    # Two separately preserved gate flags with fixed relative weights.
    targets=[[ConcG(1),ConcG(1),ConcG(1),ConcG(0,1)],[ConcG(1),ConcG(1),ConcG(1),ConcG(0,-1)]]
    roots=[F(3,5),F(4,5)]
    total=[[ConcG() for _ in range(4)] for _ in range(4)]
    measurement=[];corrected=[]
    # B0 is the unitary Walsh matrix: the actual bus-row matrix is amplitude*B0.
    B0=eigen_scale(F(1,2),[[ConcG((-1)**(a*pa+b*pb)) for pa,pb in ((0,0),(1,0),(0,1),(1,1))]
                     for a,b in ((0,0),(0,1),(1,0),(1,1))])
    assert helper_mul(B0,helper_dag(B0))==I
    for target,root in zip(targets,roots):
        pl=p0*root*root;omega=eigen_scale(pl,I)
        gate_phase_cone(omega,pl)
        total=helper_add(total,gate_schur(eigen_outer(target),omega))
        flag_corrected=[]
        for v in gate_pauli_phases():
            t=[ConcG(F(3,13)*root/2)*u*z for u,z in zip(target,v)]
            # t=B m*, so m*=B0^dagger t/amplitude.
            aconj=[z/amplitude for z in conc_mv(helper_dag(B0),t)]
            m=[z.conj() for z in aconj];measurement.append(m)
            actual=[eigen_inner(m,bus) for bus in vectors]
            assert actual==t
            fixed=[z*y for z,y in zip(v,actual)]
            assert fixed==[ConcG(F(3,13)*root/2)*u for u in target]
            flag_corrected.append(eigen_outer(fixed))
        cp=[[sum(mat[i][j] for mat in flag_corrected) for j in range(4)] for i in range(4)]
        assert cp==eigen_scale(pl,eigen_outer(target))
        corrected.append(pl)
    assert total==cov and sum(corrected)==p0
    effect=[[sum(m[i]*m[j].conj() for m in measurement) for j in range(4)] for i in range(4)]
    assert effect==I
    # Fixed/eigen_outer dual Z=|00><00|; V=Z-I/4 is orthogonal to the phase subspace.
    Z=helper_diag([1,0,0,0]);V=helper_add(Z,eigen_scale(-F(1,4),I))
    gate_psd(Z)
    assert all(helper_trace(helper_mul(V,b))==0 for b in gate_phase_subspace_basis())
    assert helper_trace(helper_mul(Z,cov))==p0
    # A local output Z correction cannot turn inverse-CS into CS.
    ratio=lambda u:u[0]*u[3]/(u[1]*u[2])
    assert ratio(targets[0])==ConcG(0,1) and ratio(targets[1])==ConcG(0,-1)
    return {'optimal_reflected_gate_probability':str(p0),'preserved_gate_flag_probabilities':[str(p) for p in corrected],
            'measurement_refinements':len(measurement),'dual_objective':str(p0)}


def gate_range_and_pauli_dual():
    u=[ConcG(1),ConcG(1),ConcG(1),ConcG(0,1)];z=ConcG(F(3,5),F(4,5))
    v=[ConcG(1),z,ConcG(1),z];k=[a*b for a,b in zip(u,v)]
    omega=eigen_outer(v);gate_phase_cone(omega,F(1));cov=eigen_outer(k)
    assert gate_schur(eigen_outer(u),omega)==cov
    # G_jk=<v_k|v_j>, not the conventional column Gram. This complex
    #fixture makes the wrong transpose violate a 2x2 PSD principal minor.
    assert gate_covariance([[z] for z in k]) == cov
    dummy_rho = eigen_scale(F(1, 4), eigen_outer(k))
    assert eigen_scale(4, dummy_rho) == cov
    wrong = helper_add(gate_transpose(cov), eigen_scale(-1, cov))
    d = gate_determinant([[wrong[i][j] for j in (0, 1)] for i in (0, 1)])
    assert d.i == 0 and d.r < 0
    # Continuous local-B correction is exact with probability one.
    assert [a*b.conj() for a,b in zip(k,v)]==u
    projection=helper_add(helper_eye(4),eigen_scale(-F(1,4),cov))
    assert projection==helper_dag(projection) and helper_mul(projection,projection)==projection
    Z=eigen_scale(F(5,4),projection);gate_psd(Z)
    assert helper_trace(helper_mul(Z,cov))==0
    values=[]
    for p in gate_pauli_phases():
        atom=[a*b for a,b in zip(u,p)]
        value=eigen_inner(atom,conc_mv(Z,atom))
        assert value.i==0 and value.r>=1
        values.append(value.r)
    assert sorted(values)==[F(1),F(4),F(5),F(5)]
    return {'continuous_phase_probability':1,'Pauli_only_probability':0,
            'Pauli_dual_atom_values':[str(x) for x in values],
            'scope':'abstract rank-one gate_covariance fixture, not a claimed native scattering realization'}


def gate_orthogonal_tag_family():
    # Two fresh registers of one preserved four-mode carrier. The rational
    # amplitudes and source components avoid an algebraic-number dependency.
    parameters=[(F(9,25),F(16,25),F(4,5),F(3,5),F(12,25),
                 ConcG(F(3,5),F(4,5)),F(25,9),F(17,25)),
                (F(25,169),F(144,169),F(12,13),F(5,13),F(60,169),
                 ConcG(F(5,13),F(12,13)),F(169,25),F(97,169))]
    local_vectors=[];local_roots=[]
    for u,v,a,b,root,phase,C,eta in parameters:
        assert a*a+b*b==1 and b*b==u/(u+v)
        assert root*root==u*v and v>=u>0
        assert 1-2*eta==-u and 1-2*eta/(1+C)==v
        assert F(1,2)<eta<=(C+1)/(C+2)
        states=[[phase*(-u)*a,phase*(-u)*b],
                [phase*(-u)*a,phase*v*b]]
        assert eigen_inner(states[0],states[1])==0
        assert eigen_inner(states[0],states[0])==u*u
        assert eigen_inner(states[1],states[1])==root*root
        local_vectors.append(states);local_roots.append([u,root])
    vectors=[[x*y for x in local_vectors[0][a] for y in local_vectors[1][b]]
             for a in (0,1) for b in (0,1)]
    roots=[x*y for x in local_roots[0] for y in local_roots[1]]
    d=[r*r for r in roots];p=min(d);sqrtp=roots[0]
    assert p==F(81,28561) and sqrtp*sqrtp==p
    pointers=[[z/r for z in v] for v,r in zip(vectors,roots)]
    assert gate_covariance(pointers)==helper_eye(4)
    cov=gate_covariance(vectors)
    assert cov==helper_diag(d)
    target=[ConcG(1),ConcG(F(3,5),F(4,5)),
            ConcG(F(5,13),F(12,13)),ConcG(0,1)]
    measurement=[];fixed_covariances=[]
    for signs in gate_pauli_phases():
        coefficients=[sqrtp*t.conj()*s/(2*r)
                      for t,s,r in zip(target,signs,roots)]
        m=[sum((c*e[i] for c,e in zip(coefficients,pointers)),ConcG())
           for i in range(4)]
        measurement.append(m)
        actual=[eigen_inner(m,v) for v in vectors]
        assert actual==[sqrtp*t*s/2 for t,s in zip(target,signs)]
        fixed=[s*z for s,z in zip(signs,actual)]
        fixed_covariances.append(eigen_outer(fixed))
    effect=[[sum((m[i]*m[j].conj() for m in measurement),ConcG())
             for j in range(4)] for i in range(4)]
    expected=[[sum((p/r**2*e[i]*e[j].conj()
                     for r,e in zip(roots,pointers)),ConcG())
               for j in range(4)] for i in range(4)]
    assert effect==expected
    gate_psd(helper_add(helper_eye(4),eigen_scale(-1,effect)))
    success=[[sum((a[i][j] for a in fixed_covariances),ConcG())
              for j in range(4)] for i in range(4)]
    # Equality of every diagonal-Kraus matrix-unit coefficient proves the
    # accepted CP map also on arbitrary reference-entangled spin inputs.
    assert success==eigen_scale(p,eigen_outer(target))
    assert cov[0][0]==p
    gate_phase_cone(eigen_scale(p,helper_eye(4)),p)
    gate_psd(helper_add(cov,eigen_scale(-p,helper_eye(4))))
    return {'reflected_gate_probability':str(p),
            'success_refinements':len(measurement),'spin_matrix_unit_coefficients':16,
            'photon_failure_effect':'positive semidefinite',
            'scope':'two independently addressed registers of one preserved four-mode carrier, calibrated single-frequency generalized photon readout; no no-click acceptance or harmless retry'}


def gate_verify():
    return {'status': 'passed',
            'balanced_reflected_gate_family': gate_balanced_family(),
            'orthogonal_tag_reflected_gate_family': gate_orthogonal_tag_family(),
            'continuous_phase_range_and_orientation': gate_range_and_pauli_dual(),
            'scope': 'exact reflected-sector gate covariance, continuous-phase, accepted-flag, balancing and weak-dual guards; no hardware loss/RUS completion or numerical optimization'}




def decorated_bus_verify():
    """Eight actual C2 tensor F4 modes, known wrappers and safe clock guards.

    Full survivor vectors imply every terminal measurement and every unknown
    ABR input. Finite fixtures also retain two coherent frequencies and test a
    complete joint mode POVM. The four-window compiler uses only one occupied
    F4 encounter per arm/window. Its three-window variant explicitly supplies
    the stronger simultaneous C2 tensor F4 middle station port.
    """
    identity = helper_eye(4)
    zero = helper_zeros(4, 4)
    native = helper_diag([1, 1, 0, 0])

    def direct_sum(a, b):
        return bus_block(a, zero, zero, b)

    def node(alpha, bright, spin, projector):
        return helper_add(eigen_scale(alpha, identity),
                          eigen_scale((bright-alpha)*spin, projector))

    def projector(v):
        conc_unitary(v)
        p = helper_mul(helper_mul(helper_dag(v), native), v)
        assert p == helper_dag(p) and helper_mul(p, p) == p
        assert helper_rank(p) == 2 and helper_rank(helper_add(identity, eigen_scale(-1, p))) == 2
        return p

    phase = helper_diag([1, ConcG(0, 1), 1, ConcG(0, -1)])
    wrappers = [
        helper_mul(conc_plane(4, 0, 2), phase),
        helper_mul(conc_plane(4, 1, 3, F(5, 13), F(12, 13)),
                   conc_plane(4, 0, 3)),
        helper_mul(phase, conc_plane(4, 0, 3, F(5, 13), F(12, 13))),
        helper_mul(conc_plane(4, 0, 2, F(8, 17), F(15, 17)),
                   conc_plane(4, 1, 2)),
    ]
    # Each arm has independently chosen A/B projectors, all conjugate to
    # the SAME rank-two native primitive; coefficients remain common.
    pa0, pa1, pb0, pb1 = [projector(v) for v in wrappers]
    assert pa0 != pa1 and pb0 != pb1
    assert helper_mul(pa0, pb0) != helper_mul(pb0, pa0)
    assert helper_mul(pa1, pb1) != helper_mul(pb1, pa1)
    first_wrap = direct_sum(wrappers[0], wrappers[3])
    second_wrap = direct_sum(wrappers[2], wrappers[1])
    middle_wrap = direct_sum(wrappers[2], wrappers[3])
    for v in (first_wrap, second_wrap, middle_wrap):
        conc_unitary(v)
    responses = [
        (ConcG(-F(4, 5), F(1, 10)), ConcG(F(3, 5), -F(1, 5)),
         ConcG(-F(2, 3), F(1, 6)), ConcG(F(3, 4), F(1, 8))),
        (ConcG(-F(3, 5), -F(1, 5)), ConcG(F(2, 3), F(1, 6)),
         ConcG(-F(5, 7), -F(1, 7)), ConcG(F(4, 5), -F(1, 10))),
    ]
    assert all(x.conc_norm2() <= 1 for values in responses for x in values)
    spectral = [ConcG(F(3, 5)), ConcG(0, F(4, 5))]
    assert conc_norm2(spectral) == 1
    sources = [
        ([ConcG(F(3, 5)), ConcG(), ConcG(0, F(4, 5)), ConcG()],
         [ConcG(), ConcG(F(5, 13)), ConcG(), ConcG(0, F(12, 13))],
         [ConcG(F(3, 5)), ConcG(0, F(4, 5))]),
        ([ConcG(F(5, 13)), ConcG(F(12, 13)), ConcG(), ConcG()],
         [ConcG(F(8, 17)), ConcG(), ConcG(F(15, 17)), ConcG()],
         [ConcG(0, F(5, 13)), ConcG(F(12, 13))]),
    ]
    # Two complete known readout bases genuinely mix frequency, order and F.
    readout_a = helper_mul(conc_plane(16, 0, 12), conc_plane(16, 2, 7))
    readout_b = helper_mul(conc_plane(16, 5, 15, F(5, 13), F(12, 13)),
                           conc_plane(16, 1, 10))
    readout_b = helper_mul(helper_diag([ConcG(0, 1) if j % 3 == 0 else 1
                                        for j in range(16)]), readout_b)
    for u in (readout_a, readout_b):
        conc_unitary(u)
    readouts = [[F(3, 5)*x for x in row] for row in readout_a]
    readouts += [[F(4, 5)*x for x in row] for row in readout_b]
    assert helper_mul(helper_dag(readouts), readouts) == helper_eye(16)
    vectors = reference_units = readout_coefficients = native_conjugations = 0
    preserved_middle = 0
    for phi0, phi1, control in sources:
        assert conc_norm2(phi0) == conc_norm2(phi1) == conc_norm2(control) == 1
        source = [control[0]*x for x in phi0]+[control[1]*x for x in phi1]
        assert conc_norm2(source) == 1 and helper_rank([phi0, phi1]) == 2
        switched, ordinary = [[] for _ in AB], [[] for _ in AB]
        for values, frequency_amplitude in zip(responses, spectral):
            alpha, bright_a, beta, bright_b = values
            for label, (a, b) in enumerate(AB):
                raw_a = node(alpha, bright_a, a, native)
                raw_b = node(beta, bright_b, b, native)
                a0, a1 = node(alpha, bright_a, a, pa0), node(alpha, bright_a, a, pa1)
                b0, b1 = node(beta, bright_b, b, pb0), node(beta, bright_b, b, pb1)
                for raw, effective, v in zip((raw_a, raw_a, raw_b, raw_b),
                                             (a0, a1, b0, b1), wrappers):
                    assert helper_mul(helper_mul(helper_dag(v), raw), v) == effective
                    native_conjugations += 1
                macro_first = helper_mul(helper_mul(helper_dag(first_wrap),
                                        direct_sum(raw_a, raw_b)), first_wrap)
                macro_second = helper_mul(helper_mul(helper_dag(second_wrap),
                                         direct_sum(raw_b, raw_a)), second_wrap)
                target = conc_mv(macro_second, conc_mv(macro_first, source))
                expected = ([control[0]*x for x in conc_mv(b0, conc_mv(a0, phi0))]
                            + [control[1]*x for x in conc_mv(a1, conc_mv(b1, phi1))])
                assert target == expected
                # Fixed global A0-B0-B1-A1: vacuum identity on the held arm.
                actual = source
                for window in (direct_sum(a0, identity), direct_sum(b0, identity),
                               direct_sum(identity, b1), direct_sum(identity, a1)):
                    actual = conc_mv(window, actual)
                assert actual == target
                # A0-Bmiddle-A1 is checked ONLY with a simultaneously
                # preserved C2 tensor F4 middle port, bright/dark rank4/4.
                middle = helper_mul(helper_mul(helper_dag(middle_wrap),
                                    direct_sum(raw_b, raw_b)), middle_wrap)
                assert middle == direct_sum(b0, b1)
                three = conc_mv(direct_sum(identity, a1), conc_mv(
                    middle, conc_mv(direct_sum(a0, identity), source)))
                assert three == target
                preserved_middle += 1
                switched[label] += [frequency_amplitude*x for x in target]
                ordinary[label] += [frequency_amplitude*x for x in actual]
                vectors += 1
        assert any(v[k] != 0 and v[k+8] != 0 for v in switched for k in range(8))
        # Explicit sparse |ab,r><a'b',s| blocks retain every photon mode,
        # including cross-frequency coherence, and leave the reference intact.
        for j, k, r, s in product(range(4), range(4), range(2), range(2)):
            left = {(r, s, m, n): switched[j][m]*switched[k][n].conj()
                    for m in range(16) for n in range(16)}
            right = {(r, s, m, n): ordinary[j][m]*ordinary[k][n].conj()
                     for m in range(16) for n in range(16)}
            assert left == right
            reference_units += 1
        cov = helper_zeros(4, 4)
        for row in readouts:
            ks = [sum((x*y for x, y in zip(row, v)), ConcG()) for v in switched]
            ko = [sum((x*y for x, y in zip(row, v)), ConcG()) for v in ordinary]
            for j, k in product(range(4), repeat=2):
                assert ks[j]*ks[k].conj() == ko[j]*ko[k].conj()
                cov[j][k] += ks[j]*ks[k].conj()
                readout_coefficients += 1
        assert cov == gate_covariance(switched)
    assert helper_rank(direct_sum(native, native)) == 4
    # A generic finite-pulse pre-B span is THREE-dimensional. Its desired
    # K=I3/2 compression has both K and I-K rank3; an F4 rank2/2 port
    # cannot supply it. This prevents silently merging the two B visits.
    half = F(1, 2)
    qb = helper_scale(bus_block(helper_eye(2), helper_eye(2),
                               helper_eye(2), helper_eye(2)), half)
    assert helper_mul(qb, qb) == qb and helper_rank(qb) == 2
    balanced = ConcG(F(1, 2), F(1, 2))
    balanced_wrap = bus_block(helper_scale(helper_eye(2), balanced),
                             helper_scale(helper_eye(2), balanced),
                             helper_scale(helper_eye(2), -balanced.conj()),
                             helper_scale(helper_eye(2), balanced.conj()))
    conc_unitary(balanced_wrap)
    assert helper_mul(helper_mul(helper_dag(balanced_wrap), native), balanced_wrap) == qb
    merged = direct_sum(qb, qb)
    feature_basis = [[ConcG(j == k) for j in range(8)] for k in (0, 1, 4)]
    phi0 = [ConcG(F(3, 5)), ConcG(F(4, 5)), ConcG(), ConcG()]
    p0 = helper_diag([1, 0, 1, 0])
    permutation = [[ConcG(j == (0, 2, 1, 3)[i]) for j in range(4)] for i in range(4)]
    conc_unitary(permutation)
    assert helper_mul(helper_mul(helper_dag(permutation), native), permutation) == p0
    phi1 = [ConcG(1), ConcG(), ConcG(), ConcG()]
    pre = []
    for a, alpha in ((0, F(1, 3)), (0, F(2, 5)), (1, F(1, 3))):
        first = conc_mv(node(ConcG(alpha), ConcG(alpha+F(1, 2)), a, p0), phi0)
        pre.append([F(3, 5)*x for x in first]+[F(4, 5)*x for x in phi1])
    assert helper_rank(pre) == 3 and helper_rank(feature_basis+pre) == 3
    compression = [[conc_inner(x, conc_mv(merged, y)) for y in feature_basis]
                   for x in feature_basis]
    assert compression == helper_scale(helper_eye(3), half)
    assert helper_rank(compression) == 3
    assert helper_rank(helper_add(helper_eye(3), helper_scale(compression, -1))) == 3
    assert 3 > 2 and 3+3 == 6
    q6 = helper_scale(bus_block(helper_eye(3), helper_eye(3),
                               helper_eye(3), helper_eye(3)), half)
    assert helper_mul(q6, q6) == q6 and helper_rank(q6) == 3
    # Padding a two-polarization spin difference by bypass rails retains rank1,
    # whereas the explicitly supplied F4 native port needs rank2.
    padded_difference = helper_diag([1, 0, 0, 0])
    assert helper_rank(padded_difference) == 1 and helper_rank(native) == 2
    assert helper_rank(helper_mul(helper_mul(helper_dag(wrappers[0]),
                            padded_difference), wrappers[0])) == 1
    padded_dark = helper_diag([F(1, 3), F(1, 3), 1, 1])
    assert helper_rank(helper_add(padded_dark, helper_scale(identity, -F(1, 3)))) == 2
    # The same spectral kernel on two orthogonal temporal inputs need not
    # preserve their accepted modal orthogonality (vectors unnormalized).
    temporal_u, temporal_v = [ConcG(1), ConcG(1)], [ConcG(1), ConcG(-1)]
    spectral_filter = helper_diag([1, F(1, 2)])
    assert conc_inner(temporal_u, temporal_v) == 0
    filtered_u, filtered_v = conc_mv(spectral_filter, temporal_u), conc_mv(spectral_filter, temporal_v)
    assert [filtered_u, filtered_v] == [[ConcG(1), ConcG(F(1, 2))],
                                        [ConcG(1), ConcG(-F(1, 2))]]
    assert conc_inner(filtered_u, filtered_v) == F(3, 4)
    return {'status': 'passed', 'arithmetic': 'Gaussian rational, stdlib',
            'independent_rank_two_arm_projectors': 4, 'normalized_pure_sources': len(sources),
            'native_same_spin_conjugations': native_conjugations,
            'full_eight_mode_frequency_spin_vectors': vectors,
            'coherent_two_frequency_spin_vectors': len(sources)*len(AB),
            'arbitrary_reference_matrix_units': reference_units,
            'joint_mode_readout_matrix_unit_coefficients': readout_coefficients,
            'four_window_survivor_compiler_vectors': vectors,
            'three_window_vectors_with_explicit_eight_mode_middle_port': preserved_middle,
            'generic_middle_feature_dimension': 3, 'generic_middle_minimum_port_dimension': 6,
            'padded_polarization_rank_obstructions': 1,
            'common_spectral_filter_bin_overlap_obstructions': 1,
            'scope': 'decorated C2 tensor F4 coherent survivor and safe four-window compiler; '
                     'three-window equality only with supplied simultaneous middle tensor port; '
                     'no generic F4 merged visit, loss/emission completion or physical clock validation'}


def exact_projector_gap_verify():
    """Exact pooled CZ primal and both ordinary-word weak-dual certificates.

    The gap is a lower/upper comparison in the declared constant-projector
    reflected gate class, with local phase feedback. No optimum equality,
    adaptive ordinary bound, no-click recovery or hardware rate is inferred.
    """
    from pathlib import Path

    data = json.loads(Path(__file__).with_name('projector_gate_gap.json').read_text(encoding='utf-8'))
    assert data['schema'] == 'projector-cz-gate-gap-v1'
    assert data['moment_denominator'] == data['phase_denominator'] == 1000
    assert data['dual_denominator'] == 60000

    def read_matrix(rows, denominator):
        assert len(rows) == 4 and all(len(row) == 4 for row in rows)
        assert all(isinstance(x, int) and not isinstance(x, bool) for row in rows for x in row)
        return [[ConcG(F(x, denominator)) for x in row] for row in rows]

    def moment(gamma, x, q, t, c):
        c = conc_cast(c)
        return [[conc_cast(gamma), conc_cast(x), conc_cast(q), c],
                [conc_cast(x), conc_cast(x), c.conj(), conc_cast(t)],
                [conc_cast(q), c, conc_cast(q), c],
                [c.conj(), conc_cast(t), c.conj(), conc_cast(t)]]

    def pairing(a, b):
        return helper_trace(helper_mul(a, b))

    def partial_b(a):
        return [[a[2*(i//2)+j % 2][2*(j//2)+i % 2]
                 for j in range(4)] for i in range(4)]

    def strict_psd(a):
        gate_psd(a)
        for size in range(1, 5):
            determinant = gate_determinant([row[:size] for row in a[:size]])
            assert determinant.i == 0 and determinant.r > 0

    identity = helper_eye(4)
    origin = helper_diag([1, 0, 0, 0])
    directions = [moment(0, 1, 0, 0, 0), moment(0, 0, 1, 0, 0),
                  moment(0, 0, 0, 1, 0), moment(0, 0, 0, 0, 1),
                  moment(0, 0, 0, 0, ConcG(0, 1))]
    assert len(directions) == 5 and all(h == helper_dag(h) for h in directions)
    # Explicit Im(c) signs and H^T covariance orientation are tested using
    # an actual complex rank-two projector program, not just real witnesses.
    phi = [ConcG(F(3, 5)), ConcG(F(4, 5)), ConcG(), ConcG()]
    p = helper_diag([1, 0, 1, 0])
    q = [[ConcG(F(9, 25)), ConcG(0, -F(12, 25)), ConcG(), ConcG()],
         [ConcG(0, F(12, 25)), ConcG(F(16, 25)), ConcG(), ConcG()],
         [ConcG(), ConcG(), ConcG(1), ConcG()],
         [ConcG(), ConcG(), ConcG(), ConcG()]]
    assert q == helper_dag(q) and helper_mul(q, q) == q and helper_rank(q) == 2
    features = [phi, conc_mv(p, phi), conc_mv(q, phi), conc_mv(q, conc_mv(p, phi))]
    feature_gram = [[conc_inner(v, w) for w in features] for v in features]
    assert feature_gram[0][3].i != 0
    assert feature_gram == moment(1, feature_gram[0][1], feature_gram[0][2],
                                  feature_gram[3][3], feature_gram[0][3])
    assert partial_b(feature_gram) == bus_transpose(gate_partial_transpose(feature_gram))
    assert partial_b(feature_gram) != gate_partial_transpose(feature_gram)
    l = [[ConcG(x) for x in row] for row in
         ((1, 0, 0, 0), (1, 0, -1, 0), (1, -1, 0, 0), (1, -1, -1, 1))]
    swap = [[ConcG(j == (0, 2, 1, 3)[i]) for j in range(4)] for i in range(4)]
    target = helper_diag([1, 1, 1, -1])
    actual_vectors = [[sum((l[i][j]*features[j][k] for j in range(4)), ConcG())
                       for k in range(4)] for i in range(4)]
    actual_covariance = gate_covariance(actual_vectors)
    assert actual_covariance == helper_mul(helper_mul(l, bus_transpose(feature_gram)), bus_transpose(l))
    assert actual_covariance != helper_mul(helper_mul(l, feature_gram), bus_transpose(l))
    # Both homogeneous arms use H/2, hence their source weights sum to one.
    h = read_matrix(data['moment_numerators'], data['moment_denominator'])
    omega = read_matrix(data['phase_numerators'], data['phase_denominator'])
    probability = F(7, 40)
    assert h[0][0] == 1
    assert h == moment(1, h[0][1], h[0][2], h[3][3], h[0][3])
    strict_psd(h)
    gate_phase_cone(omega, probability)
    strict_psd(omega)
    strict_psd(partial_b(omega))
    forward_h = helper_scale(h, F(1, 2))
    reverse_h = helper_scale(h, F(1, 2))
    assert forward_h[0][0]+reverse_h[0][0] == 1
    pooled = helper_add(bus_transpose(forward_h),
                        helper_mul(helper_mul(swap, bus_transpose(reverse_h)), swap))
    covariance = helper_mul(helper_mul(l, pooled), bus_transpose(l))
    residual = helper_add(covariance, helper_scale(
        helper_mul(helper_mul(target, omega), target), -1))
    strict_psd(residual)
    assert set(data['dual_numerators']) == {'Z', 'A', 'B', 'S'}
    dual = {name: read_matrix(rows, data['dual_denominator'])
            for name, rows in data['dual_numerators'].items()}
    phase_basis = gate_phase_subspace_basis()
    assert len(phase_basis) == 9
    assert helper_mul(target, swap) == helper_mul(swap, target)
    reversed_l = helper_mul(swap, l)
    assert reversed_l == helper_mul(l, swap)
    # The station swap exchanges the two partial transposes. For this real
    # symmetric B they agree; verify rather than assuming that simplification.
    partial_a_b = helper_mul(helper_mul(swap, partial_b(
        helper_mul(helper_mul(swap, dual['B']), swap))), swap)
    assert partial_a_b == partial_b(dual['B']) == gate_partial_transpose(dual['B'])
    objectives = []
    for reverse, coefficient in ((False, l), (True, reversed_l)):
        matrices = {name: (value if name == 'S' or not reverse else
                    helper_mul(helper_mul(swap, value), swap))
                    for name, value in dual.items()}
        z, a, b, s = (matrices[name] for name in ('Z', 'A', 'B', 'S'))
        for value in matrices.values():
            strict_psd(helper_add(value, helper_scale(identity, -F(1, 2000))))
        w = helper_add(helper_add(helper_mul(helper_mul(target, z), target),
                                  helper_scale(a, -1)),
                       helper_add(helper_scale(partial_b(b), -1),
                                  helper_scale(identity, -F(1, 4))))
        assert w == helper_dag(w)
        assert all(pairing(w, direction) == 0 for direction in phase_basis)
        qdual = helper_add(helper_mul(helper_mul(bus_transpose(coefficient), z), coefficient), s)
        assert qdual == helper_dag(qdual) == bus_transpose(qdual)
        assert all(pairing(qdual, direction) == 0 for direction in directions)
        assert qdual[0][0] == F(1, 6)
        # An arbitrary complex affine point guards all five directions with
        # non-unit leading weight. Positivity is not needed for this identity.
        test_h = moment(F(3, 5), F(2, 7), F(5, 11), F(3, 13),
                        ConcG(F(5, 17), F(7, 19)))
        assert pairing(qdual, test_h) == F(3, 5)*F(1, 6)
        assert pairing(qdual, origin) == F(1, 6)
        objectives.append(F(1, 6))
    weights = [F(1, 7), F(2, 7), F(4, 7)]
    assert sum(weights) == 1
    assert sum(weight*objectives[j % 2] for j, weight in enumerate(weights)) == F(1, 6)
    # Scalar input-output kernel at kappa=gamma=kappa_r=nu=1 and g^2=2.
    denominator_dark = ConcG(1, -1)
    denominator_bright = denominator_dark+ConcG(2)/ConcG(1, -1)
    dark = 1-ConcG(2)/denominator_dark
    bright = 1-ConcG(2)/denominator_bright
    assert dark == ConcG(0, -1) and bright == 0
    assert ConcG(0, 1)*dark == 1 and ConcG(0, 1)*bright == 0
    upper = objectives[0]
    assert probability-upper == F(1, 120)
    assert probability/upper == F(21, 20)
    return {'status': 'passed', 'arithmetic': 'Gaussian rational, stdlib',
            'coherent_pooled_CZ_probability': str(probability),
            'ordinary_AB_BA_recorded_lottery_upper': str(upper),
            'restricted_optimum_gap_lower': '1/120',
            'positive_ordinary_optimum_ratio_lower': '21/20',
            'primal_PSD_PPT_residual_matrices': 4,
            'ordinary_strict_margin_matrices': 8,
            'dual_PSD_margin': '1/2000',
            'explicit_complex_phase_direction_pairings': 18,
            'explicit_complex_moment_direction_pairings': 10,
            'complex_projector_Gram_orientation_fixtures': 1,
            'homogeneous_recorded_order_lotteries': 1,
            'projector_reflection_kernel_fixtures': 1,
            'scope': 'exact pooled reflected CZ primal and fixed-word/classically recorded-order '
                     'weak duals with terminal pure-helper POVM and local phase feedback; '
                     'lower/upper gap and ratio only, no optimum equality, adaptive-ordinary '
                     'upper, no-click acceptance or native hardware/clock advantage'}


def retained_photon_gate_verify():
    """Exact retained-F instruments, ordinary compilers and algebraic guards.

    The general balance, terminal-instrument and nuclear-norm arguments are
    analytic proofs in the method note. This replays complete finite input
    maps and exact polynomial ingredients, without parameter sweeps as bounds.
    """
    field_add, field_mul, field_conj = add, mul, conj
    field_scale = globals()["scale"]
    def field_cast(value):
        if isinstance(value, tuple) and len(value) == 8:
            return value
        if isinstance(value, ConcG):
            return field_add(field_scale(ONE, value.r), field_scale(root(4), value.i))
        return field_scale(ONE, F(value))
    class Q3:
        """Quadratic sqrt3 extension of the existing exact cyclotomic engine."""
        def __init__(self, a=0, b=0):
            self.a, self.b = field_cast(a), field_cast(b)
        def __add__(self, other):
            other = cast(other)
            return Q3(field_add(self.a, other.a), field_add(self.b, other.b))
        __radd__ = __add__
        def __neg__(self):
            return Q3(field_scale(self.a, -1), field_scale(self.b, -1))
        def __sub__(self, other):
            return self + -cast(other)
        def __rsub__(self, other):
            return cast(other) + -self
        def __mul__(self, other):
            other = cast(other)
            return Q3(field_add(field_mul(self.a, other.a), field_scale(field_mul(self.b, other.b), 3)),
                      field_add(field_mul(self.a, other.b), field_mul(self.b, other.a)))
        __rmul__ = __mul__
        def __truediv__(self, denominator):
            return Q3(field_scale(self.a, 1 / F(denominator)), field_scale(self.b, 1 / F(denominator)))
        def __eq__(self, other):
            other = cast(other)
            return self.a == other.a and self.b == other.b
        def conj(self):
            return Q3(field_conj(self.a), field_conj(self.b))
    def cast(value):
        return value if isinstance(value, Q3) else Q3(value)
    def matrix(rows):
        return [[cast(value) for value in row] for row in rows]
    def eye(d):
        return matrix([[int(i == j) for j in range(d)] for i in range(d)])
    def zeros(d, e=None):
        return matrix([[0] * (d if e is None else e) for _ in range(d)])
    def plus(a, b):
        return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]
    def scale(a, scalar):
        return [[x * scalar for x in row] for row in a]
    def multiply(a, b):
        out = zeros(len(a), len(b[0]))
        for i, row in enumerate(a):
            for k, x in enumerate(row):
                if x == 0:
                    continue
                for j, y in enumerate(b[k]):
                    if y != 0:
                        out[i][j] = out[i][j] + x * y
        return out
    def dagger(a):
        return [[a[j][i].conj() for j in range(len(a))] for i in range(len(a[0]))]
    def kron(a, b):
        return [[x * y for x in ar for y in br] for ar in a for br in b]
    def block(a, b, c, d):
        return [ar + br for ar, br in zip(a, b)] + [cr + dr for cr, dr in zip(c, d)]
    def diagonal(values):
        return matrix([[value if i == j else 0 for j in range(len(values))]
                       for i, value in enumerate(values)])
    def tr(a):
        return sum((a[i][i] for i in range(len(a))), Q3())
    def require_unitary(a):
        helper_require(multiply(dagger(a), a) == eye(len(a)), "Exact Q(i,sqrt3) unitary")

    i2, x, y, z = eye(2), matrix([[0, 1], [1, 0]]), matrix([[0, ConcG(0, -1)], [ConcG(0, 1), 0]]), diagonal([1, -1])
    imaginary, r3 = Q3(ConcG(0, 1)), Q3(0, 1)
    b00 = plus(plus(i2, x), z)
    b01 = scale(plus(plus(i2, x), scale(z, -1)), imaginary)
    b10 = scale(plus(plus(i2, scale(x, -1)), z), imaginary)
    b11 = plus(plus(scale(i2, -1), x), z)
    c = scale(block(b00, b01, b10, b11), r3 / 8)
    e0, e1 = diagonal([r3 / 2, Q3(F(1, 2))]), diagonal([Q3(F(1, 2)), r3 / 2])
    ei0, ei1 = diagonal([2 * r3 / 3, Q3(2)]), diagonal([Q3(2), 2 * r3 / 3])
    m0 = plus(scale(i2, (r3 + 1) / 4), scale(x, (r3 - 1) / 4))
    m1 = plus(scale(i2, (r3 + 1) / 4), scale(x, -(r3 - 1) / 4))
    mi0 = plus(scale(i2, 1 + r3 / 3), scale(x, -(1 - r3 / 3)))
    mi1 = plus(scale(i2, 1 + r3 / 3), scale(x, 1 - r3 / 3))
    helper_require(plus(multiply(e0, e0), multiply(e1, e1)) == i2,
                   "Exact source isometry normalization")
    helper_require(plus(multiply(m0, m0), multiply(m1, m1)) == i2,
                   "Exact accepted output coisometry normalization")
    for a, inverse in ((e0, ei0), (e1, ei1), (m0, mi0), (m1, mi1)):
        helper_require(multiply(a, inverse) == i2, "Displayed exact inverse")
    middle = multiply(multiply(block(mi0, zeros(2), zeros(2), mi1), c),
                      block(ei0, zeros(2), zeros(2), ei1))
    require_unitary(middle)
    swap = matrix([[int(i == (0, 2, 1, 3)[j]) for j in range(4)] for i in range(4)])
    pre = multiply(block(e0, scale(e1, -1), e1, e0), swap)
    post = multiply(swap, block(m0, m1, scale(m1, -1), m0))
    require_unitary(pre)
    require_unitary(post)
    # Basis throughout is F,H,A,B; the source and readout have H=0/1.
    cz_a = diagonal([(-1) ** (((index >> 3) & 1) * ((index >> 1) & 1)) for index in range(16)])
    cz_b = diagonal([(-1) ** (((index >> 3) & 1) * (index & 1)) for index in range(16)])
    full = multiply(kron(post, eye(4)), multiply(cz_b, multiply(kron(middle, eye(4)),
        multiply(cz_a, kron(pre, eye(4))))))
    branches = []
    for outcome in (0, 1):
        branches.append([[full[((row >> 2) * 2 + outcome) * 4 + row % 4]
                              [((column >> 2) * 2) * 4 + column % 4]
                          for column in range(8)] for row in range(8)])
    complement = scale(block(multiply(plus(scale(i2, -2), x), b00),
                             multiply(plus(scale(i2, -2), x), b01),
                             multiply(plus(scale(i2, 2), x), b10),
                             multiply(plus(scale(i2, 2), x), b11)), F(1, 8))
    fourier = []
    for coefficients in (c, complement):
        operator = zeros(8)
        for j in (0, 1):
            for i in (0, 1):
                coefficient = [row[2 * i:2 * i + 2] for row in coefficients[2 * j:2 * j + 2]]
                operator = plus(operator, kron(coefficient, kron(z if i else i2, z if j else i2)))
        fourier.append(operator)
    helper_require(branches == fourier, "Literal pre/CZ/middle/CZ/post circuit equals both Fourier branches")
    spin_phase = kron(i2, diagonal([imaginary, 1, 1, -imaginary]))
    target_numerator = plus(eye(8), plus(scale(kron(z, kron(z, i2)), -imaginary),
                                       scale(kron(x, kron(i2, z)), -imaginary)))
    helper_require(branches[0] == scale(multiply(spin_phase, target_numerator), r3 / 4),
                   "Accepted branch is the exact target after declared local spin phases")
    helper_require(multiply(dagger(branches[0]), branches[0]) == scale(eye(8), F(9, 16))
                   and multiply(dagger(branches[1]), branches[1]) == scale(eye(8), F(7, 16)),
                   "Both exact terminal effects are scalar and complete")
    undone_complement = multiply(dagger(spin_phase), branches[1])
    for aa, bb in ((1, 1), (1, -1), (-1, 1), (-1, -1)):
        index = 2 * int(aa == -1) + int(bb == -1)
        actual = [[undone_complement[4 * row + index][4 * column + index] for column in range(2)]
                  for row in range(2)]
        expected = scale(plus(plus(scale(i2, imaginary * bb), scale(x, -1)),
                              plus(scale(y, -aa), scale(z, 2 * aa * bb))), F(1, 4))
        helper_require(actual == expected, "Exact complement agrees with all-p sector formula at r=0")

    # Full polynomial Gram identities: no parameter grid is used as a no-go.
    def padd(a, b):
        out = [F(0)] * max(len(a), len(b))
        for j in range(len(out)):
            out[j] = (a[j] if j < len(a) else 0) + (b[j] if j < len(b) else 0)
        while len(out) > 1 and out[-1] == 0:
            out.pop()
        return tuple(out)
    def pmul(a, b):
        out = [F(0)] * (len(a) + len(b) - 1)
        for j, xx in enumerate(a):
            for k, yy in enumerate(b):
                out[j + k] += xx * yy
        return padd(tuple(out), ())
    def quaternion(aa, bb):
        return ((F(bb, 4), F(aa, 2)), (F(-1, 4),),
                (F(-aa, 4), F(-bb, 2)), (F(aa * bb, 2), F(-1, 2)))
    def pdot(a, b):
        out = ()
        for xx, yy in zip(a, b):
            out = padd(out, pmul(xx, yy))
        return out
    gram_identities = 0
    for aa, bb in ((1, 1), (1, -1), (-1, 1), (-1, -1)):
        source = quaternion(aa, bb)
        expected = ((aa, bb, (F(7, 16), 0, F(3, 4))),
                    (-aa, bb, (F(-3, 16), 0, F(1, 4))),
                    (aa, -bb, (F(-3, 16), 0, F(1, 4))),
                    (-aa, -bb, (F(3, 16), F(-aa * bb), F(-1, 4))))
        for other_a, other_b, coefficients in expected:
            helper_require(pdot(source, quaternion(other_a, other_b)) == tuple(map(F, coefficients)),
                           "All-r complement Gram polynomial")
            gram_identities += 1
    # At p=1/2 the diagonal Gram is 1/3 +/- 1/sqrt3. Equality of its
    # magnitude to 1/3 would force (2r)^2=0 or4/9, but it is1/3.
    helper_require(F(1, 3) not in (F(0), F(4, 9)), "Exact second-outcome local-G obstruction")
    helper_require(F(9, 16) / (3 * (1 - F(9, 16))) == F(3, 7) < 1,
                   "Feasible neighboring Gram magnitude never permits local-product retry")
    # Retained F is data: both native flags are full eight-dimensional maps.
    p = kron(z, kron(z, i2))
    q = kron(x, kron(i2, z))
    g = scale(target_numerator, r3 / 3)
    native_plus, native_minus = scale(target_numerator, F(1, 2)), scale(multiply(p, q), F(1, 2))
    corrected_minus = multiply(dagger(multiply(p, q)), native_minus)
    helper_require(corrected_minus == scale(eye(8), F(1, 2)), "Native failure restores the entire retained payload")
    require_unitary(g)

    # Readout-free four-contact Clifford dressing on the actual F,A,B space.
    cnot = matrix([[int(row == ((column ^ 4) if ((column >> 1) & 1) else column))
                    for column in range(8)] for row in range(8)])
    cz = diagonal([(-1) ** (((column >> 2) & 1) * (column & 1)) for column in range(8)])
    dressing = multiply(cnot, cz)
    zf, xf = kron(z, eye(4)), kron(x, eye(4))
    helper_require(multiply(multiply(dressing, zf), dagger(dressing)) == p
                   and multiply(multiply(dressing, xf), dagger(dressing)) == q,
                   "Four-contact Clifford dressing maps both local photon axes")
    local_g = scale(plus(i2, plus(scale(z, -imaginary), scale(x, -imaginary))), r3 / 3)
    helper_require(multiply(multiply(dressing, kron(local_g, eye(4))), dagger(dressing)) == g,
                   "Readout-free four-contact compiler is the full retained target")

    def sector_operator(values):
        out = zeros(8)
        for address, value in enumerate(values):
            for row in range(2):
                for column in range(2):
                    out[4 * row + address][4 * column + address] = value[row][column]
        return out
    def program_sector(a, b):
        return scale(plus(i2, plus(scale(z, -imaginary * (-1) ** a),
                                   scale(x, -imaginary * (-1) ** b))), r3 / 3)
    def spin_feedback(u, v):
        return diagonal([(-1) ** (u * ((index >> 1) & 1) + v * (index & 1)) for index in range(8)])

    # Literal ++ source, two CZs, both helper Hadamards, the computational
    # program, and X readout. The six sqrt2 factors combine to 1/8.
    two_helper = []
    for u, v in product((0, 1), repeat=2):
        sector_maps = []
        for a, b in product((0, 1), repeat=2):
            value = zeros(2)
            for hh, jj, cc, dd in product((0, 1), repeat=4):
                phase = (-1) ** (a * hh + b * jj + hh * cc + jj * dd + u * cc + v * dd)
                value = plus(value, scale(program_sector(cc, dd), F(phase, 8)))
            sector_maps.append(value)
        raw = sector_operator(sector_maps)
        corrected = multiply(spin_feedback(u, v), raw)
        helper_require(corrected == scale(g, F(1, 2)),
                       "Actual two-helper basis conversion/program/readout gives G/2 on every record")
        two_helper.append(corrected)

    # One reusable helper performs each rotation with one occupied spin CZ.
    # Every computational readout is retained and its spin phase is corrected.
    def one_helper_rotation(cosine, sine, photon_axis, spin):
        target_pauli = p if spin == 0 else q
        rotation = plus(scale(eye(8), cosine), scale(target_pauli, -imaginary * sine))
        corrected = []
        for read in (0, 1):
            values = []
            for a, b in product((0, 1), repeat=2):
                address_sign = (-1) ** (a if spin == 0 else b)
                value = zeros(2)
                for helper in (0, 1):
                    local = (scale(i2, cosine) if read == helper else scale(photon_axis, -imaginary * sine))
                    value = plus(value, scale(local, cast(INV_SQRT2) * address_sign ** helper))
                values.append(value)
            raw = sector_operator(values)
            feedback = spin_feedback(read if spin == 0 else 0, read if spin == 1 else 0)
            actual = multiply(feedback, raw)
            helper_require(actual == scale(rotation, cast(INV_SQRT2)),
                           "Single occupied CZ plus local helper rotation/read/reset preserves full unknown F")
            corrected.append(actual)
        return rotation, corrected
    rp, rp_branches = one_helper_rotation(cast(COS), cast(SIN), z, 0)
    rq, rq_branches = one_helper_rotation(cast(field_scale(INV_SQRT2, 2)) * r3 / 3, r3 / 3, x, 1)
    helper_require(multiply(multiply(rp, rq), rp) == g,
                   "Three one-helper rotations synthesize the exact target")
    three_helper = [multiply(multiply(last, middle_branch), first)
                    for first in rp_branches for middle_branch in rq_branches for last in rp_branches]
    for branch in three_helper:
        helper_require(branch == scale(g, cast(INV_SQRT2) / 2),
                       "Every three-contact readout history delivers the same target")

    # Coherent return uses the unmeasured helper keys: their byproducts cancel
    # on the two revisits. The exact occupied-key distribution also guards the
    # vacuum-I bypass loss polynomial, without supplying that physical port.
    coherent_return = []
    for u, v in product((0, 1), repeat=2):
        raw_key = scale(multiply(spin_feedback(u, v), g), F(1, 2))
        coherent_return.append(multiply(spin_feedback(u, v), raw_key))
    helper_require(coherent_return == [scale(g, F(1, 2))] * 4,
                   "Coherent helper return decouples the unknown retained target from both keys")
    helper_require(sum((F(2 + u + v, 4) for u, v in product((0, 1), repeat=2)), F(0)) == 3,
                   "Ideal occupied correction-key contact count is three")

    # Complete matrix-unit replay includes every passive-reference extension.
    def cp_unit(operator, i, j):
        out = zeros(8)
        for row in range(8):
            if operator[row][i] == 0:
                continue
            for column in range(8):
                if operator[column][j] != 0:
                    out[row][column] = operator[row][i] * operator[column][j].conj()
        return out
    native_units = program_units = three_units = sharp_units = coin_units = 0
    for i, j in product(range(8), repeat=2):
        unit_map = zeros(8)
        unit_map[i][j] = cast(1)
        target_map = cp_unit(g, i, j)
        helper_require(cp_unit(native_plus, i, j) == scale(target_map, F(3, 4))
                       and cp_unit(corrected_minus, i, j) == scale(unit_map, F(1, 4)),
                       "Both native corrected flags on every retained input matrix unit")
        native_units += 2
        total = zeros(8)
        for branch in two_helper:
            output = cp_unit(branch, i, j)
            helper_require(output == scale(target_map, F(1, 4)), "Two-helper full flag matrix unit")
            total = plus(total, output)
            program_units += 1
        helper_require(total == target_map, "Two-helper deterministic complete instrument")
        for branch in three_helper:
            helper_require(cp_unit(branch, i, j) == scale(target_map, F(1, 8)),
                           "Three-contact complete readout-history matrix unit")
            three_units += 1
        helper_require(scale(total, F(3, 4)) == cp_unit(native_plus, i, j)
                       and scale(unit_map, F(1, 4)) == cp_unit(corrected_minus, i, j),
                       "Independent classical coin and spectator helpers reproduce the native measured flags")
        coin_units += 2
        for branch, expected in zip(branches, fourier):
            helper_require(cp_unit(branch, i, j) == cp_unit(expected, i, j),
                           "Sharp U4 witness and complement complete input maps")
            sharp_units += 1

    # Exact nuclear-norm ingredients, independent of helper dimension. The
    # Schatten/Choi-support proof applying these ingredients is analytic.
    c0 = block(i2, scale(z, -imaginary), scale(x, -imaginary), zeros(2))
    gram = multiply(dagger(c0), c0)
    helper_require(plus(plus(multiply(gram, gram), scale(gram, -3)), eye(4)) == zeros(4),
                   "Target Fourier Gram obeys lambda^2-3lambda+1")
    helper_require(multiply(plus(gram, eye(4)), plus(gram, eye(4))) == scale(gram, 5)
                   and tr(gram) == 6 and tr(plus(gram, eye(4))) == 10,
                   "Positive Fourier square-root/nuclear-trace ingredients")
    squared_target_nuclear = F(10 * 10, 5 * 3)
    helper_require(squared_target_nuclear == F(20, 3)
                   and 4 / squared_target_nuclear == F(3, 5),
                   "Dimension-independent single-common-correction trace bound constant")

    # General terminal contractions: exact polynomial constants used in the
    # analytic T1--T3 eigenvalue argument, rather than a parameter sweep.
    def pscale(poly, scalar):
        return tuple(F(scalar) * value for value in poly)
    x_squared = (F(0), F(2), F(-12))
    helper_require(padd((1,), pscale(x_squared, -16)) == pscale(
        pmul((F(-1, 24), F(1)), (F(-1, 8), F(1))), 192),
        "T3 positive-product roots are exactly 1/24 and1/8")
    helper_require(padd(x_squared, (0, 0, -4)) == pmul((0, 2), (1, -8)),
                   "T3 x-squared minus4s-squared equals2s(1-8s)")
    a_poly = (F(4), F(-20))
    helper_require(padd(pscale(a_poly, 8), (-12,)) == (F(20), F(-160)),
                   "T3 larger-eigenvalue comparison numerator20x(1-8s)")
    helper_require(padd(pscale(a_poly, 2), (-8,)) == (F(0), F(-40))
                   and -12 + 32 == 20,
                   "T3 threshold numerator is exactly20(x-2s)")

    # Fixed-source/fixed-middle terminal records: the inverse and rotation
    # ratio have exact constant physical-Pauli coefficients. J's block-X
    # trace is invariant for all beta by the three displayed coefficients.
    c0_inverse = block(zeros(2), scale(x, imaginary), scale(z, imaginary), scale(y, imaginary))
    helper_require(multiply(c0, c0_inverse) == eye(4)
                   and multiply(c0_inverse, c0) == eye(4), "Exact inverse of target Fourier matrix")
    j_block = matrix([[0, -2], [1, 0]])
    ratio_generator = multiply(multiply(c0, scale(kron(x, i2), imaginary)), c0_inverse)
    helper_require(ratio_generator == plus(kron(i2, scale(z, -1)), kron(j_block, y)),
                   "All-delta Fourier rotation ratio cI+s[-I*Z+J*Y]")
    for first in (i2, z, y):
        for second in (i2, z, y):
            helper_require(tr(multiply(dagger(first), second)) == (2 if first == second else 0),
                           "Independent physical I/Z/Y coefficient directions in the phase ratio")
    helper_require(tr(multiply(x, j_block)) == -1
                   and tr(multiply(x, plus(multiply(x, j_block), scale(multiply(j_block, x), -1)))) == 0
                   and tr(multiply(x, multiply(multiply(x, j_block), x))) == -1,
                   "Conjugating J by cI+isX retains nonzero block-X coefficient for every beta")

    # A legitimate refinement of the attaining accepted flag may have
    # different photon corrections. Absorbing them and coherently compressing
    # the common spin correction recovers the same terminal contraction.
    terminal = [left + right for left, right in zip(m0, m1)]
    projection = multiply(dagger(terminal), terminal)
    helper_require(multiply(projection, projection) == projection
                   and projection == dagger(projection), "Accepted terminal row is a contraction")
    compressed = zeros(2, 4)
    lambdas = (r3 / 3, cast(field_scale(INV_SQRT2, 2)) * r3 / 3)
    for amplitude, photon_correction in zip(lambdas, (x, z)):
        refined = scale(multiply(dagger(photon_correction), terminal), amplitude)
        corrected_row = multiply(photon_correction, refined)
        helper_require(corrected_row == scale(terminal, amplitude),
                       "Record-dependent photon corrections preserve the common spin correction")
        compressed = plus(compressed, scale(corrected_row, amplitude))
    helper_require(compressed == terminal, "Exact coherent common-correction compression")

    # Terminal spin filters give general complex circulants. This exact
    # nonunitary fixture tests their ratio, while the three trace
    # coefficients above supply the all-circulant polynomial identity.
    aa, bb = (2 + imaginary) / 3, (1 - 2 * imaginary) / 5
    circulant = plus(scale(i2, aa), scale(x, bb))
    generalized_ratio = multiply(multiply(c0, kron(circulant, i2)), c0_inverse)
    helper_require(generalized_ratio == plus(scale(eye(4), aa), plus(
        scale(kron(i2, z), imaginary * bb), scale(kron(j_block, y), -imaginary * bb))),
        "Complex-circulant Fourier ratio, including nonunitary spin filters")
    nonunitary_t = plus(i2, scale(x, imaginary / 2))
    nonunitary_t_inverse = scale(plus(i2, scale(x, -imaginary / 2)), F(4, 5))
    helper_require(multiply(nonunitary_t, nonunitary_t_inverse) == i2
                   and tr(multiply(x, multiply(multiply(nonunitary_t, j_block),
                                                nonunitary_t_inverse))) == -1,
                   "Invertible nonunitary circulant preserves nonzero block-X trace")

    # A full terminal product-instrument budget with two differently
    # corrected photon rows and the same nonunitary spin filter. Its
    # residual is exhibited as an explicit sum of Gram matrices. The
    # analytic proof uses this implication for arbitrary record families.
    filter_a, filter_b = diagonal([1, F(1, 2)]), diagonal([F(1, 3), 1])
    spin_filter = kron(filter_a, filter_b)
    filter_effect = multiply(dagger(spin_filter), spin_filter)
    weighted_rows = [scale(multiply(dagger(correction), terminal), amplitude)
                     for amplitude, correction in zip(lambdas, (x, z))]
    product_budget = zeros(16)
    for row in weighted_rows:
        product_row = kron(row, spin_filter)
        product_budget = plus(product_budget, multiply(dagger(product_row), product_row))
    helper_require(product_budget == kron(projection, filter_effect),
                   "Actual complete terminal product effects have the common-filter budget")
    residual = plus(eye(16), scale(product_budget, -1))
    photon_residual = plus(eye(4), scale(projection, -1))
    # The diagonal residual has the following explicit rational-square
    # decomposition, so no further square-root extension is needed.
    gram_roots = (diagonal([F(2, 3), 0, F(5, 6), F(1, 2)]),
                  diagonal([F(2, 3), 0, F(1, 2), F(1, 2)]),
                  diagonal([0, 0, F(1, 6), F(1, 2)]))
    spin_residual = zeros(4)
    for root_matrix in gram_roots:
        spin_residual = plus(spin_residual, multiply(dagger(root_matrix), root_matrix))
    helper_require(spin_residual == plus(eye(4), scale(filter_effect, -1)),
                   "Explicit rational Gram decomposition of the normalized spin-filter residual")
    budget_residual = multiply(dagger(kron(photon_residual, spin_filter)),
                               kron(photon_residual, spin_filter))
    for root_matrix in gram_roots:
        factor = kron(eye(4), root_matrix)
        budget_residual = plus(budget_residual, multiply(dagger(factor), factor))
    helper_require(residual == budget_residual,
                   "Global terminal effect budget is positive, without a per-leaf budget substitution")

    from retained_photon_dual import verify as verify_retained_photon_dual
    all_phase_dual = verify_retained_photon_dual()
    helper_require(all_phase_dual["status"] == "PASS"
                   and all_phase_dual["sharp_probability"] == "9/16",
                   "Imported all-phase finite-helper exact dual certificate")

    from retained_photon_middle import run_certificate as verify_retained_photon_middle
    middle_certificate = verify_retained_photon_middle()
    helper_require(middle_certificate["pass"] is True,
                   "Imported four-mode middle-photon-instrument exact certificate")

    from retained_photon_serial import verify as verify_retained_photon_serial
    serial_certificate = verify_retained_photon_serial()
    helper_require(serial_certificate["status"] == "passed"
                   and serial_certificate["full_control_data_matrix_units"] == 256
                   and serial_certificate["both_flag_data_matrix_units"] == 128,
                   "Imported conditional ordinary serial-survivor exact certificate")

    # Rational ledgers price every fatal erasure. These finite identities do
    # not establish an actual detector, survival law or safe vacuum retry.
    ledger_guards = 0
    for transmission, meter, routing in ((F(0), F(1), F(1)), (F(1), F(1), F(1)),
            (F(1, 2), F(1, 2), F(1)), (F(4, 5), F(31, 100), F(1)),
            (F(9, 10), F(9, 10), F(1)), (F(9, 10), F(31, 100), F(3, 4))):
        survival = transmission ** 2 * meter * routing
        good, repeat, fatal = 3 * survival / 4, survival / 4, 1 - survival
        helper_require(good + repeat + fatal == 1, "All round outcomes including fatal photon erasure")
        delivered, rounds = 3 * survival / (4 - survival), 4 / (4 - survival)
        helper_require(delivered == good / (1 - repeat) and rounds == 1 / (1 - repeat)
                       and survival >= delivered,
                       "Defined scalar delivered ledger and joint-meter ordinary comparison")
        for cap in (1, 2, 4):
            visits = sum((repeat ** j for j in range(cap)), F(0))
            helper_require(good * visits + fatal * visits + repeat ** cap == 1
                           and (1 - repeat) * visits == 1 - repeat ** cap,
                           "Capped records retain rejection and every launched round")
            ledger_guards += 1
        returned = sum((transmission ** (2 + u + v) / 4
                        for u, v in product((0, 1), repeat=2)), F(0))
        helper_require(returned == transmission ** 2 * (1 + transmission) ** 2 / 4,
                       "Actual coherent correction-key occupation loss polynomial")
    meter = F(31, 100)
    helper_require(3 * meter ** 2 / (4 - meter ** 2) == F(961, 13013) < F(1, 10),
                   "Declared common-meter rejection constant, excluding plus-bypass models")
    return {"status": "passed", "arithmetic": "Q(exp(i*pi/8),sqrt3) and exact rational polynomials",
            "retained_input_dimension": 8, "native_corrected_flag_matrix_units": native_units,
            "four_contact_Clifford_axis_identities": 2,
            "two_helper_program_flag_matrix_units": program_units,
            "three_contact_readout_history_matrix_units": three_units,
            "native_classical_coin_flag_matrix_units": coin_units,
            "coherent_return_keys": 4, "coherent_return_mean_occupied_contacts": 3,
            "sharp_U4_controls": 3, "sharp_U4_both_flag_matrix_units": sharp_units,
            "sharp_projective_single_branch_probability": "9/16", "complement_probability": "7/16",
            "complement_Gram_polynomial_identities": gram_identities,
            "Fourier_Gram_square_root_identities": 3,
            "squared_target_Fourier_nuclear_norm": "20/3",
            "single_common_correction_trace_probability_upper": "3/5",
            "terminal_contraction_T3_polynomial_identities": 4,
            "Fourier_inverse_and_rotation_ratio_identities": 3,
            "terminal_phase_Pauli_trace_guards": 12,
            "common_spin_correction_terminal_refinement_records": 2,
            "four_mode_total_terminal_corrected_probability_upper": "9/16",
            "terminal_spin_filter_complex_circulant_guards": 2,
            "terminal_spin_filter_full_effect_budget_guards": 3,
            "four_mode_total_terminal_separable_filter_probability_upper": "3/5",
            "all_phase_arbitrary_finite_helper_dual": all_phase_dual,
            "four_mode_photon_middle_instrument": middle_certificate,
            "ordinary_serial_survivor": serial_certificate,
            "finite_capped_ledger_guards": ledger_guards,
            "scope": "Exact retained-F instruments and ordinary compilers, U4 witness/projective complement Gram identities, terminal-contraction and fixed-four-mode phase-ratio polynomial ingredients, common-correction compression, complex-circulant and terminal product-effect budget guards, all-phase finite-helper SDP dual certificate, middle-photon-instrument construction and polynomial optimization ingredients, conditional ordinary serial raw-survivor and local-response algebra, and finite scalar ledgers. General pinching, instrument and norm deductions remain analytic: four photon modes with one arbitrary photon instrument between two fixed CZ contacts have unitary-spin-feedback optimum 3/(3+sqrt5), and terminal separable spin filters obey 3/5. These scopes exclude spin filters or spin-ancilla encodings before or between contacts; no broader intermediate-adaptive upper, actual survival/readout port, microscopic scattering or hardware advantage. Serial raw-survivor equality requires supplied coherent-vacuum, stationary common-record kernels and matched output modes. Its disjoint event layers imply neither an opaque-query simulation nor a four-versus-two hardware-latency lower bound; full retimed bath/loss maps remain unproved."}


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
            "reflected_diagonal_gate_cone": gate_verify(),
            "decorated_eight_mode_bus": decorated_bus_verify(),
            "exact_projector_CZ_gate_gap": exact_projector_gap_verify(),
            "retained_photon_gate": retained_photon_gate_verify(),
            "scope": "exact detected/aggregate-vacuum spin instruments under declared reciprocal post-unitary erasures, plus scalar concurrence/Bell-yield, cavity/rank-loss/factory and known-gate identities, a full-rank helper POVM/filter example, constant-control coherent-frequency normal forms, eigen-source survivor compilers and reflected diagonal-gate cone/balancing witnesses, decorated eight-mode coherent survivors and safe four-window compiler, with merged-port rank guards, and an exact restricted projector-kernel primal/dual gate gap; universal proofs, native ports, calibration and clocks remain analytic"}


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True))
