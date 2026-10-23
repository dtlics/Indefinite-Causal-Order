"""Exact finite replay of NR-R11's detected remote-spin phase instruments.

Arithmetic is in Q[exp(i*pi/8)] with standard-library fractions. All spin
matrix-unit coefficients and explicit unequal-module loss histories are
checked. Gaussian rationals also guard the scalar-concurrence determinant
factorization; the rational Bell-yield witness and known-gate compilers are
replayed exactly. The native port, calibration, timing and general scattering/RUS
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
            "scope": "exact detected/aggregate-vacuum spin instruments under declared reciprocal post-unitary erasures, plus scalar concurrence/Bell-yield, cavity/rank-loss/factory and known-gate identities; native ports, calibration and clocks remain analytic"}


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True))
