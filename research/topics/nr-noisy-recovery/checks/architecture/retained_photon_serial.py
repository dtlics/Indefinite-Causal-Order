"""Exact conditional ordinary serial-survivor and local-response guards.

Gaussian-rational arithmetic replays the complete controlled survivor,
both output flags, physical phase wrappers, raw reflected kernels and
coherent frequency inputs. Polynomial identities concern a declared
stationary closed-transition model only. Supplied controlled-vacuum ports,
timed routing, full rejected/bath maps and hardware rates remain analytic
or physical assumptions. Import is quiet, no files are written, and every
guard remains active under -O.

Additional physical-screen ingredients are formal energy-decay reflection,
common reliable-meter scalar polynomials and exact CZ relative sectors.
They supply no complete detector instrument or hardware certificate.
"""
from fractions import Fraction as F
from itertools import product
import json


class G:
    def __init__(self, r=0, i=0):
        if isinstance(r, G):
            self.r, self.i = r.r, r.i
        else:
            self.r, self.i = F(r), F(i)

    def __add__(self, other):
        other = G(other)
        return G(self.r+other.r, self.i+other.i)

    __radd__ = __add__

    def __neg__(self):
        return G(-self.r, -self.i)

    def __sub__(self, other):
        return self + -G(other)

    def __rsub__(self, other):
        return G(other) + -self

    def __mul__(self, other):
        other = G(other)
        return G(self.r*other.r-self.i*other.i,
                 self.r*other.i+self.i*other.r)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = G(other)
        norm = other.r**2+other.i**2
        return self*G(other.r/norm, -other.i/norm)

    def __eq__(self, other):
        other = G(other)
        return self.r == other.r and self.i == other.i

    def conj(self):
        return G(self.r, -self.i)


def require(test, message):
    if not test:
        raise ValueError(message)


def eye(n):
    return [[G(int(i == j)) for j in range(n)] for i in range(n)]


def zeros(n, m=None):
    return [[G() for _ in range(n if m is None else m)] for _ in range(n)]


def mm(a, b):
    require(len(a[0]) == len(b), "matrix product dimensions")
    out = zeros(len(a), len(b[0]))
    for i, row in enumerate(a):
        for k, x in enumerate(row):
            if x != 0:
                for j, y in enumerate(b[k]):
                    if y != 0:
                        out[i][j] += x*y
    return out


def adj(a):
    return [[a[j][i].conj() for j in range(len(a))]
            for i in range(len(a[0]))]


def add(a, b):
    require(len(a) == len(b) and len(a[0]) == len(b[0]), "matrix sum dimensions")
    return [[x+y for x, y in zip(r, s)] for r, s in zip(a, b)]


def scale(a, z):
    return [[x*z for x in row] for row in a]


def blockdiag(a, b):
    da, db = len(a), len(b)
    out = zeros(da+db)
    for i in range(da):
        for j in range(da):
            out[i][j] = a[i][j]
    for i in range(db):
        for j in range(db):
            out[da+i][da+j] = b[i][j]
    return out


def blockrows(a, b):
    return [list(ar)+list(br) for ar, br in zip(a, b)]


def kron(a, b):
    return [[x*y for x in ar for y in br] for ar in a for br in b]


def rank(a):
    work = [list(row) for row in a]
    pivot_row = 0
    for col in range(len(work[0])):
        pivot = next((r for r in range(pivot_row, len(work))
                      if work[r][col] != 0), None)
        if pivot is None:
            continue
        work[pivot_row], work[pivot] = work[pivot], work[pivot_row]
        value = work[pivot_row][col]
        work[pivot_row] = [x/value for x in work[pivot_row]]
        for row in range(len(work)):
            if row != pivot_row:
                factor = work[row][col]
                work[row] = [x-factor*y for x, y in zip(work[row], work[pivot_row])]
        pivot_row += 1
        if pivot_row == len(work):
            break
    return pivot_row


def cp_difference(a, b):
    """Return a full matrix-unit coefficient witness, or None.

    Zero rows outside the union of the two column supports have identically
    zero coefficients on both sides. Sparse traversal therefore checks every
    input matrix unit and every potentially nonzero output coefficient.
    """
    require(len(a) == len(b) and len(a[0]) == len(b[0]), "CP dimensions")
    supports = [[r for r in range(len(a)) if a[r][i] != 0 or b[r][i] != 0]
                for i in range(len(a[0]))]
    for i, j in product(range(len(a[0])), repeat=2):
        for r, s in product(supports[i], supports[j]):
            if a[r][i]*a[s][j].conj() != b[r][i]*b[s][j].conj():
                return [i, j, r, s]
    return None


def cp_equal(a, b):
    require(cp_difference(a, b) is None, "full matrix-unit CP coefficient")
    return len(a[0])**2


def flags(controlled):
    """Literal C=+ source and C=X readout, retaining the full payload."""
    n = len(controlled)//2
    return [[[sum((controlled[i+c*n][j+d*n] * (sign**c)
                   for c, d in product(range(2), repeat=2)), G())/2
              for j in range(n)] for i in range(n)] for sign in (1, -1)]


def single_f(matrix):
    out = zeros(8)
    for a, b, f, g in product(range(2), repeat=4):
        out[(a*2+b)*2+f][(a*2+b)*2+g] = matrix[f][g]
    return out


def spin_phase(which):
    out = eye(8)
    for a, b, f in product(range(2), repeat=3):
        index = (a*2+b)*2+f
        out[index][index] = G(0, 1) if (a, b)[which] else G(1)
    return out


def cz(which, x_axis=False):
    out = zeros(8)
    for a, b, f in product(range(2), repeat=3):
        bit = (a, b)[which]
        target = f ^ bit if x_axis else f
        phase = (-1)**(bit*f) if not x_axis else 1
        out[(a*2+b)*2+target][(a*2+b)*2+f] = G(phase)
    return out


def ising_pauli(which, x_axis=False):
    out = zeros(8)
    for a, b, f in product(range(2), repeat=3):
        bit = (a, b)[which]
        target = f ^ 1 if x_axis else f
        value = (-1)**bit if x_axis else (-1)**(bit+f)
        out[(a*2+b)*2+target][(a*2+b)*2+f] = G(value)
    return out


def reflected(which, dark, bright, x_axis=False):
    """Complex spin-dependent selected elastic block, no loss completion."""
    out = zeros(8)
    for a, b, f, g in product(range(2), repeat=4):
        bit = (a, b)[which]
        values = [dark, bright if bit else dark]
        value = values[f] if f == g else G()
        if x_axis:
            value = (values[0]+values[1])/2 if f == g else (values[0]-values[1])/2
        out[(a*2+b)*2+f][(a*2+b)*2+g] = value
    return out


def raw_polarization(which, dark, bright, bypass, x_axis=False):
    """Keep both m/d polarization outputs: payload is A,B,F,p (dimension16)."""
    out = zeros(16)
    for a, b, f, g, pol in product(range(2), repeat=5):
        bit = (a, b)[which]
        reflected_value = bright if bit == pol else dark
        values = [bypass, reflected_value]
        value = values[f] if f == g else G()
        if x_axis:
            value = (values[0]+values[1])/2 if f == g else (values[0]-values[1])/2
        out[((a*2+b)*2+f)*2+pol][((a*2+b)*2+g)*2+pol] = value
    return out


def require_raw_polarization_kernel(op, which, dark, bright, bypass, x_axis=False):
    """Independently expose the constructed m and d ports in the +/- basis."""
    x = [[G(), G(1)], [G(1), G()]]
    z = [[G(1), G()], [G(), G(-1)]]
    hadamard_numerator = [[G(1), G(1)], [G(1), G(-1)]]
    hp = kron(eye(8), hadamard_numerator)
    transformed = scale(mm(hp, mm(op, hp)), F(1, 2))
    axis = kron(eye(4), kron(x if x_axis else z, eye(2)))
    hot = scale(add(eye(16), scale(axis, -1)), F(1, 2))
    spin_z = kron(z, eye(8)) if which == 0 else kron(eye(2), kron(z, eye(4)))
    polarization_x = kron(eye(8), x)
    mean, difference = (dark+bright)/2, (bright-dark)/2
    expected = add(add(scale(eye(16), bypass), scale(hot, mean-bypass)),
                   scale(mm(spin_z, mm(hot, polarization_x)), difference))
    require(transformed == expected,
            "literal full raw polarization m/d operator, including the unselected port")
    require(mean != 0, "constructed raw fixture has a nonzero unselected m port")


def compiler(a, b):
    n = len(a)
    ident = eye(n)
    native = blockdiag(mm(b, a), mm(a, b))
    a0, a1 = blockdiag(a, ident), blockdiag(ident, a)
    b0, b1 = blockdiag(b, ident), blockdiag(ident, b)
    three = mm(a1, mm(blockdiag(b, b), a0))
    four = mm(a1, mm(b1, mm(b0, a0)))
    require(native == three == four, "serial survivor operator")
    for first, second in ((a0, b1), (b0, a1), (b0, b1)):
        require(mm(first, second) == mm(second, first), "disjoint path events commute")
    layers = mm(mm(a1, b0), mm(b1, a0))
    require(layers == four, "two disjoint event layers equal four serial factors")
    return native, three, four


# Formal polynomials in (kappa_e,kappa_i,gamma,g_squared,delta). All
# coefficients are Gaussian rationals; squares of output amplitudes avoid
# expanding any positive square roots of physical decay rates.
def pc(value):
    value = G(value)
    return {} if value == 0 else {(0,)*5: value}


def pv(index):
    powers = [0]*5
    powers[index] = 1
    return {tuple(powers): G(1)}


def pa(a, b):
    out = dict(a)
    for power, value in b.items():
        out[power] = out.get(power, G())+value
    return {power: value for power, value in out.items() if value != 0}


def ps(a, b):
    return pa(a, {power: -value for power, value in b.items()})


def pm(a, b):
    out = {}
    for ap, av in a.items():
        for bp, bv in b.items():
            power = tuple(x+y for x, y in zip(ap, bp))
            out[power] = out.get(power, G())+av*bv
    return {power: value for power, value in out.items() if value != 0}


def pconj(a):
    return {power: value.conj() for power, value in a.items()}


def pn(a):
    return pm(a, pconj(a))


def finite_pulse_algebra():
    ke, ki, gamma, g2, delta = [pv(i) for i in range(5)]
    kappa = pa(ke, ki)
    dc, da = ps(kappa, pm(pc(G(0, 1)), delta)), ps(gamma, pm(pc(G(0, 1)), delta))
    denominator = pa(pm(dc, da), g2)
    d0 = pa(pm(kappa, gamma), g2)
    reflected_numerator = ps(denominator, pm(pc(2), pm(ke, da)))
    loss_numerator = pm(pc(4), pm(pm(ke, ki), pn(da)))
    emission_numerator = pm(pc(4), pm(pm(g2, ke), gamma))
    require(pa(pa(pn(reflected_numerator), loss_numerator), emission_numerator) == pn(denominator),
            "declared closed-transition r/l/e norm polynomial")
    residual = ps(pm(da, d0), pm(gamma, denominator))
    residual_expected = pm(delta, pa(pm(gamma, delta), pm(pc(G(0, 1)), ps(pm(gamma, gamma), g2))))
    require(residual == residual_expected, "bright detuning residual numerator")
    require(pn(residual) == pm(pm(delta, delta), pa(pm(pm(gamma, gamma), pm(delta, delta)), pn(ps(pm(gamma, gamma), g2)))),
            "bright detuning residual norm polynomial")
    require(ps(kappa, dc) == pm(pc(G(0, 1)), delta), "dark detuning residual numerator")
    require(pn(dc) == pa(pm(kappa, kappa), pm(delta, delta)), "dark detuning denominator norm")
    require(ps(denominator, pm(dc, da)) == g2, "raw symmetric selected-difference numerator")
    # Critical coupling is checked after its exact symbolic substitution.
    intrinsic, rate, s = pv(0), pv(1), pv(2)
    external = pm(intrinsic, s)
    total = pm(intrinsic, pa(pc(1), s))
    coupling_squared = pm(pm(intrinsic, rate), ps(pm(s, s), pc(1)))
    carrier_denominator = pa(pm(total, rate), coupling_squared)
    require(pm(ps(carrier_denominator, pm(pc(2), pm(external, rate))), pa(s, pc(1))) ==
            pm(ps(s, pc(1)), carrier_denominator), "critical-coupling bright carrier amplitude")
    require(pm(ps(total, pm(pc(2), external)), pa(s, pc(1))) ==
            pm(ps(pc(1), s), total), "critical-coupling dark carrier amplitude")
    return {"polynomial_identities": 8,
            "scope": "declared stationary closed-transition r/l/e normalization and detuning/critical-coupling algebra only; no parameter fit, broadband equality, pulse/router bound or complete Raman/bath model"}


def physical_screen_algebra():
    # All variables here are formal. Positivity on the stated parameter
    # rectangle and the clean-ancilla one-contact deduction remain analytic.
    t, meter = pv(0), pv(1)
    one_plus_t = pa(pc(1), t)
    t2, one_plus_t2 = pm(t, t), pm(one_plus_t, one_plus_t)
    denominator = ps(pc(4), pm(meter, t2))
    bracket = pa(pm(t2, one_plus_t2), pc(12))
    numerator = ps(pm(pc(4), one_plus_t2), pm(meter, bracket))
    require(ps(pm(one_plus_t2, denominator), pm(pc(12), meter)) == numerator,
            "common-meter delivered-weight difference numerator")
    manifest = pa(pm(pm(pc(F(1, 3)), t),
                     pa(pa(pc(24), pm(pc(8), t)),
                        pm(pm(t, ps(pc(1), t)), pa(t, pc(3))))),
                  pm(ps(pc(F(1, 3)), meter), bracket))
    require(numerator == manifest, "common-meter nonnegative polynomial decomposition")
    margin = pa(pc(F(11, 3)),
                pa(pm(ps(pc(F(1, 3)), meter), t2),
                   pm(pc(F(1, 3)), ps(pc(1), t2))))
    require(denominator == margin, "common-meter denominator lower-margin identity")

    # These kappa values are ENERGY decay rates. This response convention
    # differs from the amplitude-rate closed-transition model above.
    ke, ki, delta, chi = [pv(i) for i in range(4)]
    half_width = pm(pc(F(1, 2)), pa(ke, ki))
    imaginary = pc(G(0, 1))
    shifted = [ps(delta, chi), pa(delta, chi)]
    cavity = [ps(half_width, pm(imaginary, x)) for x in shifted]
    reflected = [ps(d, ke) for d in cavity]
    intensities = [pn(d) for d in cavity]
    loss_product = pm(ke, ki)
    for r, d in zip(reflected, intensities):
        require(pn(r) == ps(d, loss_product),
                "energy-decay dispersive reflected intensity numerator")
    imbalance = ps(pm(pn(reflected[0]), intensities[1]),
                   pm(pn(reflected[1]), intensities[0]))
    require(imbalance == pm(pc(-4), pm(pm(loss_product, delta), chi)),
            "energy-decay spin-reflectance imbalance numerator")
    carrier_plus = pa(half_width, pm(imaginary, chi))
    carrier_minus = ps(half_width, pm(imaginary, chi))
    carrier_sum = pa(pm(ps(carrier_plus, ke), carrier_minus),
                     pm(ps(carrier_minus, ke), carrier_plus))
    opposition = pm(pc(F(1, 2)),
                    pa(ps(pm(ki, ki), pm(ke, ke)), pm(pc(4), pm(chi, chi))))
    require(carrier_sum == opposition, "energy-decay opposite-carrier condition numerator")

    x = [[G(), G(1)], [G(1), G()]]
    z = [[G(1), G()], [G(), G(-1)]]
    identity = eye(2)
    for spin in (1, -1):
        plus = add(add(identity, scale(z, G(0, -spin))), scale(x, G(0, -1)))
        minus = add(add(identity, scale(z, G(0, -spin))), scale(x, G(0, 1)))
        require(mm(adj(plus), plus) == scale(identity, 3)
                and mm(adj(minus), minus) == scale(identity, 3),
                "target-sector numerator normalization")
        relative = scale(mm(adj(plus), minus), F(1, 3))
        expected = scale(add(add(identity, scale(x, G(0, 2))),
                             scale(mm(z, x), -2*spin)), F(1, 3))
        require(relative == expected and mm(adj(relative), relative) == identity,
                "single-CZ clean-return relative unitary")
        trace = relative[0][0]+relative[1][1]
        determinant = relative[0][0]*relative[1][1]-relative[0][1]*relative[1][0]
        require(trace == F(2, 3) and determinant == 1 and relative != adj(relative),
                "relative trace/determinant obstruct a phased Hermitian involution")
    return {"common_meter_polynomial_identities": 3,
            "microwave_energy_decay_polynomial_identities": 4,
            "clean_CZ_relative_spin_sectors": 2,
            "clean_CZ_relative_sector_trace": "2/3",
            "clean_CZ_relative_sector_determinant": 1,
            "scope": "formal common-reliable-meter scalar closure ingredients for 0<=t<=1 and 0<=m<=1/3, declared stationary energy-decay dispersive reflection, and clean-CZ relative-sector identities only. Sign-domain positivity, arbitrary-clean-photonic-ancilla invariance and the unitary-only four-contact theorem remain analytic. No rail-preserving detector, complete repeated-use instrument, device fit, fractional-angle port or hardware-rate claim."}


def deferred_exit_frame_guards():
    imaginary = G(0, 1)
    sf = single_f([[G(1), G()], [G(), imaginary]])
    sx = single_f([[G(F(1, 2), F(1, 2)), G(F(1, 2), F(-1, 2))],
                   [G(F(1, 2), F(-1, 2)), G(F(1, 2), F(1, 2))]])
    yf = single_f([[G(), -imaginary], [imaginary, G()]])
    sa, sb = spin_phase(0), spin_phase(1)
    t = mm(sa, sb)
    s = mm(t, t)
    p, q = ising_pauli(0), ising_pauli(1, True)
    numerator = add(add(eye(8), scale(p, -imaginary)), scale(q, -imaginary))
    require(mm(s, numerator) == mm(numerator, s) and mm(s, s) == eye(8),
            "commuting spin-only retry Pauli")
    require(mm(p, q) == scale(mm(yf, s), imaginary), "literal minus photon/spin factors")

    def power(op, exponent):
        if exponent < 0:
            return power(adj(op), -exponent)
        result = eye(len(op))
        for _ in range(exponent):
            result = mm(op, result)
        return result

    ra, rb = mm(sf, cz(0)), mm(sx, cz(1, True))
    ideal = flags(compiler(mm(sa, ra), mm(sb, rb))[0])
    raw = flags(compiler(ra, rb)[0])
    ideal_exit = scale(ideal[0], -imaginary)
    ideal_repeat = mm(scale(yf, -1), ideal[1])
    raw_exit = scale(raw[0], -imaginary)
    raw_repeat = mm(scale(yf, -1), raw[1])
    require(ideal_exit == scale(numerator, F(1, 2))
            and ideal_repeat == scale(s, F(1, 2)), "ideal photon-only retry correction")
    require(raw_exit == scale(mm(adj(t), numerator), F(1, 2))
            and raw_repeat == scale(t, F(1, 2)), "raw plus-minus photon gauge and Clifford retry")
    literal_repeat = mm(scale(yf, -imaginary), raw[1])
    require(literal_repeat == scale(t, imaginary/2), "literal uncompensated raw retry phase")
    coherent_units, residual_cases, phase_witness = 0, 0, None
    for cap in (2, 3):
        for variant, exit_op, repeat_op in (("ideal", ideal_exit, ideal_repeat),
                                            ("raw", raw_exit, raw_repeat),
                                            ("literal", raw[0], literal_repeat)):
            actual, expected, continuation = [], [], eye(8)
            for j in range(1, cap+1):
                actual.extend(mm(exit_op, continuation))
                frame = power(s, j-1) if variant == "ideal" else power(t, j-2)
                block = scale(mm(frame, numerator), F(1, 2**j))
                if variant == "literal":
                    block = scale(block, power([[imaginary]], j)[0][0])
                expected.extend(block)
                continuation = mm(repeat_op, continuation)
            residual = scale(power(s if variant == "ideal" else t, cap), F(1, 2**cap))
            if variant == "literal":
                residual = scale(residual, power([[imaginary]], cap)[0][0])
            actual.extend(continuation)
            expected.extend(residual)
            require(actual == expected, "all coherent exit-time and residual amplitudes")
            require(mm(adj(actual), actual) == eye(8), "finite-cap coherent isometry")
            require(mm(adj(continuation), continuation) == scale(eye(8), F(1, 4**cap)),
                    "finite-cap full-input failure effect")
            coherent_units += cp_equal(actual, expected)
            residual_cases += 1
            if cap == 2 and variant == "raw":
                mutant = [row[:] for row in expected]
                mutant[8:16] = scale(mutant[8:16], -1)
                require(cp_equal(mutant[8:16], expected[8:16]) == 64,
                        "a single exit global phase leaves its separate CP map unchanged")
                phase_witness = cp_difference(actual, mutant)
                require(phase_witness is not None and phase_witness[2]//8 != phase_witness[3]//8,
                        "exit-time relative phase changes a coherent cross block")
    # The two parity classes have exact infinite geometric weights. The
    # finite coefficient identity below checks every ABF matrix unit.
    require(F(3, 4)/(1-F(1, 16)) == F(4, 5)
            and F(3, 16)/(1-F(1, 16)) == F(1, 5), "untracked ideal retry-frame weights")
    sn = mm(s, numerator)
    for i, j, row, col in product(range(8), repeat=4):
        first = numerator[row][i]*numerator[col][j].conj()
        second = sn[row][i]*sn[col][j].conj()
        require((first/4+second/16)/F(15, 16) == (4*first+second)/15,
                "untracked geometric channel on every ABF matrix unit")
    require([F(3, 4**j)/(1-F(1, 256)) for j in range(1, 5)] ==
            [F(64, 85), F(16, 85), F(4, 85), F(1, 85)], "untracked raw mod4 frame weights")
    relative = scale(mm(mm(numerator, mm(p, q)), adj(numerator)), F(1, 3))
    require(relative == scale(add(add(scale(mm(p, q), -1), scale(p, 2*imaginary)),
                                  scale(q, -2*imaginary)), F(1, 3)),
            "omitting photon correction is not a Pauli output frame")
    x = [[G(), G(1)], [G(1), G()]]
    y = [[G(), -imaginary], [imaginary, G()]]
    phase = [[G(1), G()], [G(), imaginary]]
    require(mm(mm(phase, x), adj(phase)) == y and power(t, 4) == eye(8),
            "raw frame changes terminal Pauli basis modulo four")
    for sign in (1, -1):
        rho = scale(add(eye(2), scale(x, sign)), F(1, 2))
        require(sum((x[r][c]*rho[c][r] for r, c in product(range(2), repeat=2)), G()) == sign,
                "opposite target X eigenstate outcomes")
        transformed = mm(mm(phase, rho), adj(phase))
        require(sum((x[r][c]*transformed[c][r] for r, c in product(range(2), repeat=2)), G()) == 0,
                "late fixed-X data cannot distinguish the two raw-framed X eigenstates")
    return {"finite_caps": [2, 3], "coherent_ABF_matrix_units": coherent_units,
            "residual_cases": residual_cases, "coherent_exit_phase_CP_witness": phase_witness,
            "untracked_ABF_matrix_units": 64, "ideal_untracked_frame_weights": ["4/5", "1/5"],
            "raw_untracked_mod4_frame_weights": ["64/85", "16/85", "4/85", "1/85"],
            "late_fixed_X_counterexample_states": 2,
            "scope": "finite ideal and literal raw-CZ ABFR exit-time isometries in the explicit plus-minus photon gauge; all coherent time cross blocks retained. General loop/vacuum/error dilation, endpoint record access, physical clock and ordinary same-port simulations remain analytic or supplied-interface assumptions. An unread quantum time key is not a reusable fixed-frame gate or an online classical herald."}


def unreset_meter_guards():
    identity, z = eye(2), [[G(1), G()], [G(), G(-1)]]

    def coefficient(kraus, i, j, row, col):
        return sum((k[row][i]*k[col][j].conj() for k in kraus), G())

    def compare_channels(actual, expected):
        for i, j, row, col in product(range(3), repeat=4):
            require(coefficient(actual, i, j, row, col) ==
                    coefficient(expected, i, j, row, col),
                    "full vacuum-early-late matrix-unit CP coefficient")
        return 9

    def diagonal(entries):
        return [[G(entries[i]) if i == j else G() for j in range(len(entries))]
                for i in range(len(entries))]

    units = 0
    fixtures = [(F(1), F(0)), (F(4, 5), F(3, 5)), (F(3, 5), F(4, 5)), (F(0), F(1))]
    for a, r in fixtures:
        require(a*a+r*r == 1, "Pythagorean amplitude-damping fixture")
        damping = [[G(1), G(), G(), G()], [G(), G(a), G(r), G()],
                   [G(), G(-r), G(a), G()], [G(), G(), G(), G(1)]]
        require(mm(adj(damping), damping) == eye(4), "unitary meter-bath amplitude-damping dilation")
        early = diagonal([-1 if rail == 1 and meter == 1 else 1
                          for rail, meter, bath in product(range(3), range(2), range(2))])
        late = diagonal([-1 if rail == 2 and meter == 1 else 1
                         for rail, meter, bath in product(range(3), range(2), range(2))])
        full = mm(late, mm(kron(eye(3), damping), early))
        require(mm(adj(full), full) == eye(12), "full ordered qutrit-meter-bath dilation")
        effects = zeros(3)
        for h in (1, -1):
            actual = [[[sum((full[row*4+2*mout+bath][col*4+2*minput] * h**mout
                              for mout, minput in product(range(2), repeat=2)), G())/2
                        for col in range(3)] for row in range(3)] for bath in range(2)]
            expected = [diagonal([F(1+h*a, 2), F(1-h*a, 2), F(1-h*a, 2)]),
                        diagonal([r/2, -r/2, r/2])]
            require(actual == expected, "full three-sector Ramsey Kraus amplitudes")
            units += compare_channels(actual, expected)
            for k in actual:
                effects = add(effects, mm(adj(k), k))
            pocc, pvac = (1-h*a)/2, (1+h*a)/2
            require(coefficient(actual, 1, 1, 1, 1) == pocc
                    and coefficient(actual, 2, 2, 2, 2) == pocc
                    and coefficient(actual, 0, 0, 0, 0) == pvac,
                    "occupied flags and vacuum dark indication")
            require(coefficient(actual, 1, 2, 1, 2) == -h*a*pocc,
                    "matched occupied populations do not ensure payload coherence")
            require(coefficient(actual, 0, 1, 0, 1) == 0
                    and coefficient(actual, 0, 2, 0, 2) == r*r/2,
                    "asymmetric vacuum-bin cross histories retained")
        require(effects == eye(3), "complete two-flag qutrit instrument")

    # Diagonal dephasing Kraus operators commute with the ideal kicks:
    # the missed indication changes a flag without dephasing the payload.
    c, d = F(3, 5), F(4, 5)
    pure_units = 0
    for h in (1, -1):
        actual = []
        for gap in (scale(identity, c), scale(z, d)):
            require(mm(gap, z) == mm(z, gap), "record-level diagonal dephasing commutes with kicks")
            joint = blockdiag(blockdiag(gap, mm(gap, z)), mm(z, gap))
            actual.append([[sum((joint[row*2+mout][col*2+minput] * h**mout
                                  for mout, minput in product(range(2), repeat=2)), G())/2
                            for col in range(3)] for row in range(3)])
        expected = ([diagonal([c, 0, 0]), diagonal([0, d, d])] if h == 1 else
                    [diagonal([0, c, c]), diagonal([d, 0, 0])])
        require(actual == expected, "pure-dephasing full qutrit flag amplitudes")
        pure_units += compare_channels(actual, expected)
        require(coefficient(actual, 1, 2, 1, 2) == (d*d if h == 1 else c*c),
                "pure-dephasing occupied output stays clean even on a missed flag")
    return {"amplitude_damping_fixtures": len(fixtures), "dilation_dimension": 12,
            "amplitude_damping_qutrit_matrix_units": units,
            "pure_dephasing_qutrit_matrix_units": pure_units,
            "scope": "exact ideal phase-kick and gap-only rational damping/dephasing fixtures, both flags and all vacuum/one-photon cross histories. General hidden-record/POVM theorems, finite-pulse driven scattering, actual loss/cavity/readout maps, device rates and protected flying-rail ports remain analytic or unprovided. No experimental error or hardware-performance estimate."}


def verify():
    imaginary = G(0, 1)
    sf = single_f([[G(1), G()], [G(), imaginary]])
    sx = single_f([[G(F(1, 2), F(1, 2)), G(F(1, 2), F(-1, 2))],
                   [G(F(1, 2), F(-1, 2)), G(F(1, 2), F(1, 2))]])
    sa, sb = spin_phase(0), spin_phase(1)
    ra, rb = mm(sf, cz(0)), mm(sx, cz(1, True))
    a, b = mm(sa, ra), mm(sb, rb)
    for op in (a, b, ra, rb):
        require(mm(adj(op), op) == eye(8), "unitary physical wrapper")
    p, q = ising_pauli(0), ising_pauli(1, True)
    require(a == scale(add(eye(8), scale(p, -imaginary)), G(F(1, 2), F(1, 2))),
            "literal Ising/CZ A phase wrapper")
    require(b == scale(add(eye(8), scale(q, -imaginary)), G(F(1, 2), F(1, 2))),
            "literal Ising/CZ B phase wrapper")
    raw, qualified_three, serial = compiler(a, b)
    raw_no_spin, _, serial_no_spin = compiler(ra, rb)
    finish = blockdiag(mm(sa, sb), mm(sa, sb))
    require(mm(finish, serial_no_spin) == raw, "one common-finish spin phase")
    wrong = mm(blockdiag(sa, sa), mm(finish, serial_no_spin))
    wrong_witness = cp_difference(wrong, raw)
    require(wrong_witness == [0, 4, 0, 4], "double-S_A cross-spin CP mismatch")
    full_units = cp_equal(raw, serial)
    require(cp_equal(raw, qualified_three) == full_units, "qualified three-window full CP replay")
    native_flags, serial_flags = flags(raw), flags(serial)
    ng = add(add(eye(8), scale(p, -imaginary)), scale(q, -imaginary))
    require(native_flags[0] == scale(ng, imaginary/2), "native plus literal physical phase")
    require(native_flags[1] == scale(mm(p, q), imaginary/2), "native minus literal physical phase")
    require(mm(adj(native_flags[0]), native_flags[0]) == scale(eye(8), F(3, 4)), "plus success effect")
    require(mm(adj(native_flags[1]), native_flags[1]) == scale(eye(8), F(1, 4)), "minus success effect")
    flag_units = sum(cp_equal(x, y) for x, y in zip(native_flags, serial_flags))

    cases = [(G(F(3, 5), F(1, 7)), G(F(-2, 3), F(1, 5)),
              G(F(5, 13), F(-1, 11)), G(F(4, 7), F(1, 3))),
             (G(), G(F(1, 2)), G(0, F(1, 3)), G(F(-2, 5)))]
    spectral, raw_units, raw_flag_units = [], 0, 0
    for da, ba, db, bb in cases:
        require(all(value.r**2+value.i**2 <= 1 for value in (da, ba, db, bb)),
                "raw scalar fixture amplitudes are contractions")
        ka, kb = reflected(0, da, ba), reflected(1, db, bb, True)
        require(mm(ka, kb) != mm(kb, ka), "raw fixture operators do not commute")
        native, _, ordinary = compiler(ka, kb)
        raw_units += cp_equal(native, ordinary)
        raw_flag_units += sum(cp_equal(x, y) for x, y in zip(flags(native), flags(ordinary)))
        spectral.append((native, ordinary))
    frequency_native, frequency_serial = [blockdiag(pair[0], pair[1])
                                         for pair in zip(*spectral)]
    require(frequency_native == frequency_serial, "coherent two-frequency operator")
    frequency_units = cp_equal(frequency_native, frequency_serial)
    mismatched_phase = blockdiag(spectral[0][1], scale(spectral[1][1], imaginary))
    require(cp_equal(spectral[1][0], scale(spectral[1][1], imaginary)) == 256,
            "per-frequency global phase preserves each separate CP map")
    frequency_phase_witness = cp_difference(frequency_native, mismatched_phase)
    require(frequency_phase_witness is not None and
            frequency_phase_witness[0]//16 != frequency_phase_witness[1]//16,
            "unmatched frequency phase changes a coherent cross-frequency matrix unit")
    frequency_flag_units = 0
    for flag in range(2):
        first = blockdiag(flags(spectral[0][0])[flag], flags(spectral[1][0])[flag])
        second = blockdiag(flags(spectral[0][1])[flag], flags(spectral[1][1])[flag])
        frequency_flag_units += cp_equal(first, second)

    # Preserve the complete auxiliary polarization, including the reflected
    # port a selected-CZ reduction would discard. No input-polarization or
    # frequency trace is performed in these full raw maps.
    auxiliary, auxiliary_units, auxiliary_flag_units = [], 0, 0
    for da, ba, db, bb in cases:
        ka = raw_polarization(0, da, ba, G(F(2, 3)))
        kb = raw_polarization(1, db, bb, G(F(3, 4), F(1, 9)), True)
        require_raw_polarization_kernel(ka, 0, da, ba, G(F(2, 3)))
        require_raw_polarization_kernel(kb, 1, db, bb, G(F(3, 4), F(1, 9)), True)
        require(mm(ka, kb) != mm(kb, ka), "raw auxiliary fixture operators do not commute")
        require(da+ba != 0 and db+bb != 0,
                "raw auxiliary fixtures retain nonzero unselected m ports")
        native, _, ordinary = compiler(ka, kb)
        auxiliary_units += cp_equal(native, ordinary)
        auxiliary_flag_units += sum(cp_equal(x, y) for x, y in zip(flags(native), flags(ordinary)))
        auxiliary.append((native, ordinary))
    auxiliary_frequency_native, auxiliary_frequency_serial = [blockdiag(pair[0], pair[1])
                                                             for pair in zip(*auxiliary)]
    auxiliary_frequency_units = cp_equal(auxiliary_frequency_native, auxiliary_frequency_serial)
    auxiliary_frequency_flag_units = 0
    for flag in range(2):
        first = blockdiag(flags(auxiliary[0][0])[flag], flags(auxiliary[1][0])[flag])
        second = blockdiag(flags(auxiliary[0][1])[flag], flags(auxiliary[1][1])[flag])
        auxiliary_frequency_flag_units += cp_equal(first, second)

    # The ideal Ising placement has span4 after clearing nonzero sqrt2
    # row/column scalings. Deferring S_A changes the literal photon graph
    # to span3, which is still too large for a single F2 arrival port.
    ap = [[G(1, -1), G()], [G(), G(1, 1)]]
    am = [[G(1, 1), G()], [G(), G(1, -1)]]
    difference = add(ap, scale(am, -1))
    require(difference[0][0]*difference[1][1] == 4 and rank(difference) == 2,
            "ideal-Ising graph difference invertible")
    ideal_graph = blockrows(ap, am)+blockrows(eye(2), eye(2))
    require(rank(ideal_graph) == 4, "ideal-Ising middle input span4")
    ra0 = [[G(1), G()], [G(), imaginary]]
    ra1 = [[G(1), G()], [G(), -imaginary]]
    deferred_graph = blockrows(ra0, ra1)+blockrows(eye(2), eye(2))
    require(rank(deferred_graph) == 3, "deferred-S_A middle input span3")
    sx2 = [[G(F(1, 2), F(1, 2)), G(F(1, 2), F(-1, 2))],
           [G(F(1, 2), F(-1, 2)), G(F(1, 2), F(1, 2))]]
    x2 = [[G(), G(1)], [G(1), G()]]
    b_contrast = mm(sx2, add(x2, scale(eye(2), -1)))
    require(rank(mm(blockdiag(b_contrast, b_contrast), deferred_graph)) == 2,
            "required B spin contrast rank2 on the actual deferred graph")
    # The two bright-F columns belong to the reachable span. After removing
    # the common SX wrapper, output rows with F=0 give an identity minor for
    # X-lambda I for every complex spin phase lambda: the I contribution is0.
    bright_inputs = [[G(), G()], [G(1), G()], [G(), G()], [G(), G(1)]]
    require(rank(blockrows(deferred_graph, bright_inputs)) == 3,
            "contrast-minor inputs lie in the deferred reachable span")
    contrast_x = mm(blockdiag(x2, x2), bright_inputs)
    contrast_i = mm(eye(4), bright_inputs)
    require([contrast_x[row] for row in (0, 2)] == eye(2) and
            [contrast_i[row] for row in (0, 2)] == zeros(2),
            "rank2 contrast minor for every local B spin phase")
    padded_bright = [[G(int(i == j == 1)) for j in range(4)] for i in range(4)]
    require(rank(padded_bright) == 1, "single-bright padded port contrast rank1")

    # These are counts of potential factors, not a latency lower bound:
    # the disjoint events can be regrouped into the two layers checked above.
    occupations = [[1, 1, 0, 0], [0, 0, 1, 1]]
    require(all(sum(row) == 2 and row[0]+row[3] == 1 and row[1]+row[2] == 1
                for row in occupations), "one occupied A and B per history")
    return {"status": "passed", "arithmetic": "Gaussian rational matrices and polynomials; standard library",
            "full_control_data_matrix_units": full_units,
            "both_flag_data_matrix_units": flag_units,
            "common_finish_phase_guards": 2,
            "literal_Ising_CZ_phase_wrappers": 2,
            "wrong_double_S_A_CP_witness": wrong_witness,
            "nonunitary_raw_kernel_cases": len(cases),
            "nonunitary_raw_full_matrix_units": raw_units,
            "nonunitary_raw_flag_matrix_units": raw_flag_units,
            "coherent_two_frequency_full_matrix_units": frequency_units,
            "coherent_two_frequency_flag_matrix_units": frequency_flag_units,
            "coherent_frequency_phase_mismatch_CP_witness": frequency_phase_witness,
            "raw_auxiliary_polarization_cases": len(cases),
            "literal_raw_polarization_matrix_guards": 2*len(cases),
            "raw_auxiliary_full_matrix_units": auxiliary_units,
            "raw_auxiliary_flag_matrix_units": auxiliary_flag_units,
            "raw_auxiliary_coherent_frequency_matrix_units": auxiliary_frequency_units,
            "raw_auxiliary_coherent_frequency_flag_matrix_units": auxiliary_frequency_flag_units,
            "disjoint_event_commutators_per_fixture": 3,
            "two_event_layers_equal_four_serial_factors": True,
            "safe_potential_windows": 4, "qualified_simultaneous_middle_windows": 3,
            "occupied_A_B_contacts_per_history": 2,
            "ideal_Ising_middle_input_span": 4,
            "deferred_S_A_middle_input_span": 3,
            "required_B_contrast_rank_on_deferred_span": 2,
            "B_contrast_arbitrary_local_spin_phase_minor": True,
            "padded_single_bright_contrast_rank": 1,
            "finite_pulse_local_algebra": finite_pulse_algebra(),
            "physical_screen_ingredients": physical_screen_algebra(),
            "deferred_exit_frames": deferred_exit_frame_guards(),
            "unreset_two_rail_meter": unreset_meter_guards(),
            "scope": "conditional coherent-vacuum survivor operator equality for safe same-local-port four-factor routing or a supplied spectator-C simultaneous middle port. Disjoint events also regroup into two layers: no four-versus-two hardware-latency lower bound or opaque-query-class equivalence. Raw auxiliary polarization and coherent frequency remain quantum. Additional formal scalar-meter, energy-decay reflection, clean-CZ relative-sector, finite deferred-exit-frame and gap-only two-rail-meter ingredients do not certify their general analytic or physical deductions. No actual routing/port, common timed-bath/rejected-loss instrument, parameter fit, readout or hardware-rate certificate."}


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True))
