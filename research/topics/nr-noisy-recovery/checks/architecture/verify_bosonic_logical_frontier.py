"""Exact finite guards for the fixed product-decoder bosonic comparator.

The all-function dominance proof, Gaussian integrals, Fourier completeness,
Sobolev regularity, heat positivity, QEC and SDP duality remain analytic
in methods/bosonic-logical-frontier.md, as do physical control costs.
No floating grid or numerical SDP solver is used.
"""
if not __debug__:
    raise RuntimeError("Run without -O: exact verification requires assertions")

from fractions import Fraction as F
from itertools import product
import json


def mm(a, b):
    return tuple(tuple(sum((x * y for x, y in zip(row, col)), F(0))
                       for col in zip(*b)) for row in a)


def ident(d):
    return tuple(tuple(F(i == j) for j in range(d)) for i in range(d))


def affine(a, shift=(0, 0)):
    return ((F(a[0][0]), F(a[0][1]), F(shift[0])),
            (F(a[1][0]), F(a[1][1]), F(shift[1])),
            (F(0), F(0), F(1)))


def circuit(*chronological):
    out = ident(3)
    for gate in chronological:
        out = mm(gate, out)
    return out


def symplectic(z, w):
    return z[1] * w[0] - z[0] * w[1]


def mv(a, z):
    return tuple(sum((x * y for x, y in zip(row, z)), F(0)) for row in a)


def sign(integer):
    return 1 - 2 * (integer & 1)


def dominance():
    count = 0
    for i, j, k in product(range(17), repeat=3):
        hq, hp, c = F(i, 16), F(j, 16), F(k, 16)
        tq, tp = 1 - hq, 1 - hp
        first = 2 * hq * hp / (1 + c)
        second = 1 - (tq + tp - 2 * tq * tp) / (1 + c)
        assert min(first, second) <= max(hq, hp)
        high, low = max(hq, hp), min(hq, hp)
        if low <= (1 + c) / 2:
            assert first <= high
        else:
            assert second <= high
        acceptance = (1 + c) / 2
        assert acceptance * max(hq, hp) >= acceptance * min(first, second)
        count += 1
    # The constructive score is hq only when the other coordinate retains zero.
    assert F(3, 4) * F(1, 2) != F(3, 4)
    return count


def alignment():
    count = phase_checks = 0
    eye = ident(2)
    j = ((F(0), F(1)), (F(-1), F(0)))
    ji = ((F(0), F(-1)), (F(1), F(0)))
    vectors = tuple(product((F(-2, 3), F(0), F(3, 5)), repeat=2))
    for g in (F(1, 2), F(2, 3), F(3, 4)):
        squeeze = affine(((1 / g, 0), (0, g)))
        undo = affine(((g, 0), (0, 1 / g)))
        for total in (F(1, 3), F(1), F(5, 2)):
            for axis in (0, 1):
                a, b = ((g * g * total, (1 - g * g) * total)
                        if axis == 0 else ((1 - g * g) * total, g * g * total))
                assert g * g * (a + b) == (a if axis == 0 else b)
                for x, y in product((F(-7, 3), F(0), F(4, 5)), repeat=2):
                    gates = (squeeze, affine(eye, (x, 0)), affine(ji),
                             affine(eye, (0, y)), affine(j), undo)
                    if axis == 1:
                        # Outer Fourier rotations preserve AB call order.
                        gates = (affine(j),) + gates + (affine(ji),)
                    expected = (g * (x + y), 0) if axis == 0 else (0, g * (x + y))
                    assert circuit(*gates) == affine(eye, expected)
                    assert symplectic((x, 0), mv(j, (0, y))) == 0
                    count += 1
        for matrix in (j, ji, ((g, 0), (0, 1 / g))):
            for z, w in product(vectors, repeat=2):
                assert symplectic(mv(matrix, z), mv(matrix, w)) == symplectic(z, w)
                phase_checks += 1
    return count, phase_checks


def wrap(z):
    r = (z + F(1, 2)).numerator // (z + F(1, 2)).denominator
    reduced = z - r
    assert F(-1, 2) <= reduced < F(1, 2)
    return reduced, r


def zak_guards():
    records = phases = matrix_units = ordered = 0
    syndromes = (F(-2, 5), F(-1, 5), F(0), F(1, 5), F(2, 5))
    shifts = (F(-7, 3), F(-1, 2), F(0), F(1, 2), F(9, 4))
    for u, v in product(syndromes, repeat=2):
        # X(u)Z(v)=exp(-i*pi*u*v/2) D(u,v), in units L=sqrt(pi).
        assert symplectic((u, 0), (0, v)) / 2 == -u * v / 2
        ordered += 1
        for x, y in product(shifts, repeat=2):
            up, r = wrap(u + x)
            vp, s = wrap(v + y)
            assert up - x + r == u and vp - y + s == v
            pauli = tuple(tuple(F(sign(s * row)) if row == (col + r) % 2 else F(0)
                                for col in range(2)) for row in range(2))
            for m in (-2, 0, 3):
                integrand = [[F(0), F(0)] for _ in range(2)]
                common = y * (up - x / 2) - r * v
                for logical in (0, 1):
                    lp = (logical + r) % 2
                    kp = 2 * m + lp
                    left = y * (up + kp - x / 2) + (kp - r) * v
                    right = common + kp * vp + lp * s
                    delta = left - right
                    assert delta.denominator == 1 and delta.numerator % 2 == 0
                    parity = left - kp * vp - common
                    assert parity.denominator == 1
                    integrand[lp][logical] = F(sign(parity.numerator))
                    phases += 1
                assert tuple(map(tuple, integrand)) == pauli
                pt = tuple(zip(*pauli))
                # All four matrix units imply the action for arbitrary complex
                # logical operators, including nonzero off-diagonal terms.
                for i, j in product(range(2), repeat=2):
                    e = tuple(tuple(F(row == i and col == j) for col in range(2))
                              for row in range(2))
                    actual = mm(mm(pauli, e), pt)
                    expected = tuple(tuple(F(sign(s * (row + col)))
                                           if (row, col) == ((i + r) % 2, (j + r) % 2)
                                           else F(0) for col in range(2)) for row in range(2))
                    assert actual == expected
                    matrix_units += 1
                records += 1
    return records, phases, matrix_units, ordered


def ladd(*terms):
    out = {}
    for scale, poly in terms:
        for power, coefficient in poly.items():
            out[power] = out.get(power, F(0)) + scale * coefficient
    return {power: coefficient for power, coefficient in out.items() if coefficient}


def energy():
    symbolic = forms = scaling = 0
    one = {0: F(1)}  # Laurent polynomials in t=pi^2, never floating pi.
    for dq, dp in product((F(1, 4), F(1, 2), F(3, 4)), repeat=2):
        q2 = {1: 1 / (4 * dp * dp), 0: dq * dq / 3, -1: -2 * dq * dq}
        p2 = {1: 1 / (4 * dq * dq)}
        number = ladd((F(1, 2), q2), (F(1, 2), p2), (F(-1, 2), one))
        expected = {1: (1 / (dq * dq) + 1 / (dp * dp)) / 8,
                    0: dq * dq / 6 - F(1, 2), -1: -dq * dq}
        assert number == expected
        # The even-cosine second moment follows from its endpoint terms:
        # integral u^2 cos(pi*u/dq) du = -4*dq^3/pi^2.
        assert ladd((F(1, 2) / dq, {-1: -4 * dq ** 3}),
                    (F(1), {0: dq * dq / 3})) == {0: dq * dq / 3, -1: -2 * dq * dq}
        symbolic += 1
    for g in (F(1, 2), F(2, 3), F(1), F(3, 2), F(2)):
        kappa = max(g * g, 1 / (g * g))
        assert kappa - 1 / (g * g) >= 0 and kappa - g * g >= 0
        for q2, p2 in product((F(1, 2), F(1), F(5, 2), F(4)), repeat=2):
            normal = (q2 + p2 - 1) / 2
            squeezed = (q2 / (g * g) + g * g * p2 - 1) / 2
            assert squeezed <= kappa * normal + (kappa - 1) / 2
            for mass in (F(0), F(1, 3), F(1), F(2)):
                unnormal = (mass * q2 + mass * p2 - mass) / 2
                unsqueezed = (mass * q2 / (g * g) + mass * g * g * p2 - mass) / 2
                assert unnormal == mass * normal and unsqueezed == mass * squeezed
                assert unsqueezed <= kappa * unnormal + (kappa - 1) * mass / 2
                scaling += 1
            forms += 1
    return symbolic, forms, scaling


def thinning():
    count = 0
    for i, j in product(range(17), repeat=2):
        acceptance, fidelity = F(i, 16), F(j, 16)
        accepted_correct = acceptance * fidelity
        assert accepted_correct + (1 - acceptance) * fidelity == fidelity
        if acceptance:
            assert accepted_correct / acceptance == fidelity
        else:
            assert accepted_correct == 0  # No undefined conditional score.
        count += 1
    return count


def centered_kick_energy():
    count = 0
    for mq, mp in product((F(-2, 3), F(0), F(3, 5)), repeat=2):
        q2, p2 = mq * mq + F(1, 2), mp * mp + F(1, 2)
        initial = (q2 + p2 - 1) / 2
        for x, y in product((F(0), F(1, 3), F(5, 4)), repeat=2):
            energies = [(q2 + 2 * sx * x * mq + x * x
                         + p2 + 2 * sy * y * mp + y * y - 1) / 2
                        for sx, sy in product((-1, 1), repeat=2)]
            # Finite centered signs guard the mean/second-moment identity;
            # the Gaussian moments and continuum averaging remain analytic.
            assert sum(energies, F(0)) / 4 == initial + (x * x + y * y) / 2
            count += 1
    return count


def product_prior_guards():
    cases = flag_cases = 0
    for i, j in product(range(17), repeat=2):
        hq, hp = F(i, 16), F(j, 16)
        priors = (hq * hp, (1 - hq) * hp, hq * (1 - hp), (1 - hq) * (1 - hp))
        assert sum(priors) == 1
        assert sum(sorted(priors, reverse=True)[:2]) == max(hq, 1 - hq, hp, 1 - hp)
        cases += 1
    for i, j in product(range(5), repeat=2):
        hq, hp = F(i, 4), F(j, 4)
        priors = (hq * hp, (1 - hq) * hp, hq * (1 - hp), (1 - hq) * (1 - hp))
        top_two = sum(sorted(priors, reverse=True)[:2])
        for factors in product((-1, 0, 1), repeat=4):
            hs = tuple(p * t for p, t in zip(priors, factors))
            weights = tuple(tuple((p + f * h) / 2 for p, h in zip(priors, hs))
                            for f in (-1, 1))
            assert all(w >= 0 for row in weights for w in row)
            assert sum(map(sum, weights)) == 1
            assert all(sum(row[e] for row in weights) == priors[e] for e in range(4))
            assert sum(map(max, weights)) <= top_two
            flag_cases += 1
    return cases, flag_cases


# Complex rational pairs avoid floating complex arithmetic in gauge guards.
def cz(a=0, b=0):
    return F(a), F(b)


def cadd(z, w):
    return z[0] + w[0], z[1] + w[1]


def cmul(z, w):
    return z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0]


def cstar(z):
    return z[0], -z[1]


def cscale(z, r):
    return z[0] * r, z[1] * r


def cmat_add(a, b):
    return tuple(tuple(cadd(z, w) for z, w in zip(row, other))
                 for row, other in zip(a, b))


def cmat_scale(a, r):
    return tuple(tuple(cscale(z, r) for z in row) for row in a)


def cmat_mul(a, b):
    return tuple(tuple(cadd(cmul(row[0], col[0]), cmul(row[1], col[1]))
                       for col in zip(*b)) for row in a)


def ctrace(a):
    return cadd(a[0][0], a[1][1])


def cpsd2(a):
    assert a[0][0][1] == a[1][1][1] == 0
    assert a[1][0] == cstar(a[0][1])
    assert a[0][0][0] >= 0 and a[1][1][0] >= 0
    determinant = cadd(cmul(a[0][0], a[1][1]), cscale(cmul(a[0][1], a[1][0]), -1))
    assert determinant[1] == 0 and determinant[0] >= 0


def phase_gauge_recovery():
    eye = ((cz(1), cz()), (cz(), cz(1)))
    xp = ((cz(), cz(1)), (cz(1), cz()))
    rho0 = cmat_scale(((cz(1), cz(1)), (cz(1), cz(1))), F(1, 2))
    pairs = effects = matrix_units = 0
    for z, s in ((F(3, 5), F(4, 5)), (F(5, 13), F(12, 13)),
                 (F(8, 17), F(15, 17)), (F(20, 29), F(21, 29))):
        assert z * z + s * s == 1 and 0 < z < 1
        phase = cmul(cz(z, s), cz(z, s))
        rho1 = cmat_scale(((cz(1), phase), (cstar(phase), cz(1))), F(1, 2))
        for rho in (rho0, rho1):
            cpsd2(rho)
            assert ctrace(rho) == cz(1) and cmat_mul(rho, rho) == rho
        assert rho0[0][0] == rho1[0][0] and rho0[1][1] == rho1[1][1]
        assert ctrace(cmat_mul(rho0, rho1)) == cz(z * z)
        delta = cmat_add(rho0, cmat_scale(rho1, -1))
        assert cmat_mul(delta, delta) == cmat_scale(eye, s * s)
        plus = cmat_scale(cmat_add(eye, cmat_scale(delta, 1 / s)), F(1, 2))
        minus = cmat_add(eye, cmat_scale(plus, -1))
        for effect in (plus, minus):
            cpsd2(effect)
            assert cmat_mul(effect, effect) == effect
            effects += 1
        h00, h01 = (ctrace(cmat_mul(plus, rho)) for rho in (rho0, rho1))
        h10, h11 = (ctrace(cmat_mul(minus, rho)) for rho in (rho0, rho1))
        assert h00 == h11 == cz((1 + s) / 2)
        assert h01 == h10 == cz((1 - s) / 2)
        e0 = cmat_scale(cmat_add(eye, cmat_scale(rho1, -1)), 1 / (1 + z))
        e1 = cmat_scale(cmat_add(eye, cmat_scale(rho0, -1)), 1 / (1 + z))
        fail = cmat_add(eye, cmat_scale(cmat_add(e0, e1), -1))
        for effect in (e0, e1, fail):
            cpsd2(effect)
            effects += 1
        t00, t01 = (ctrace(cmat_mul(e0, rho)) for rho in (rho0, rho1))
        t10, t11 = (ctrace(cmat_mul(e1, rho)) for rho in (rho0, rho1))
        f0, f1 = (ctrace(cmat_mul(fail, rho)) for rho in (rho0, rho1))
        assert (t00, t01, t10, t11) == (cz(1 - z), cz(), cz(), cz(1 - z))
        assert f0 == f1 == cz(z)
        for i, j in product(range(2), repeat=2):
            unit = tuple(tuple(cz(row == i and col == j) for col in range(2))
                         for row in range(2))
            flipped = cmat_mul(cmat_mul(xp, unit), xp)
            helstrom = cmat_add(cmat_scale(unit, (h00[0] + h11[0]) / 2),
                                cmat_scale(flipped, (h01[0] + h10[0]) / 2))
            assert helstrom == cmat_add(cmat_scale(unit, (1 + s) / 2),
                                        cmat_scale(flipped, (1 - s) / 2))
            assert ctrace(helstrom) == ctrace(unit)
            accepted = cmat_add(cmat_scale(unit, (t00[0] + t11[0]) / 2),
                                cmat_scale(flipped, (t01[0] + t10[0]) / 2))
            failed = cmat_add(cmat_scale(unit, f0[0] / 2), cmat_scale(flipped, f1[0] / 2))
            assert accepted == cmat_scale(unit, 1 - z)
            assert failed == cmat_scale(cmat_add(unit, flipped), z / 2)
            assert ctrace(cmat_add(accepted, failed)) == ctrace(unit)
            matrix_units += 1
        pairs += 1
    return pairs, effects, matrix_units


def partial_trace2(a, first):
    return tuple(tuple(sum((a[2 * k + i][2 * k + j] if first
                            else a[2 * i + k][2 * j + k] for k in range(2)), F(0))
                       for j in range(2)) for i in range(2))


def recovery_normalization():
    # Matching explicit primal/dual witnesses only, not a generic SDP solver.
    def scale(a, t):
        return tuple(tuple(t * z for z in row) for row in a)

    def trace(a):
        return sum((a[i][i] for i in range(len(a))), F(0))

    phi = tuple(tuple(F(i in (0, 3) and j in (0, 3), 2) for j in range(4))
                for i in range(4))
    assert mm(phi, phi) == phi and phi == tuple(zip(*phi))
    cases = accepted_cases = 0
    for rho, x, sigma in ((phi, scale(phi, 2), F(1)),
                           (scale(ident(4), F(1, 4)), scale(ident(4), F(1, 2)), F(1, 4))):
        assert trace(rho) == 1 and partial_trace2(rho, True) == scale(ident(2), F(1, 2))
        assert partial_trace2(x, True) == ident(2)
        gap = tuple(tuple(sigma * F(i == j) - rho[i][j] for j in range(4))
                    for i in range(4))
        # Dual residuals are respectively an orthogonal projector and zero.
        assert gap == tuple(zip(*gap)) and mm(gap, gap) == gap
        fidelity = trace(mm(rho, x)) / 2
        assert fidelity == sigma
        for acceptance in (F(0), F(1, 4), F(1, 2), F(3, 4), F(1)):
            xa = scale(x, acceptance)
            total = partial_trace2(xa, True)
            assert total == scale(ident(2), acceptance)
            assert trace(mm(partial_trace2(rho, True), total)) == acceptance
            assert trace(mm(rho, xa)) / 2 == acceptance * fidelity
            # I_R tensor S is scalar here, so this also checks all-input acceptance.
            assert partial_trace2(scale(rho, acceptance), False) == scale(ident(2), acceptance / 2)
            accepted_cases += 1
        cases += 1
    return cases, accepted_cases


def asymmetric_acceptance():
    # Normalized Choi state of amplitude damping gamma=3/4, in R,B order.
    gamma, root = F(3, 4), F(1, 2)
    assert root * root == 1 - gamma
    vector = (F(1), F(0), F(0), root)
    rho = tuple(tuple(vector[i] * vector[j] / 2 + F(i == j == 2) * gamma / 2
                      for j in range(4)) for i in range(4))
    half_eye = ((F(1, 2), F(0)), (F(0), F(1, 2)))
    rho_b = ((F(7, 8), F(0)), (F(0), F(1, 8)))
    assert partial_trace2(rho, False) == half_eye
    assert partial_trace2(rho, True) == rho_b
    count = 0
    for i, j in product(range(5), repeat=2):
        s0, s1 = F(i, 4), F(j, 4)
        weighted = tuple(tuple((s0 if row % 2 == 0 else s1) * z for z in entries)
                         for row, entries in enumerate(rho))
        average = F(7, 8) * s0 + F(1, 8) * s1
        assert sum((weighted[k][k] for k in range(4)), F(0)) == average
        reduced = partial_trace2(weighted, False)
        assert reduced == ((s0 / 2, F(0)), (F(0), (gamma * s0 + (1 - gamma) * s1) / 2))
        uniform = ((average / 2, F(0)), (F(0), average / 2))
        assert (reduced == uniform) == (s0 == s1)
        count += 1
    return count


def verify():
    triples = dominance()
    alignments, symplectic_phases = alignment()
    records, phases, matrix_units, ordered = zak_guards()
    symbolic, forms, scaling = energy()
    priors, flags = product_prior_guards()
    tags, effects, recovery_units = phase_gauge_recovery()
    sdp_cases, accepted_sdp_cases = recovery_normalization()
    return {"status": "passed", "rational_dominance_triples": triples,
            "alignment_circuits": alignments, "symplectic_phase_checks": symplectic_phases,
            "zak_records": records, "zak_phase_checks": phases,
            "logical_matrix_units": matrix_units, "ordered_weyl_phases": ordered,
            "symbolic_energy_cases": symbolic, "squeeze_form_cases": forms,
            "unnormalized_scaling_cases": scaling, "centered_kick_energy_cases": centered_kick_energy(),
            "thinning_cases": thinning(),
            "product_prior_cases": priors, "all_flags_diagonal_cases": flags,
            "pure_phase_tag_pairs": tags, "positive_recovery_effects": effects,
            "recovery_channel_matrix_units": recovery_units,
            "sdp_normalization_witnesses": sdp_cases,
            "accepted_sdp_normalization_cases": accepted_sdp_cases,
            "asymmetric_acceptance_cases": asymmetric_acceptance(),
            "scope": "Exact finite rational algebra only; all-function dominance, Gaussian integration, "
                     "Fourier completeness, Sobolev regularity, heat positivity, QEC, SDP duality, "
                     "the continuum decoder and device costs remain analytic. Phase-tag cases are not a Gaussian counterexample."}


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2, sort_keys=True))
