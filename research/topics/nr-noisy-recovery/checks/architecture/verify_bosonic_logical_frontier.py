"""Exact finite guards for the fixed product-decoder bosonic comparator.

The all-function dominance proof, Gaussian integrals, Fourier completeness,
Sobolev regularity, continuum decoder and physical control costs remain
analytic in methods/bosonic-logical-frontier.md. No floating grid is used.
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


def verify():
    triples = dominance()
    alignments, symplectic_phases = alignment()
    records, phases, matrix_units, ordered = zak_guards()
    symbolic, forms, scaling = energy()
    return {"status": "passed", "rational_dominance_triples": triples,
            "alignment_circuits": alignments, "symplectic_phase_checks": symplectic_phases,
            "zak_records": records, "zak_phase_checks": phases,
            "logical_matrix_units": matrix_units, "ordered_weyl_phases": ordered,
            "symbolic_energy_cases": symbolic, "squeeze_form_cases": forms,
            "unnormalized_scaling_cases": scaling, "centered_kick_energy_cases": centered_kick_energy(),
            "thinning_cases": thinning(),
            "scope": "Exact finite rational algebra only; all-function dominance, Gaussian integration, "
                     "Fourier completeness, Sobolev regularity, the continuum decoder and device costs remain analytic."}


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2, sort_keys=True))
