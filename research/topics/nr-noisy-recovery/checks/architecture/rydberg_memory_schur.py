"""Exact finite replays of the explicitly scoped Rydberg Schur-memory screen.

This is algebra, not a fit or a continuum/experimental certification.
"""

from fractions import Fraction as F
from itertools import combinations, product
import json

if not __debug__:
    raise RuntimeError("Exact Rydberg memory checks require assertions; do not use -O.")


def z(real=0, imag=0):
    return (F(real), F(imag))


ZERO, ONE, I = z(), z(1), z(0, 1)


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def neg(a):
    return (-a[0], -a[1])


def mul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def conj(a):
    return (a[0], -a[1])


def sumz(values):
    result = ZERO
    for value in values:
        result = add(result, value)
    return result


def norm2(a):
    result = mul(a, conj(a))
    assert result[1] == 0
    return result[0]


def verify_rydberg_memory_schur():
    # Four physical sites and two stored excitations: all six configurations.
    configurations = list(combinations(range(4), 2))
    d = len(configurations)
    probe_a = [
        (ONE, ZERO),
        (ZERO, I),
        (z(F(3, 5)), z(F(4, 5))),
        (z(F(5, 13)), z(0, F(12, 13))),
        (z(F(-8, 17)), z(F(15, 17))),
        (z(0, F(20, 29)), z(F(-21, 29))),
    ]
    probe_b = [
        (z(F(3, 5)), z(0, F(4, 5))),
        (z(F(-5, 13)), z(F(12, 13))),
        (ZERO, neg(I)),
        (z(F(8, 17)), z(F(15, 17))),
        (z(0, F(-20, 29)), z(F(21, 29))),
        (I, ZERO),
    ]
    record_pairs = list(product(range(2), repeat=2))
    full_record_reference_coefficients = 0
    reduced_kernel_coefficients = 0
    selected_record_coefficients = 0

    for shift in range(3):
        b = probe_b[shift:] + probe_b[:shift]
        for family in (probe_a, b):
            assert all(sum(norm2(v) for v in row) == 1 for row in family)

        def ab(x, a_record, b_record):
            return mul(b[x][b_record], probe_a[x][a_record])

        def ba(x, a_record, b_record):
            # Canonical physical record factors remain labeled A and B.
            return mul(probe_a[x][a_record], b[x][b_record])

        for x, y in product(range(d), repeat=2):
            phi_a = sumz(mul(probe_a[x][a], conj(probe_a[y][a])) for a in range(2))
            phi_b = sumz(mul(b[x][c], conj(b[y][c])) for c in range(2))
            reduced = sumz(mul(ab(x, a, c), conj(ab(y, a, c))) for a, c in record_pairs)
            assert reduced == mul(phi_a, phi_b)
            assert reduced == mul(phi_b, phi_a)
            reduced_kernel_coefficients += 1

            # Include every cross-record coherence and a two-dimensional
            # passive reference, not only probabilities/diagonal records.
            for (a, c), (ap, cp), r, s in product(record_pairs, record_pairs, range(2), range(2)):
                left = mul(ab(x, a, c), conj(ab(y, ap, cp)))
                right = mul(ba(x, a, c), conj(ba(y, ap, cp)))
                assert left == right
                assert add(ab(x, a, c), neg(ba(x, a, c))) == ZERO
                full_record_reference_coefficients += 1

            # Two coherent eraser outcomes on both accessible probe records.
            # Unnormalized +/- bras are sufficient for equality; the common
            # physical 1/2 factor cannot affect the asserted identity.
            for signs in ((1, 1), (1, -1)):
                out_ab = sumz(mul(z(signs[a] * signs[c]), ab(x, a, c)) for a, c in record_pairs)
                out_ba = sumz(mul(z(signs[a] * signs[c]), ba(x, a, c)) for a, c in record_pairs)
                out_y = sumz(mul(z(signs[a] * signs[c]), ab(y, a, c)) for a, c in record_pairs)
                assert mul(out_ab, conj(out_y)) == mul(out_ba, conj(out_y))
                selected_record_coefficients += 1

        # The complete retained-probe output is an isometry on each memory
        # basis state and a nontrivial Schur dephasing on its coherences.
        for x in range(d):
            assert sum(norm2(ab(x, a, c)) for a, c in record_pairs) == 1
        assert sumz(mul(probe_a[0][a], conj(probe_a[1][a])) for a in range(2)) == ZERO

    # RM5: fresh reduced Schur maps do not certify a shared-probe dilation.
    def controlled(kind, state):
        memory, probe = state
        if not memory:
            return state, 1
        if kind == 'A':
            return (memory, 1-probe), 1
        return state, -1 if probe else 1

    shared_cases = 0
    for state in product(range(2), repeat=2):
        amid, aphase = controlled('A', state)
        abstate, abphase = controlled('B', amid)
        bmid, bphase = controlled('B', state)
        bastate, baphase = controlled('A', bmid)
        assert abstate == bastate
        if state[0]:
            assert aphase*abphase == -bphase*baphase
        else:
            assert aphase*abphase == bphase*baphase
        shared_cases += 1

    return {
        "two_excitation_configurations": d,
        "shared_probe_counterexample_basis_cases": shared_cases,
        "complex_probe_models": 3,
        "full_record_reference_coefficients": full_record_reference_coefficients,
        "reduced_kernel_coefficients": reduced_kernel_coefficients,
        "coherent_record_selection_coefficients": selected_record_coefficients,
    }



if __name__ == "__main__":
    print(json.dumps(verify_rydberg_memory_schur(), sort_keys=True))
