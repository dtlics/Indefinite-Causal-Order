"""Finite exact phase-dressed Raman instruments; no measured-rate assertion."""


if not __debug__:
    raise RuntimeError('Exact phase-covariance checks require assertions; do not use -O.')


def verify_raman_phase_covariance():
    from fractions import Fraction as F
    from itertools import product
    import verify_fault_simulation as g

    # Gaussian-rational coefficients adjoined with sqrt(2).
    z, one = (g.ZERO, g.ZERO), (g.ONE, g.ZERO)

    def plus(x, y):
        return g.add(x[0], y[0]), g.add(x[1], y[1])

    def mul(x, y):
        return (g.add(g.multiply(x[0], y[0]), g.times(g.multiply(x[1], y[1]), 2)),
                g.add(g.multiply(x[0], y[1]), g.multiply(x[1], y[0])))

    def conj(x):
        return g.conjugate(x[0]), g.conjugate(x[1])

    def q(x):
        return x, g.ZERO

    def scale(x, f):
        return g.times(x[0], f), g.times(x[1], f)

    def norm(v):
        out = z
        for x in v:
            out = plus(out, mul(x, conj(x)))
        assert out[0][1] == 0 and out[1] == g.ZERO
        return out[0][0]

    def swap_scatter(v, site, a, b, phase, scalar):
        out = [z] * 16
        bit = 1 << (3-site)
        for i, value in enumerate(v):
            p, s = bool(i & 8), bool(i & bit)
            target = i ^ (8 | bit) if p != s else i
            leg = (phase if p else g.conjugate(phase)) if p != s else g.ONE
            out[i] = plus(out[i], mul(q(a), value))
            out[target] = plus(out[target], mul(q(g.multiply(b, leg)), value))
        return [mul(q(scalar), x) for x in out]

    W = [[z] * 4 for _ in range(4)]
    W[0][0], W[3][0] = (g.ZERO, g.ONE), q(g.gaussian(2))
    W[1][1], W[2][1] = one, (g.ZERO, g.ONE)
    W[1][2], W[2][2] = q(g.gaussian(-1)), (g.ZERO, g.gaussian(-1))
    read_f = [(g.ZERO, g.ONE), z, z, q(g.gaussian(-1))]
    read_g = [z, (g.ZERO, g.ONE), q(g.gaussian(-1)), z]

    def processor(v):
        out = [z] * 16
        for i, value in enumerate(v):
            pq, ab = divmod(i, 4)
            for j in range(4):
                out[4*j+ab] = plus(out[4*j+ab], mul(W[j][pq], value))
        return out

    def herald(v, h):
        out = []
        for ab in range(4):
            value = z
            for pq in range(4):
                value = plus(value, mul(conj(h[pq]), v[4*pq+ab]))
            out.append(scale(value, F(1, 6)))
        return out

    phases = [g.ONE, g.gaussian(0, 1), g.gaussian(F(3, 5), F(4, 5)),
              g.gaussian(F(5, 13), F(-12, 13))]
    coefficients = [(g.gaussian(F(1, 3)), g.gaussian(F(2, 3)),
                     g.gaussian(F(1, 4)), g.gaussian(F(1, 2))),
                    (g.gaussian(F(1, 4), F(-1, 4)), g.gaussian(F(1, 2), F(1, 4)),
                     g.gaussian(F(1, 5), F(1, 10)), g.gaussian(F(2, 5), F(-1, 10)))]
    source = [z] * 16
    source[4] = source[8] = one
    passive_vectors = passive_norms = 0
    for x, y in product(phases, repeat=2):
        for a_a, b_a, a_b, b_b in coefficients:
            scalar_a, scalar_b = y, g.conjugate(x)
            v = swap_scatter(source, 2, a_a, b_a, x, scalar_a)
            v = processor(v)
            v = swap_scatter(v, 3, a_b, b_b, y, scalar_b)
            actual_f, actual_g = herald(v, read_f), herald(v, read_g)
            actual_g = [scale(value, F(1, 2) if i >= 2 else 1)
                        for i, value in enumerate(actual_g)]
            base = g.multiply(g.multiply(b_a, b_b), g.multiply(scalar_a, scalar_b))
            expected_f = [z, scale(q(g.multiply(base, y)), F(1, 3)),
                          scale(q(g.multiply(base, x)), F(1, 3)), z]
            expected_g = [scale((g.ZERO, base), F(1, 6)), z, z,
                          scale((g.ZERO, g.multiply(base, g.multiply(x, y))), F(1, 6))]
            assert actual_f == expected_f and actual_g == expected_g
            passive_vectors += 2
            bb2 = g.multiply(base, g.conjugate(base))[0]
            assert norm(actual_f) == F(2, 9)*bb2
            assert norm(actual_g) == F(1, 9)*bb2
            passive_norms += 2

    # Full six-qubit circuit, before the outcome-dependent A correction.
    # Pair order P,Q,A,A',B,B'; source and Bell-bra normalization give 1/4.
    source6 = [g.ZERO] * 64
    for p, aa, bb in product(range(2), repeat=3):
        source6[48*p+12*aa+3*bb] = g.ONE

    def scatter6(v, site, a, b, phase, scalar):
        out = [g.ZERO] * 64
        bit = 1 << (5-site)
        for i, value in enumerate(v):
            p, spin = bool(i & 32), bool(i & bit)
            target = i ^ (32 | bit) if p != spin else i
            leg = (phase if p else g.conjugate(phase)) if p != spin else g.ONE
            out[i] = g.add(out[i], g.multiply(a, value))
            out[target] = g.add(out[target], g.multiply(g.multiply(b, leg), value))
        return [g.multiply(scalar, value) for value in out]

    def bell_readout(v, m, n):
        return [g.times(g.add(v[16*m+matter],
                    g.times(v[32+16*(1 ^ m)+matter], (-1)**n)), F(1, 4))
                for matter in range(16)]

    def phase_power(x, exponent):
        assert exponent in (-1, 0, 1)
        return x if exponent == 1 else (g.conjugate(x) if exponent == -1 else g.ONE)

    ancilla_vectors = ancilla_coefficients = 0
    for x, y in product(phases, repeat=2):
        for a_a, b_a, a_b, b_b in coefficients:
            base = scatter6(scatter6(source6, 2, a_a, b_a, g.ONE, g.ONE),
                            4, a_b, b_b, g.ONE, g.ONE)
            scalar_a, scalar_b = y, g.conjugate(x)
            rotated = scatter6(scatter6(source6, 2, a_a, b_a, x, scalar_a),
                               4, a_b, b_b, y, scalar_b)
            scalar = g.multiply(scalar_a, scalar_b)
            for m, n in product(range(2), repeat=2):
                actual, unrotated = bell_readout(rotated, m, n), bell_readout(base, m, n)
                expected = []
                for i, value in enumerate(unrotated):
                    aa, ap, bb, bp = (i >> 3) & 1, (i >> 2) & 1, (i >> 1) & 1, i & 1
                    factor = g.multiply(scalar, g.multiply(
                        phase_power(x, aa-ap), phase_power(y, bb-bp)))
                    expected.append(g.multiply(factor, value))
                assert actual == expected
                ancilla_vectors += 1
                ancilla_coefficients += 16

    return dict(status='passed', passive_full_phase_branch_vectors=passive_vectors,
                passive_phase_independent_branch_probabilities=passive_norms,
                full_six_qubit_rotated_ancilla_branches=ancilla_vectors,
                full_six_qubit_rotated_ancilla_coefficients=ancilla_coefficients,
                scope='Finite Gaussian-rational plus sqrt(2) circuit checks of the phase-covariant filter and ancilla instruments. General phase covariance and scalar cancellation follow analytically. No unknown Raman-frame immunity, device ports, PSD model, or delivered rate is certified.')


if __name__ == '__main__':
    import json
    print(json.dumps(verify_raman_phase_covariance(), indent=2))
