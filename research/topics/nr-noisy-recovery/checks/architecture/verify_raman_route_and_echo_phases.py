"""Exact accepted-vector guards for route phase and ordinary double heralds."""


if not __debug__:
    raise RuntimeError('Exact route/echo checks require assertions; do not use -O.')


def verify_raman_route_and_echo_phases():
    from fractions import Fraction as F
    from itertools import product
    import verify_fault_simulation as g

    def phase_norm(z):
        value = g.multiply(z, g.conjugate(z))
        assert value[1] == 0
        return value[0]

    def scatter(vector, site, a, b, phase):
        output = [g.ZERO] * 8
        for index, value in enumerate(vector):
            photon, aa, bb = (index >> 2) & 1, (index >> 1) & 1, index & 1
            spin = aa if site == 1 else bb
            target = (spin << 2) + ((photon if site == 1 else aa) << 1) + (photon if site == 2 else bb)
            twist = (phase if photon else g.conjugate(phase)) if photon != spin else g.ONE
            output[index] = g.add(output[index], g.multiply(a, value))
            output[target] = g.add(output[target], g.multiply(g.multiply(b, twist), value))
        return output

    phases = (g.ONE, g.gaussian(-1), g.gaussian(0, 1),
              g.gaussian(0, -1), g.gaussian(F(3, 5), F(4, 5)))
    for phase in phases:
        assert phase_norm(phase) == 1
    nodes = ((g.gaussian(F(3, 10), F(2, 5)), g.gaussian(F(3, 10), F(-1, 5))),
             (g.gaussian(F(1, 10)), g.gaussian(F(9, 10))),
             (g.ONE, g.ZERO), (g.ZERO, g.ONE))
    source = [g.ZERO] * 8
    source[4] = g.ONE
    route_cases = false_photon_guards = 0
    for (a_a, b_a), (a_b, b_b), phase_a, phase_b in product(nodes, nodes, phases, phases):
        for a, b in ((a_a, b_a), (a_b, b_b)):
            assert phase_norm(g.add(a, b)) <= 1
            assert phase_norm(g.add(a, g.times(b, -1))) <= 1
        ab = scatter(scatter(source, 1, a_a, b_a, phase_a), 2, a_b, b_b, phase_b)
        ba = scatter(scatter(source, 2, a_b, b_b, phase_b), 1, a_a, b_a, phase_a)
        for route in phases:
            actual = [g.times(g.add(x, g.times(g.multiply(route, y), -1)), F(1, 2)) for x, y in zip(ab, ba)]
            expected = [g.ZERO] * 8
            expected[2] = g.times(g.multiply(g.multiply(phase_a, b_a),
                                           g.add(g.add(a_b, b_b), g.times(g.multiply(route, a_b), -1))), F(1, 2))
            expected[1] = g.times(g.multiply(g.multiply(phase_b, b_b),
                                           g.add(a_a, g.times(g.multiply(route, g.add(a_a, b_a)), -1))), F(1, 2))
            expected[4] = g.times(g.multiply(g.multiply(a_a, a_b), g.add(g.ONE, g.times(route, -1))), F(1, 2))
            assert actual == expected
            if route != g.ONE and a_a != g.ZERO and a_b != g.ZERO:
                assert actual[4] != g.ZERO
                false_photon_guards += 1
            route_cases += 1

    def click(vector, ca, cb, sign):
        return [g.multiply(g.add(g.times(ca, aa), g.times(cb, sign * bb)), vector[2 * aa + bb])
                for aa, bb in product(range(2), repeat=2)]

    # Both +/- clicks are contractions with a positive residual failure effect.
    ca1, cb1 = g.gaussian(F(3, 20), F(1, 5)), g.gaussian(F(3, 20), F(-1, 10))
    ca2, cb2 = g.gaussian(F(1, 20)), g.gaussian(F(9, 20))
    for ca, cb in ((ca1, cb1), (ca2, cb2)):
        assert 2 * (phase_norm(ca) + phase_norm(cb)) <= 1
    double_cases = 0
    four = phases[:4]
    for eta_a, eta_b, chi_a, chi_b in product(four, repeat=4):
        initial = [g.times(value, F(1, 2)) for value in
                   (g.ONE, chi_b, chi_a, g.multiply(chi_a, chi_b))]
        for sign1, sign2 in product((-1, 1), repeat=2):
            first = click(initial, ca1, cb1, sign1)
            flipped = []
            for aa, bb in product(range(2), repeat=2):
                rotation = g.multiply(eta_a if aa else g.conjugate(eta_a),
                                      eta_b if bb else g.conjugate(eta_b))
                flipped.append(g.multiply(rotation, first[2 * (aa ^ 1) + (bb ^ 1)]))
            actual = click(flipped, ca2, cb2, sign2)
            expected = [g.ZERO] * 4
            expected[1] = g.times(g.multiply(g.multiply(g.multiply(ca1, cb2), chi_a),
                                             g.multiply(g.conjugate(eta_a), eta_b)), F(sign2, 2))
            expected[2] = g.times(g.multiply(g.multiply(g.multiply(cb1, ca2), chi_b),
                                             g.multiply(eta_a, g.conjugate(eta_b))), F(sign1, 2))
            assert actual == expected
            double_cases += 1
    return dict(status='passed', full_route_phase_vectors=route_cases,
                unmatched_route_false_photon_guards=false_photon_guards,
                complete_double_herald_spin_axis_vectors=double_cases,
                scope='Exact finite full-vector route and two-click phase identities, with normalized spin source and contractive click branches. No physical compilation of cycling-emission double heralds from Raman SWAP, measured PSD, or delivered rate is certified.')


if __name__ == '__main__':
    import json
    print(json.dumps(verify_raman_route_and_echo_phases(), indent=2))
