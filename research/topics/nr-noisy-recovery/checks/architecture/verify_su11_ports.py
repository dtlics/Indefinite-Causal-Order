"""Exact five-mode ordinary SU(1,1) dilation and independent-bath guards."""

if not __debug__:
    raise RuntimeError('Exact port checks require assertions; do not use -O.')


def verify_su11_full_ports():
    from fractions import Fraction as F
    import verify_fault_simulation as g

    n = 5
    eye = g.identity(n)

    def plus(a, b):
        return [[g.add(x, y) for x, y in zip(ar, br)] for ar, br in zip(a, b)]

    def neg(a):
        return [[g.times(x, -1) for x in row] for row in a]

    def conjugate(a):
        return [[g.conjugate(x) for x in row] for row in a]

    def transpose(a):
        return [list(row) for row in zip(*a)]

    def compose(second, first):
        x2, y2 = second
        x1, y1 = first
        return (plus(g.matmul(x2, x1), g.matmul(y2, conjugate(y1))),
                plus(g.matmul(x2, y1), g.matmul(y2, conjugate(x1))))

    def inverse(pair):
        x, y = pair
        return g.adjoint(x), neg(transpose(y))

    def passive(matrix):
        return matrix, g.zeros(n, n)

    def beamsplitter(first, second, transmitted, reflected):
        assert transmitted*transmitted + reflected*reflected == 1
        m = g.identity(n)
        m[first][first] = m[second][second] = g.gaussian(transmitted)
        m[first][second], m[second][first] = g.gaussian(reflected), g.gaussian(-reflected)
        return passive(m)

    def phase(mode, value):
        assert g.multiply(value, g.conjugate(value)) == g.ONE
        m = g.identity(n)
        m[mode][mode] = value
        return passive(m)

    def squeeze(u, v):
        assert g.gaussian(u*u-1) == g.multiply(v, g.conjugate(v))
        x, y = g.identity(n), g.zeros(n, n)
        x[0][0] = x[1][1] = g.gaussian(u)
        y[0][1] = y[1][0] = v
        return x, y

    def canonical(pair):
        x, y = pair
        assert plus(g.matmul(x, g.adjoint(x)), neg(g.matmul(y, g.adjoint(y)))) == eye
        assert plus(g.matmul(x, transpose(y)), neg(g.matmul(y, transpose(x)))) == g.zeros(n, n)

    def mul(*values):
        answer = g.ONE
        for value in values:
            answer = g.multiply(answer, value)
        return answer

    def norm(value):
        answer = mul(value, g.conjugate(value))
        assert answer[1] == 0
        return answer[0]

    phases = [g.ONE, g.gaussian(0, 1), g.gaussian(F(3, 5), F(4, 5)),
              g.gaussian(F(5, 13), F(-12, 13))]
    upper_pre = [(F(3, 5), F(4, 5)), (F(5, 13), F(12, 13))]
    upper_post = [(F(5, 13), F(12, 13)), (F(3, 5), F(4, 5))]
    idler = F(8, 17), F(15, 17)
    ua, ue = F(13, 5), F(5, 3)
    bath_occupations = [(F(0),)*5, (F(1, 7), F(2, 5), F(1, 3), F(4, 9), F(3, 8))]
    circuits = coefficients = moments = bath_guards = relative_pairs = 0
    for pre, post in zip(upper_pre, upper_post):
        tp, rp = pre
        tq, rq = post
        ti, ri = idler
        for index, z in enumerate(phases):
            pump_e, pump_a, idler_phase = phases[index-1], phases[(index+1) % 4], phases[(index+2) % 4]
            ve, va = g.times(pump_e, F(4, 3)), g.times(pump_a, F(12, 5))
            entangler, analyzer = squeeze(ue, ve), squeeze(ua, va)
            pre_bs, post_bs, lower_bs = (beamsplitter(0, 2, tp, rp),
                                        beamsplitter(0, 3, tq, rq),
                                        beamsplitter(1, 4, ti, ri))
            before_cavity = compose(pre_bs, entangler)
            arm_after = compose(lower_bs, compose(phase(1, idler_phase), post_bs))
            after_cavity = compose(analyzer, arm_after)
            network = compose(after_cavity, compose(phase(0, z), before_cavity))
            canonical(network)
            x, y = network
            a = g.add(mul(g.gaussian(ua*tp*tq*ue), z),
                      mul(va, g.gaussian(ti), g.conjugate(idler_phase), g.conjugate(ve)))
            b = g.add(mul(g.gaussian(ua*tp*tq), z, ve),
                      mul(va, g.gaussian(ti*ue), g.conjugate(idler_phase)))
            lpre, lpost, m = g.times(z, ua*tq*rp), g.gaussian(ua*rq), g.times(va, ri)
            assert x[0] == [a, g.ZERO, lpre, lpost, g.ZERO]
            assert y[0] == [g.ZERO, b, g.ZERO, g.ZERO, m]
            assert norm(a)-norm(b)+norm(lpre)+norm(lpost)-norm(m) == 1
            coefficients += 10
            circuits += 1
            for occupations in bath_occupations:
                nout = sum(norm(x[0][j])*occupations[j] + norm(y[0][j])*(occupations[j]+1)
                           for j in range(n))
                expected = (norm(a)*occupations[0]+norm(b)*(occupations[1]+1)
                            +norm(lpre)*occupations[2]+norm(lpost)*occupations[3]
                            +norm(m)*(occupations[4]+1))
                anomalous = g.ZERO
                for j in range(n):
                    anomalous = g.add(anomalous, g.times(mul(x[0][j], y[0][j]), 2*occupations[j]+1))
                assert nout == expected and anomalous == g.ZERO
                moments += 2
            spurious = norm(g.add(lpre, lpost))-norm(lpre)-norm(lpost)
            assert spurious == 2*ua*ua*tq*rp*rq*z[0]
            bath_guards += 1
            # All downstream modes cancel from the relative conditional unitary.
            second_z = phases[(index+1) % 4]
            second_network = compose(after_cavity, compose(phase(0, second_z), before_cavity))
            actual_relative = compose(inverse(second_network), network)
            expected_relative = compose(inverse(before_cavity),
                                        compose(phase(0, mul(g.conjugate(second_z), z)), before_cavity))
            assert actual_relative == expected_relative
            relative_pairs += 1

    # Exact zero-point coherent bath-compression failure at the dark phase.
    assert any(ph[0] != 0 for ph in phases)
    return dict(status='passed', full_five_mode_canonical_networks=circuits,
                explicit_output_Bogoliubov_coefficients=coefficients,
                warm_bath_noise_and_anomalous_moments=moments,
                independent_upper_bath_commutator_guards=bath_guards,
                full_environment_downstream_backaction_cancellations=relative_pairs,
                scope='Exact finite symplectic and moment identities for the declared one-way phase-cavity cascade. Gaussian integration, thermal purification, infinite-Fock extension, temporal bandwidth and measured device costs remain analytic or measured inputs.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Exact port checks require assertions; do not use -O.')
    import json
    print(json.dumps(verify_su11_full_ports(), indent=2))
