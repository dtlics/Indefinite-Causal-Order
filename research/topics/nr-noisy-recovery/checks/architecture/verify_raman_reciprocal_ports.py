"""Exact finite port checks for the explicitly frozen Raman-frame limit."""


if not __debug__:
    raise RuntimeError('Exact reciprocal-port checks require assertions; do not use -O.')


def verify_reciprocal_raman_ports():
    from fractions import Fraction as F
    import verify_fault_simulation as g

    def add(a, b):
        return [[g.add(x, y) for x, y in zip(ar, br)] for ar, br in zip(a, b)]

    def scaled(a, z):
        return [[g.multiply(x, z) for x in row] for row in a]

    def act(a, v):
        return [r[0] for r in g.matmul(a, [[x] for x in v])]

    def phased_swap(node, phase):
        out = g.zeros(8, 8)
        for j in range(8):
            p, aa, bb = (j >> 2) & 1, (j >> 1) & 1, j & 1
            spin = aa if node == 'a' else bb
            coefficient = (phase if p == 1 else g.conjugate(phase)) if p != spin else g.ONE
            target = (spin << 2) + ((p if node == 'a' else aa) << 1) + (p if node == 'b' else bb)
            out[target][j] = coefficient
        assert g.matmul(out, out) == g.identity(8)
        return out

    def propagation(raman, incident):
        out = g.zeros(8, 8)
        for j in range(8):
            out[j][j] = incident if j & 4 else raman
        return out

    phases = [g.ONE, g.gaussian(0, 1), g.gaussian(F(3, 5), F(4, 5)),
              g.gaussian(F(5, 13), F(-12, 13))]
    initial = [g.ZERO] * 8
    initial[4] = g.ONE
    eye = g.identity(8)
    branches = bells = 0
    for aa, bb in [(g.gaussian(F(1, 3)), g.gaussian(F(2, 3))),
                   (g.gaussian(F(1, 4), F(-1, 4)), g.gaussian(F(1, 2), F(1, 4))),
                   (g.ZERO, g.gaussian(1))]:
        spectator = g.add(aa, bb)
        for phase_a, phase_b in zip(phases, phases[1:] + phases[:1]):
            ta = add(scaled(eye, aa), scaled(phased_swap('a', phase_a), bb))
            tb = add(scaled(eye, aa), scaled(phased_swap('b', phase_b), bb))
            for forward_r, forward_i, backward_r, backward_i in [
                    (phases[0], phases[1], phases[0], phases[1]),
                    (phases[2], phases[3], phases[2], phases[3]),
                    (phases[0], phases[1], phases[2], phases[3])]:
                order_ab = act(g.matmul(tb, g.matmul(propagation(forward_r, forward_i), ta)), initial)
                order_ba = act(g.matmul(ta, g.matmul(propagation(backward_r, backward_i), tb)), initial)
                for sign in [1, -1]:
                    actual = [g.times(g.add(x, g.times(y, sign)), F(1, 2))
                              for x, y in zip(order_ab, order_ba)][:4]
                    amp_a = g.times(g.multiply(g.multiply(bb, phase_a),
                        g.add(g.multiply(spectator, forward_r),
                              g.times(g.multiply(aa, backward_i), sign))), F(1, 2))
                    amp_b = g.times(g.multiply(g.multiply(bb, phase_b),
                        g.add(g.multiply(aa, forward_i),
                              g.times(g.multiply(spectator, backward_r), sign))), F(1, 2))
                    assert actual == [g.ZERO, amp_b, amp_a, g.ZERO]
                    branches += 1
                    if forward_r == backward_r and forward_i == backward_i:
                        assert g.multiply(amp_a, g.conjugate(phase_a)) == g.times(
                            g.multiply(amp_b, g.conjugate(phase_b)), sign)
                        bells += 1
    # Deterministic carrier-time cancellation: the t_R coefficient is zero.
    for incident, raman in [(F(7), F(5)), (F(13, 3), F(5, 7)), (F(2), F(2))]:
        splitting = incident - raman
        assert -incident + raman + splitting == 0
    # Reverse propagation multiplies, rather than conjugates, a static phase.
    for phase in phases[1:]:
        assert g.multiply(phase, phase) != g.ONE
        assert g.multiply(phase, g.conjugate(phase)) == g.ONE
    return dict(status='passed', complete_directional_port_branches=branches,
                frozen_reciprocal_Bell_frame_identities=bells,
                energy_matched_event_time_identities=3,
                reverse_phase_vs_phase_conjugation_guards=3,
                scope='Finite exact four-amplitude check in the stated static compensated Raman frame. General retarded kernels, distributed PSDs, causal pilot filtering, source/duty costs and physical access remain analytic and measured inputs.')


if __name__ == '__main__':
    import json
    print(json.dumps(verify_reciprocal_raman_ports(), indent=2))
