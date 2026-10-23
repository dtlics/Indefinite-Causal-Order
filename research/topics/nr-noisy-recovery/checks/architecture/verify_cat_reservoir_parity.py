"""Exact finite guards for the cat-reservoir parity theorem and expansion.

Matrix examples retain a buffer and complete CP maps. CCR normal ordering
checks polynomial identities without a Fock cutoff. Finite-time domains,
measured parameters, convergence and physical gate costs remain analytic
or experimental inputs, rather than claims of this replay.
"""

if not __debug__:
    raise RuntimeError('Exact cat checks require assertions; do not use -O.')


def verify_cat_reservoir_parity():
    from fractions import Fraction as F
    from math import comb, factorial
    import verify_fault_simulation as g

    def plus(*matrices):
        out = g.zeros(len(matrices[0]), len(matrices[0][0]))
        for matrix in matrices:
            out = [[g.add(x, y) for x, y in zip(ar, br)] for ar, br in zip(out, matrix)]
        return out

    def scaled(matrix, scalar):
        return [[g.times(x, scalar) for x in row] for row in matrix]

    def diagonal(entries):
        out = g.zeros(len(entries), len(entries))
        for j, value in enumerate(entries):
            out[j][j] = g.gaussian(value)
        return out

    def normalized(kraus, size):
        assert plus(*(g.matmul(g.adjoint(k), k) for k in kraus)) == g.identity(size)

    # A complete finite channel on four memory levels. A jump changes
    # parity; its rational strengths are guards, not a fitted semigroup.
    d = 4
    c = [F(3, 5), F(5, 13), F(8, 17)]
    s = [F(4, 5), F(12, 13), F(15, 17)]
    down0 = diagonal([F(1)]+c)
    down1 = g.zeros(d, d)
    up0 = diagonal(c+[F(1)])
    up1 = g.zeros(d, d)
    for j in range(3):
        down1[j][j+1] = g.gaussian(s[j])
        up1[j+1][j] = g.gaussian(s[j])
    a_mem = [scaled(down0, F(3, 5)), scaled(down1, F(3, 5)),
             scaled(up0, F(4, 5)), scaled(up1, F(4, 5))]
    normalized(a_mem, d)
    a_channel = [g.tensor(k, g.identity(2)) for k in a_mem]
    parity = g.tensor(diagonal([1, -1, 1, -1]), g.identity(2))
    size = d*2

    # Nonlinear memory-buffer exchange: mixes (memory,buffer) |0,0>
    # with |2,1>, and |1,0> with |3,1>. It is even in memory parity.
    u = g.identity(size)
    for j, k in [(0, 5), (2, 7)]:
        u[j][j] = u[k][k] = g.gaussian(F(3, 5))
        u[j][k], u[k][j] = g.gaussian(0, F(4, 5)), g.gaussian(0, F(4, 5))
    assert g.matmul(g.adjoint(u), u) == g.identity(size)
    b0 = diagonal([F(1), F(5, 13)])
    b1 = g.zeros(2, 2)
    b1[0][1] = g.gaussian(F(12, 13))
    b_channel = [g.matmul(g.tensor(g.identity(d), k), u) for k in [b0, b1]]
    normalized(b_channel, size)
    cp = g.zeros(2*size, 2*size)
    for j in range(size):
        cp[j][j] = g.ONE
        for k in range(size):
            cp[size+j][size+k] = parity[j][k]
    full_kraus = flag_identities = normalizations = 0
    for second, first in [(b_channel, a_channel), (a_channel, b_channel)]:
        serial = [g.matmul(v, w) for v in second for w in first]
        normalized(serial, size)
        normalizations += 1
        flagged = [[], []]
        for k in serial:
            reflected = g.matmul(parity, g.matmul(k, parity))
            if reflected == k:
                sign = 1
            else:
                assert reflected == scaled(k, -1)
                sign = -1
            actual = g.matmul(cp, g.matmul(g.tensor(g.identity(2), k), cp))
            expected = g.tensor(diagonal([1, sign]), k)
            assert actual == expected
            full_kraus += 1
            for flag, epsilon in enumerate([1, -1]):
                # <epsilon| actual |+>, with both sqrt(2) factors.
                measured = [[g.times(g.add(actual[j][l], g.times(actual[size+j][size+l], epsilon)), F(1, 2))
                             for l in range(size)] for j in range(size)]
                expected_flag = k if epsilon == sign else g.zeros(size, size)
                assert measured == expected_flag
                flagged[flag].append(measured)
                flag_identities += 1
        normalized(flagged[0]+flagged[1], size)
        normalizations += 1

    # Complete ideal SWITCH flags have the ordinary randomized-order
    # marginal for all inputs/reference, checked as full Choi matrices.
    switch_flags = []
    actual_choi = g.zeros(size*size, size*size)
    mixed_choi = g.zeros(size*size, size*size)
    switch_pairs = 0
    for ak in a_channel:
        for bk in b_channel:
            ba, ab = g.matmul(bk, ak), g.matmul(ak, bk)
            for epsilon in [1, -1]:
                mk = scaled(plus(ba, scaled(ab, epsilon)), F(1, 2))
                switch_flags.append(mk)
                g.add_outer(actual_choi, g.vectorize(mk), F(1))
            g.add_outer(mixed_choi, g.vectorize(ba), F(1, 2))
            g.add_outer(mixed_choi, g.vectorize(ab), F(1, 2))
            switch_pairs += 1
    assert actual_choi == mixed_choi
    normalized(switch_flags, size)

    # Normally ordered CCR polynomials: (m,n) represents (a^dagger)^m a^n.
    def clean(poly):
        return {key: value for key, value in poly.items() if value != g.ZERO}

    def padd(*polys):
        out = {}
        for poly in polys:
            for key, value in poly.items():
                out[key] = g.add(out.get(key, g.ZERO), value)
        return clean(out)

    def pscale(poly, scalar):
        return clean({key: g.multiply(value, scalar) for key, value in poly.items()})

    def pmul(left, right):
        out = {}
        for (m, n), value in left.items():
            for (p, q), other in right.items():
                for k in range(min(n, p)+1):
                    key = m+p-k, n+q-k
                    coefficient = g.times(g.multiply(value, other), comb(n, k)*comb(p, k)*factorial(k))
                    out[key] = g.add(out.get(key, g.ZERO), coefficient)
        return clean(out)

    def pdag(poly):
        return {(n, m): g.conjugate(value) for (m, n), value in poly.items()}

    def comm(left, right):
        return padd(pmul(left, right), pscale(pmul(right, left), g.gaussian(-1)))

    def smul(left, right):
        out = {}
        for (a1, b1), op in left.items():
            for (a2, b2), other in right.items():
                key = a1+a2, b1+b2
                out[key] = padd(out.get(key, {}), pmul(op, other))
        return {key: value for key, value in out.items() if value}

    def sminus(left, right):
        keys = left.keys() | right.keys()
        return {key: value for key in keys
                if (value := pscale(padd(left.get(key, {}), pscale(right.get(key, {}), g.gaussian(-1))), g.gaussian(F(1, 2))))}

    one = {(0, 0): g.ONE}
    a = {(0, 1): g.ONE}
    adag = pdag(a)
    number = {(1, 1): g.ONE}
    lambdas = [g.ZERO, g.gaussian(F(1, 2)), g.gaussian(F(26, 25)), g.gaussian(F(3, 5), F(4, 5))]
    alphas_squared = [g.ZERO, g.gaussian(2), g.gaussian(0, 1)]
    commutators = nojump = qnorms = 0
    for lam in lambdas:
        for alpha_squared in alphas_squared:
            f = padd(pmul(a, a), pscale(number, lam),
                     pscale(one, g.multiply(g.gaussian(-1), g.multiply(g.add(g.ONE, lam), alpha_squared))))
            assert all((m+n) % 2 == 0 for m, n in f)
            assert comm(f, a) == pscale(a, g.times(lam, -1))
            qop = padd(pscale(a, g.gaussian(2)), pscale(adag, lam))
            assert comm(f, adag) == qop
            commutators += 2
            lamnorm = g.multiply(lam, g.conjugate(lam))[0]
            expected_norm = padd(pscale(number, g.gaussian(4+lamnorm)), pscale(one, g.gaussian(lamnorm)),
                                 pscale(pmul(adag, adag), g.times(lam, 2)),
                                 pscale(pmul(a, a), g.times(g.conjugate(lam), 2)))
            assert pmul(pdag(qop), qop) == expected_norm
            qnorms += 1
            ldown = pscale(a, g.gaussian(F(3, 5)))
            lup = pscale(adag, g.gaussian(F(4, 5)))
            lb = pscale(f, g.gaussian(F(5, 13)))
            ra = padd(pscale(padd(pmul(pdag(ldown), ldown), pmul(pdag(lup), lup)), g.gaussian(F(1, 2))),
                      pscale(number, g.gaussian(0, F(2, 7))))
            rb = padd(pscale(pmul(pdag(lb), lb), g.gaussian(F(1, 2))),
                      pscale(padd(pmul(a, a), pmul(adag, adag)), g.gaussian(0, F(3, 11))))
            a0 = {(0, 0): one, (2, 0): pscale(ra, g.gaussian(-1))}
            b0 = {(0, 0): one, (0, 2): pscale(rb, g.gaussian(-1))}
            bs = {(0, 1): lb}
            cases = [(a0, b0, (2, 2), pscale(comm(rb, ra), g.gaussian(F(1, 2)))),
                     (a0, bs, (2, 1), pscale(comm(lb, ra), g.gaussian(F(-1, 2))))]
            for lop in [ldown, lup]:
                aj = {(1, 0): lop}
                cases.extend([(aj, b0, (1, 2), pscale(comm(rb, lop), g.gaussian(F(-1, 2)))),
                              (aj, bs, (1, 1), pscale(comm(lb, lop), g.gaussian(F(1, 2))))])
            for left, right, power, expected in cases:
                actual = sminus(smul(right, left), smul(left, right))
                assert actual.get(power, {}) == expected
                assert all(key == power for key in actual)
                nojump += 1

    nbar, lam, nth = F(41, 10), F(26, 25), F(93, 100)
    root_upper = F(23, 5)
    assert root_upper**2 >= nbar*(nbar+1)
    heating_lower = 4*nbar+lam**2*(nbar+1)-4*lam*root_upper
    loss_weight = lam**2*nbar
    assert heating_lower == F(17376, 6250)
    assert loss_weight == F(27716, 6250)
    heating_fraction = nth*heating_lower/((nth+1)*loss_weight+nth*heating_lower)
    assert heating_fraction > F(23, 100)
    return dict(status='passed', complete_memory_buffer_normalizations=normalizations,
                full_control_data_kraus_identities=full_kraus,
                all_flag_kraus_identities=flag_identities,
                full_switch_mixed_order_choi_kraus_pairs=switch_pairs,
                ccr_loss_heating_commutators=commutators,
                nojump_and_jump_mixed_coefficients=nojump,
                thermal_jump_norm_polynomials=qnorms,
                nominal_heating_fraction_lower_bound=str(heating_fraction),
                scope='Exact finite CP/parity and formal CCR coefficient guards. General trace-class covariance, trajectory convergence, small-time remainders, physical bath/order access, gate errors and measured memory utility remain analytic or experimental inputs; no full heralded frontier dominance.')


if __name__ == '__main__':
    import json
    print(json.dumps(verify_cat_reservoir_parity(), indent=2))
