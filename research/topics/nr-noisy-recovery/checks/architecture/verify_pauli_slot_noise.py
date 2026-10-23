"""Exact finite checks for the local Pauli kernel and discarded-target scope."""

if not __debug__:
    raise RuntimeError("Run this checker with assertions enabled.")


def verify():
    from fractions import Fraction as F

    def add(*ps):
        out = [F(0)] * max(map(len, ps))
        for p in ps:
            for i, v in enumerate(p):
                out[i] += v
        return tuple(out)

    def scale(a, p):
        return tuple(a * v for v in p)

    def mul(p, q):
        out = [F(0)] * (len(p) + len(q) - 1)
        for i, a in enumerate(p):
            for j, b in enumerate(q):
                out[i + j] += a * b
        return tuple(out)

    def chi(a, b):
        return (-1) ** (((a & 1) * (b >> 1) + (a >> 1) * (b & 1)) % 2)

    def bernstein2(p):
        p = tuple(p) + (F(0),) * (3 - len(p))
        a, b, c = p
        return a, a + b / 2, a + b + c

    nu = (F(0), F(1))
    one_minus = (F(1), F(-1))
    n2, nq, q2 = mul(nu, nu), mul(nu, one_minus), mul(one_minus, one_minus)
    law = [(F(1, 4), F(3, 4))] + [(F(1, 4), F(-1, 4))] * 3
    r = add(n2, scale(2, nq), scale(F(1, 4), q2))
    assert r == (F(1, 4), F(3, 2), F(-3, 4))
    assert add(*law) == (F(1), F(0))
    pairs = envelopes = 0
    for a in range(4):
        for b in range(4):
            direct = (F(0), F(0), F(0))
            for u in range(4):
                for v in range(4):
                    direct = add(direct, scale(chi(a ^ u, b ^ v), mul(law[u], law[v])))
            formula = add(scale(chi(a, b), n2),
                          scale(int(a == 0) + int(b == 0), nq),
                          scale(F(1, 4), q2))
            assert direct == formula
            for sign in (-1, 1):
                # Nonnegative Bernstein coefficients certify r +/- m >= 0
                # for EVERY nu in [0,1], rather than only sampled values.
                assert all(x >= 0 for x in bernstein2(add(r, scale(sign, formula))))
                envelopes += 1
            if a == b == 0:
                assert direct == r
            pairs += 1

    identity_mass = 0
    for a in range(4):
        for b in range(4):
            # Each two-site noise atom is bounded by its identity atom
            # for the entire parameter interval, certifying the finite
            # point-mass vertices of the arbitrary-law convolution bound.
            difference = add(mul(law[0], law[0]), scale(-1, mul(law[a], law[b])))
            assert all(x >= 0 for x in bernstein2(difference))
            identity_mass += 1

    # A Hermitian Pauli with label (x,z) acts as i^(xz+2zt)|t xor x>.
    def pauli_action(a, t):
        x, z = a & 1, a >> 1
        return t ^ x, (x * z + 2 * z * t) % 4

    def branch_action(a, b, c, t, m):
        first, second = (a, b) if c == 0 else (b, a)
        t1, e1 = pauli_action(first, t)
        t2, e2 = pauli_action(second, t1)
        return c, t2, m, (e1 + e2) % 4

    # Every matrix unit on C,T,M is checked. This includes off-diagonal
    # C--T--M correlations; linearity then covers arbitrary entangled states.
    traced_units = 0
    states = [(c, t, m) for c in range(2) for t in range(2) for m in range(2)]
    for a in range(4):
        for b in range(4):
            k = int(chi(a, b) == -1)
            for ci, ti, mi in states:
                for cj, tj, mj in states:
                    oi = branch_action(a, b, ci, ti, mi)
                    oj = branch_action(a, b, cj, tj, mj)
                    actual = None if oi[1] != oj[1] else (
                        oi[0], oi[2], oj[0], oj[2], (oi[3] - oj[3]) % 4)
                    expected = None if ti != tj else (
                        ci, mi, cj, mj, (2 * k * (ci - cj)) % 4)
                    assert actual == expected
                    traced_units += 1

    # KL(Bern(u)||Bern(v)) <= chi-square <= 4R^2/(1-R^2).
    # Multiplication by the positive denominator gives this exact polynomial
    # certificate for the further <= (16/3)R^2 bound on 0<=R<=1/2.
    R2 = (F(0), F(0), F(1))
    denominator = (F(1), F(0), F(-1))
    lhs = add(mul(scale(F(16, 3), R2), denominator), scale(-4, R2))
    rhs = scale(F(4, 3), mul(R2, (F(1), F(0), F(-4))))
    assert lhs == rhs
    assert F(4) / (1 - F(1, 2) ** 2) == F(16, 3)
    # The RHS is (4/3)R^2(1-4R^2), nonnegative on that interval.
    return {"status": "passed",
            "local_label_pairs": pairs,
            "all_parameter_envelope_certificates": envelopes,
            "identity_mass_vertex_certificates": identity_mass,
            "entangled_input_matrix_units": traced_units,
            "kl_polynomial_certificates": 1}


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), sort_keys=True))
