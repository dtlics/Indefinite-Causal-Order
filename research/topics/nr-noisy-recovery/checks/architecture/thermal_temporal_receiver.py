"""Finite rational transcription guards for the multiarm receiver identity.

This is an abstract shared-Kraus fixture, not a thermal Fock cutoff. Its
proof input is A-T,B-T CP. Full oscillator/bath and timing claims are analytic.
"""

from fractions import Fraction as F
import json


def verify_temporal_approx():
    def require(condition, message):
        if not condition:
            raise RuntimeError(message)

    def zero(n):
        return [[F(0) for _ in range(n)] for _ in range(n)]

    def add(*matrices):
        n = len(matrices[0])
        return [[sum(matrix[i][j] for matrix in matrices)
                 for j in range(n)] for i in range(n)]

    def scale(a, scalar):
        return [[scalar * v for v in row] for row in a]

    def mul(a, b):
        n = len(a)
        return [[sum(a[i][k] * b[k][j] for k in range(n))
                 for j in range(n)] for i in range(n)]

    def transpose(a):
        return [list(row) for row in zip(*a)]

    def eye(n):
        return [[F(i == j) for j in range(n)] for i in range(n)]

    def outer_block(control, signal):
        return [[control[i // 2][j // 2] * signal[i % 2][j % 2]
                 for j in range(4)] for i in range(4)]

    def ad(k, rho):
        return mul(mul(k, rho), transpose(k))

    # Both full channels have the same Kraus K, with distinct CP residuals.
    # Rational right triangles make both trace-preserving completions exact.
    k = [[F(3, 5), F(0)], [F(0), F(5, 13)]]
    la = [[F(4, 5), F(0)], [F(0), F(12, 13)]]
    lb = [[F(0), F(12, 13)], [F(4, 5), F(0)]]
    for l in (la, lb):
        require(add(mul(transpose(k), k), mul(transpose(l), l)) == eye(2),
                "Shared-Kraus completion is not trace preserving.")

    p0 = [[F(1), F(0)], [F(0), F(0)]]
    p1 = [[F(0), F(0)], [F(0), F(1)]]
    pp = [[F(1, 2), F(1, 2)], [F(1, 2), F(1, 2)]]
    for p in (p0, p1):
        diff = add(pp, scale(p, -1))
        require(mul(diff, diff) == scale(eye(2), F(1, 2)),
                "Control difference has the wrong exact singular squares.")

    fixtures = classical_fixtures = 0
    for m in (2, 3, 4, 7):
        # P_s has all entries 1/m, hence is an orthogonal rank-one projector.
        ps = [[F(1, m) for _ in range(m)] for _ in range(m)]
        require(mul(ps, ps) == ps, "Uniform time projector failed.")
        require(sum(ps[i][i] for i in range(m)) == 1,
                "Uniform time projector trace failed.")
        for r in range(2):
            for s in range(2):
                rho = zero(2)
                rho[r][s] = F(1)
                t = ad(k, rho)
                ra, rb = ad(la, rho), ad(lb, rho)
                a, b = add(t, ra), add(t, rb)

                def literal_receiver(channel, output_reject):
                    # Direct time-block construction: diagonal A/m, cross T/m.
                    blocks = [[scale(channel if i == j else t, F(1, m))
                               for j in range(m)] for i in range(m)]
                    good = zero(2)
                    total = zero(2)
                    for i in range(m):
                        total = add(total, blocks[i][i])
                        for j in range(m):
                            good = add(good, scale(blocks[i][j], ps[j][i]))
                    other = add(total, scale(good, -1))
                    return add(outer_block(pp, good),
                               outer_block(output_reject, other))

                ordinary = scale(add(literal_receiver(a, p0),
                                     literal_receiver(b, p1)), F(1, 2))
                native = add(outer_block(pp, t),
                             scale(outer_block(p0, ra), F(1, 2)),
                             scale(outer_block(p1, rb), F(1, 2)))
                if m == 2:
                    classical = scale(add(outer_block(p0, a),
                                          outer_block(p1, b)), F(1, 2))
                    x_half = [[F(0), F(1, 2)], [F(1, 2), F(0)]]
                    require(add(native, scale(classical, -1)) ==
                            outer_block(x_half, t),
                            "Classical-order dephasing difference failed.")
                    require(sum(classical[i][i] for i in range(4)) == F(r == s),
                            "Classical-order complete channel loses probability.")
                    classical_fixtures += 1
                expected_difference = scale(add(
                    outer_block(add(pp, scale(p0, -1)), ra),
                    outer_block(add(pp, scale(p1, -1)), rb)), F(1, 2*m))
                require(add(ordinary, scale(native, -1)) == expected_difference,
                        "Literal complete receiver differs from multiarm formula.")
                expected_trace = F(r == s)
                require(sum(ordinary[i][i] for i in range(4)) == expected_trace,
                        "Ordinary complete receiver loses probability.")
                require(sum(native[i][i] for i in range(4)) == expected_trace,
                        "Native complete channel loses probability.")
                fixtures += 1

    # Full-oscillator norm location is analytic: |beta|<=1 puts the maximum
    # at n=0. These rational endpoint/sign fixtures guard its coefficients.
    thermal_norm_fixtures = 0
    thermal_points = ((F(0), F(0)), (F(0), F(1, 2)),
                      (F(1), F(0)), (F(1), F(9, 10)),
                      (F(3, 5), F(1, 2)), (F(1, 5), F(9, 10)),
                      (F(3, 5), F(3, 5)))
    for c, q in thermal_points:
        den = 1-q*c
        alpha, beta = (1-q)/den, (c-q)/den
        require(den > 0 and 0 < alpha <= 1 and -1 <= beta <= 1,
                "Thermal mean contraction failed.")
        require(1-alpha == q*(1-c)/den and
                1-beta == (1-c)*(1+q)/den and
                1+beta == (1+c)*(1-q)/den,
                "Thermal mean endpoint identities failed.")
        for c2, q2 in thermal_points:
            den2 = 1-q2*c2
            alpha2, beta2 = (1-q2)/den2, (c2-q2)/den2
            k0 = alpha*alpha2
            for n in range(9):
                kn = k0*(beta*beta2)**n
                require(abs(kn) <= k0 and (n != 0 or kn == k0),
                        "Thermal common Kraus norm is not vacuum-maximized.")
                thermal_norm_fixtures += 1

    # A tight abstract boundary: orthogonal residual outputs, zero common K.
    # Each output block of Delta squares to I/(8 m^2); summing both blocks
    # gives half trace norm 1/(sqrt(2) m), as used in the analytic bound.
    return {"status": "passed", "matrix_unit_multiarm_fixtures": fixtures,
            "matrix_unit_classical_order_fixtures": classical_fixtures,
            "thermal_mean_endpoint_sign_norm_fixtures": thermal_norm_fixtures,
            "shared_kraus_trace_preserving_completions": 2,
            "control_difference_singular_square": "1/2",
            "scope": "Exact abstract CP residual/helper receiver identities; "
                     "full oscillator, reference extension, diamond bound, "
                     "conditional payoff transfer and physical ports analytic."}


if __name__ == "__main__":
    print(json.dumps(verify_temporal_approx(), sort_keys=True))
