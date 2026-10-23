"""Exact algebra for communication.md#nr-r11-rydberg-exchange.

This checks the scoped record models, not an experimental implementation.
Only the Python standard library is required.
"""

if not __debug__:
    raise RuntimeError("Exact verification requires assertions enabled.")

from fractions import Fraction as F
import json


def q(a=0, b=0):
    return (F(a), F(b))


ZERO = q()


def add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def mul(x, y):
    return (x[0] * y[0] - x[1] * y[1],
            x[0] * y[1] + x[1] * y[0])


def conj(x):
    return (x[0], -x[1])


def scale(x, a):
    return (x[0] * a, x[1] * a)


def dot(x, y):
    result = ZERO
    for a, b in zip(x, y):
        result = add(result, mul(conj(a), b))
    return result


def norm(x):
    result = dot(x, x)
    assert result[1] == 0
    return result[0]


def outer(x, y):
    return mul(x, conj(y))


def density(state):
    """Trace all K,E records; keep memory A/B. State is an unnormalized ket."""
    result = [[ZERO for _ in range(2)] for _ in range(2)]
    records = {record for memory, record in state}
    for record in records:
        for row in range(2):
            for col in range(2):
                result[row][col] = add(result[row][col], outer(
                    state.get((row, record), ZERO),
                    state.get((col, record), ZERO)))
    return result


def eraser(tau, eta, alpha=F(1), beta=F(1)):
    """Both BS outcomes plus memory Z frame; omit sqrt2 and weight density 1/2."""
    result = [[ZERO for _ in range(2)] for _ in range(2)]
    for sign in (1, -1):
        state = {}
        for record, (t, h) in enumerate(zip(tau, eta)):
            state[(0, record)] = scale(t, alpha)
            # Detector sign and feedforward sign are separately present.
            state[(1, record)] = scale(h, beta * sign * sign)
        branch = density(state)
        for row in range(2):
            for col in range(2):
                result[row][col] = add(result[row][col],
                                       scale(branch[row][col], F(1, 2)))
    return result


def verify_exchange_eraser():
    models = [
        ([q(F(3, 5)), ZERO, ZERO, ZERO],
         [q(F(8, 25)), q(F(6, 25)), ZERO, ZERO]),
        ([q(F(3, 5)), ZERO, ZERO, ZERO],
         [ZERO, q(F(2, 5)), ZERO, ZERO]),
        ([q(F(1, 5), F(1, 5)), q(F(2, 5)), ZERO, ZERO],
         [q(0, F(1, 5)), q(F(1, 5)), q(F(1, 5)), ZERO]),
        ([q(F(1, 4)), q(0, F(1, 4)), q(F(1, 4)), ZERO],
         [q(0, F(1, 4)), q(F(1, 4)), ZERO, q(F(1, 4))]),
    ]
    flags = coefficients = attenuation = 0
    for tau, eta in models:
        a, b, c = norm(tau), norm(eta), dot(eta, tau)
        assert a + b <= 1
        assert norm([c]) <= a * b  # Cauchy-Schwarz, exact complex records.
        for alpha, beta in ((F(1), F(1)), (F(2, 3), F(1)),
                            (F(1), F(3, 4))):
            got = eraser(tau, eta, alpha, beta)
            wanted = [[q(alpha * alpha * a), scale(c, alpha * beta)],
                      [scale(conj(c), alpha * beta), q(beta * beta * b)]]
            assert got == wanted
            coefficients += 4
            flags += 2
            # Rejected optical attenuation ports plus successful flags complete
            # the full pre-attenuation survival probability.
            rejected = (1 - alpha * alpha) * a + (1 - beta * beta) * b
            assert got[0][0][0] + got[1][1][0] + rejected == a + b
            attenuation += 1

    # Two models have identical complete rail populations and total loss but
    # different inaccessible-record coherence. Both detector flags are kept.
    tau0, eta0 = models[0]
    tau1, eta1 = models[1]
    assert norm(tau0) == norm(tau1) == F(9, 25)
    assert norm(eta0) == norm(eta1) == F(4, 25)
    assert 1 - norm(tau0) - norm(eta0) == F(12, 25)
    balanced = eraser(tau0, eta0, F(2, 3), F(1))
    incoherent = eraser(tau1, eta1, F(2, 3), F(1))
    assert balanced == [[q(F(4, 25)), q(F(16, 125))],
                        [q(F(16, 125)), q(F(4, 25))]]
    assert incoherent == [[q(F(4, 25)), ZERO], [ZERO, q(F(4, 25))]]
    code_yield = F(8, 25)
    bell_numerator = (balanced[0][0][0] + balanced[1][1][0]
                      + balanced[0][1][0] + balanced[1][0][0]) / 2
    assert bell_numerator / code_yield == F(9, 10)
    assert bell_numerator / (code_yield + F(1, 25)) == F(4, 5)
    assert F(1, 2) + incoherent[0][1][0] / code_yield == F(1, 2)

    # The same false-herald fidelity formula allows coherent vacuum/code
    # cross terms. This positive 3x3 state is a sum of exact outer products.
    full = [[F(0) for _ in range(3)] for _ in range(3)]
    for vector in ((F(1, 5), F(2, 5), F(8, 25)),
                   (F(0), F(0), F(6, 25))):
        for row in range(3):
            for col in range(3):
                full[row][col] += vector[row] * vector[col]
    assert full[0][1] != 0 and full[0][2] != 0
    assert sum(full[j][j] for j in range(3)) == F(9, 25)
    assert (full[1][1] + full[1][2] + full[2][1] + full[2][2]) / 2 == bell_numerator

    # Full three-exit open feedback network, including first loss and loss only
    # after the first successful hop. No hidden deterministic second query.
    feedback_checks = 0
    for t1, h1, l1 in ((q(F(1, 2)), q(0, F(1, 2)), F(1, 2)),
                        (q(F(3, 5)), q(0, F(4, 5)), F(0)),
                        (q(F(2, 5)), q(0, F(1, 5)), F(4, 5))):
        assert norm([t1, h1]) + l1 == 1
        for t2, h2, l2 in ((q(F(3, 5)), q(0, F(4, 5)), F(0)),
                            (q(F(1, 2)), q(0, F(1, 2)), F(1, 2))):
            assert norm([t2, h2]) + l2 == 1
            early_b, late_c, late_b = t1, mul(t2, h1), mul(h2, h1)
            assert norm([early_b, late_c, late_b]) + l1 + norm([h1]) * l2 == 1
            assert norm([late_b]) == norm([h1]) * norm([h2])
            assert norm([late_b]) <= norm([h1])
            feedback_checks += 1

    # Explicit EB location instrument, with a retained classical record:
    # matrix units |j><j'| map to zero when j != j'. All basis populations
    # match a nontrivial rational stochastic hopping matrix.
    p = [[F(1, 2), F(1, 4), F(1, 4)],
         [F(1, 3), F(1, 3), F(1, 3)],
         [F(1, 5), F(2, 5), F(2, 5)]]
    population_coefficients = 0
    for source in range(3):
        assert sum(p[source]) == 1
    for left in range(3):
        for right in range(3):
            for out_left in range(3):
                for out_right in range(3):
                    # Full sum L_{kj}|left><right|L_{kj}^dagger;
                    # different environment labels never interfere.
                    got = sum(p[source][target]
                              for source in range(3) for target in range(3)
                              if left == source == right
                              and out_left == target == out_right)
                    wanted = (p[left][out_left]
                              if left == right and out_left == out_right else F(0))
                    assert got == wanted
                    population_coefficients += 1

    # Formal common-exchange-parity algebra. A key is(F parity, four
    # independent coefficient exponents). This checks arbitrary scalars
    # on each invariant coordinate orbit, rather than a numeric grid.
    def product(left, right):
        result = {}
        for (lp, le), lc in left.items():
            for (rp, re), rc in right.items():
                key = (lp ^ rp, tuple(x + y for x, y in zip(le, re)))
                result[key] = result.get(key, F(0)) + lc * rc
        return {key: value for key, value in result.items() if value}

    ka = {(0, (1, 0, 0, 0)): F(1), (1, (0, 1, 0, 0)): F(1)}
    kb = {(0, (0, 0, 1, 0)): F(1), (1, (0, 0, 0, 1)): F(1)}
    normal = {(0, (1, 0, 1, 0)): F(1), (0, (0, 1, 0, 1)): F(1),
              (1, (1, 0, 0, 1)): F(1), (1, (0, 1, 1, 0)): F(1)}
    assert product(ka, kb) == product(kb, ka) == normal

    return {"full_record_models": len(models), "both_detector_flags": flags,
            "memory_density_coefficients": coefficients,
            "rejected_attenuator_completions": attenuation,
            "open_feedback_completions": feedback_checks,
            "classical_location_coefficients": population_coefficients,
            "balanced_false_herald_cases": 4,
            "formal_common_parity_monomials": len(normal)}


if __name__ == "__main__":
    print(json.dumps(verify_exchange_eraser(), sort_keys=True))
