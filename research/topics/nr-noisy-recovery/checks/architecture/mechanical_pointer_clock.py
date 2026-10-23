"""Finite transcription checks for NR-R08 mechanical-pointer clock identities.

Proof: architecture-baselines.md#nr-r08-mechanical-clock.
The infinite-mode Weyl/thermal and instrument arguments remain analytic.
This stdlib replay checks exact finite passive-dilation Gram identities and
control counterexamples; scalar exponentials are additional numerical guards.
"""

if not __debug__:
    raise RuntimeError("Run without -O: verification requires assertions")

from fractions import Fraction as F
import cmath
import json
import math


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def neg(a):
    return (-a[0], -a[1])


def sub(a, b):
    return add(a, neg(b))


def mul(a, b):
    return (a[0] * b[0] - a[1] * b[1],
            a[0] * b[1] + a[1] * b[0])


def conj(a):
    return (a[0], -a[1])


def power(a, n):
    z = (F(1), F(0))
    for _ in range(n):
        z = mul(z, a)
    return z


def dot(a, b):
    z = (F(0), F(0))
    for x, y in zip(a, b):
        z = add(z, mul(conj(x), y))
    return z


def norm2(v):
    z = dot(v, v)
    assert z[1] == 0
    return z[0]


def vector_sub(a, b):
    return [sub(x, y) for x, y in zip(a, b)]


def dilation_vector(t, h, g, steps):
    """Conjugated annihilator coefficients; no final emitted mode discarded."""
    zero = (F(0), F(0))
    result = [power(h, t)] + [zero] * steps
    for k in range(t):
        result[1 + k] = mul((g, F(0)), power(h, t - 1 - k))
    return result


def weyl_product(vectors):
    """D(v)D(w)=exp[-i Im(v†w)]D(v+w), exact exponent coefficient."""
    total = [(F(0), F(0))] * len(vectors[0])
    phase = F(0)
    for v in vectors:
        phase -= dot(total, v)[1]
        total = [add(x, y) for x, y in zip(total, v)]
    return phase, total


def real_zero(d):
    return [[F(0) for _ in range(d)] for _ in range(d)]


def real_mul(a, b):
    d = len(a)
    out = real_zero(d)
    for i in range(d):
        for k in range(d):
            if a[i][k]:
                for j in range(d):
                    if b[k][j]:
                        out[i][j] += a[i][k] * b[k][j]
    return out


def real_projectors(d, mub):
    if not mub:
        return [[[F(i == j == label) for j in range(d)] for i in range(d)]
                for label in range(d)]
    return [[[F((-1) ** ((label & i).bit_count()
                         + (label & j).bit_count()), d)
              for j in range(d)] for i in range(d)] for label in range(d)]


def verify_fixed_input_task():
    # Every isotropic K is a linear combination of J and I. Checking their
    # four tensor combinations certifies all kernel coefficients here by
    # bilinearity, including complex coefficient substitutions in the proof.
    full_target_coefficients = 0
    for d in (2, 4):
        ps = real_projectors(d, False)
        for mub in (False, True):
            qs = real_projectors(d, mub)
            v = F(1, d) if mub else F(1)
            for qa, ka in ((F(1), F(1)), (F(0), F(1))):
                for qb, kb in ((F(1), F(1)), (F(0), F(1))):
                    actual = real_zero(d)
                    for i in range(d):
                        for k in range(d):
                            ca = ka if i == k else qa
                            if not ca:
                                continue
                            for j in range(d):
                                left = real_mul(qs[j], ps[i])
                                for l in range(d):
                                    cb = kb if j == l else qb
                                    if not cb:
                                        continue
                                    term = real_mul(left, real_mul(qs[l], ps[k]))
                                    for x in range(d):
                                        for y in range(d):
                                            actual[x][y] += ca * cb * term[x][y] / d
                    c = qa * kb + ka * qb - qa * qb + v * (ka - qa) * (kb - qb)
                    assert actual == [[F(x == y) * c / d
                                       for y in range(d)] for x in range(d)]
                    full_target_coefficients += 1

    # Actual closed Gaussian cases at angle zero and pi have k=1 and q**2.
    # Check complete classical channels, not only their contrast.
    exact_garbling_rows = 0
    for q in (F(1, 5), F(1, 2), F(9, 10)):
        for d in (2, 3, 5):
            g = 1 - F(1, d)
            p = 1 - q
            t = g * p * p / 2
            for k in (F(1), q * q):
                b = (1 - k * k) / 2
                h2 = (k - q) ** 2 / (p * p)
                assert 0 <= b <= 1 and 0 <= b + h2 <= 1
                assert b * (1 - t) + (b + h2) * t == b + g * (k - q) ** 2 / 2
                exact_garbling_rows += 1
    return full_target_coefficients, exact_garbling_rows


def verify_mechanical_pointer_clock():
    steps = 6
    h = (F(0), F(3, 5))
    g = F(4, 5)
    assert norm2([h]) + g * g == 1
    vectors = [dilation_vector(t, h, g, steps) for t in range(steps + 1)]
    for v in vectors:
        assert norm2(v) == 1
    exact_pairs = 0
    covariance_splits = 0
    force_guards = 0
    beta = [(F(k + 1, 13), F(2 * k - 1, 17))
            for k in range(steps + 1)]
    for s in range(steps + 1):
        for t in range(s, steps + 1):
            inner = power(h, t - s)
            assert dot(vectors[s], vectors[t]) == inner
            difference = vector_sub(vectors[t], vectors[s])
            total = 2 - 2 * inner[0]
            assert norm2(difference) == total
            exact_pairs += 1
            initial = norm2([difference[0]])
            atten_s = power(h, s)
            atten_delta = power(h, t - s)
            expected_initial = (norm2([atten_s])
                                * (1 + norm2([atten_delta])
                                   - 2 * atten_delta[0]))
            assert initial == expected_initial
            field = norm2(difference[1:])
            assert initial + field == total
            assert field >= 0
            for n_m, n_b in ((F(0), F(0)), (F(3), F(3)),
                             (F(5), F(0)), (F(0), F(7))):
                exponent_direct = ((n_m + F(1, 2)) * initial
                                   + (n_b + F(1, 2)) * field)
                exponent_split = ((n_b + F(1, 2)) * total
                                  + (n_m - n_b) * initial)
                assert exponent_direct == exponent_split
                assert exponent_direct >= 0
                covariance_splits += 1
            shifted_t = [add(x, y) for x, y in zip(vectors[t], beta)]
            shifted_s = [add(x, y) for x, y in zip(vectors[s], beta)]
            assert vector_sub(shifted_t, shifted_s) == difference
            force_guards += 1

    # Orthogonal material-cell labels keep complete norm difference two.
    label_guards = 0
    z = [(F(0), F(0))] * (steps + 1)
    for v in vectors:
        for w in vectors:
            vi, wk = v + z, z + w
            assert dot(vi, wk) == (F(0), F(0))
            assert norm2(vector_sub(vi, wk)) == 2
            label_guards += 1

    # Closed oscillator returns after four quarter turns; damped full records
    # do not, although a mechanical phase alone has returned.
    unit_h = (F(0), F(1))
    closed0 = dilation_vector(0, unit_h, F(0), steps)
    closed4 = dilation_vector(4, unit_h, F(0), steps)
    damped0, damped4 = vectors[0], vectors[4]
    assert closed0 == closed4
    assert norm2(vector_sub(damped4, damped0)) == 2 * (1 - F(3, 5) ** 4)
    assert norm2(vector_sub(damped4, damped0)) > 0
    assert norm2(vector_sub(damped4[1:], damped0[1:])) > 0

    # Bosonic parity commutes with N. Its midpoint sequence leaves R(2tau),
    # rather than reversing the harmonic idle Hamiltonian.
    parity_guards = 0
    for number in range(5):
        parity = F((-1) ** number)
        idle = power((F(0), F(-1)), number)
        observed = mul(mul(mul((parity, F(0)), idle),
                           (parity, F(0))), idle)
        assert observed == power(idle, 2)
        if number % 2:
            assert observed != (F(1), F(0))
        parity_guards += 1

    # The all-input force-loop identity has zero final record displacement
    # on every photon label and the correct controllable scalar phase.
    # No finite Fock truncation or initial pointer state is invoked.
    force_loop_branches = 0
    force_loop_phase_programs = 0
    alpha = (F(1, 3), F(1, 5))
    A = norm2([alpha])
    for dimension in (2, 3, 5):
        betas = [(F(j - 1, 7), F(2 * j + 1, 11))
                 for j in range(dimension)]
        for label in range(dimension):
            a = [(F(0), F(0))] * dimension
            a[label] = alpha
            phase, final = weyl_product([
                [neg(z) for z in a], betas, a,
                [neg(z) for z in betas]])
            assert final == [(F(0), F(0))] * dimension
            assert phase == 2 * mul(conj(alpha), betas[label])[1]
            force_loop_branches += 1
        # beta=i theta alpha/(2A) gives precisely the chosen exponent theta.
        for theta in (F(-7, 3), F(0), F(5, 2)):
            beta = mul((F(0), theta / (2 * A)), alpha)
            phase, final = weyl_product([
                [neg(alpha)], [beta], [alpha], [neg(beta)]])
            assert final == [(F(0), F(0))]
            assert phase == theta
            force_loop_phase_programs += 1

    # Complex phases and equilibrium/non-equilibrium thermal exponents.
    # These floating-point identities guard the analytic Weyl formula;
    # they are not finite-Fock substitutes for its proof.
    numerical_guards = 0
    numerical_gaussian_garbling_guards = 0
    for amplitude in (0.01, 0.3, 2.0):
        for n in (0.0, 0.7, 5.0):
            for delta in (0.0, 0.2, 1.1, math.pi, 2 * math.pi):
                a = amplitude * cmath.exp(1j * delta)
                b = complex(amplitude)
                k_direct = cmath.exp(1j * (b.conjugate() * a).imag
                                    - (n + 0.5) * abs(a - b) ** 2)
                A = amplitude ** 2
                k_formula = cmath.exp(1j * A * math.sin(delta)
                                     - (2 * n + 1) * A * (1 - math.cos(delta)))
                assert abs(k_direct - k_formula) < 2e-14
                eta2 = 2 - 2 * k_formula.real
                assert -1e-14 <= eta2 <= 4 + 1e-14
                # This is a fidelity of mechanical states, not the trace
                # characteristic function involving thermal purification.
                mechanical_root_fidelity = math.exp(-A / (2 * n + 1))
                assert 0 < mechanical_root_fidelity <= 1
                numerical_guards += 1

                q = math.exp(-(2 * n + 1) * A)
                p = -math.expm1(-(2 * n + 1) * A)
                for response_amplitude in (0.0, 0.6, 1.0):
                    response = response_amplitude * cmath.exp(1j * delta)
                    k = cmath.exp(1j * A * response.imag
                                  - (2 * n + 1) * A * (1 - response.real))
                    assert abs(k - q) <= p + 2e-14
                    assert 2 * abs(k - q) ** 2 <= p * p * (1 + abs(k) ** 2) + 2e-14
                    numerical_gaussian_garbling_guards += 1

    full_target_coefficients, exact_garbling_rows = verify_fixed_input_task()

    return {
        "exact_passive_dilation_pairs": exact_pairs,
        "exact_thermal_covariance_splits": covariance_splits,
        "exact_common_force_difference_guards": force_guards,
        "exact_distinct_cell_norm_guards": label_guards,
        "exact_parity_non_echo_guards": parity_guards,
        "exact_force_loop_label_branches": force_loop_branches,
        "exact_force_loop_phase_programs": force_loop_phase_programs,
        "closed_recurrence_and_damped_field_counterexample": True,
        "numerical_closed_weyl_guards": numerical_guards,
        "exact_fixed_input_full_target_kernel_coefficients": full_target_coefficients,
        "exact_gaussian_endpoint_garbling_rows": exact_garbling_rows,
        "numerical_gaussian_garbling_guards": numerical_gaussian_garbling_guards,
        "scope": ("finite exact passive-dilation, Weyl-loop and fixed-input kernel identities; "
                  "Gaussian exponentials are numerical guards; infinite Weyl/thermal, "
                  "garbling inequality, Chernoff, timing and physical claims analytic"),
    }


if __name__ == "__main__":
    print(json.dumps(verify_mechanical_pointer_clock(), sort_keys=True))
