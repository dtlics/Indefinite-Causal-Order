"""Exact polynomial and finite-instrument guards for the TIP helper note.

Standard library only. This does not propagate the 72/144-dimensional
Hamiltonian, fit a bath, or optimize an ordinary control policy.
"""
from fractions import Fraction as F
from math import comb

if not __debug__:
    raise RuntimeError("Run exact TIP guards without -O.")


def mul(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def avg(a):
    # f=cos^2(x/2), uniform x in [0,pi].
    return sum(c * F(comb(2 * n, n), 4 ** n) for n, c in enumerate(a))


def add(a, b):
    return [(a[n] if n < len(a) else F(0))
            + (b[n] if n < len(b) else F(0))
            for n in range(max(len(a), len(b)))]


def echo_instrument_guard():
    from verify_fault_simulation import (ZERO, ONE, gaussian, conjugate,
                                         identity, matmul, tensor, zeros)
    # Helper first, one data qubit. All data matrix units span every K.
    tag = identity(4)
    tag[3][3] = gaussian(-1)
    x = tensor([[ZERO, ONE], [ONE, ZERO]], identity(2))
    zb = tensor(identity(2), [[ONE, ZERO], [ZERO, gaussian(-1)]])
    units = []
    for i in range(2):
        for j in range(2):
            k = zeros(2, 2)
            k[i][j] = ONE
            units.append(tensor(identity(2), k))
    count = 0
    for phase in (ONE, gaussian(F(3, 5), F(4, 5)), gaussian(F(5, 13), F(-12, 13))):
        dephase = tensor([[phase, ZERO], [ZERO, conjugate(phase)]], identity(2))
        for k1 in units:
            for k2 in units:
                # Z_B C R K2 X_D R K1 C = X_D C K2 K1 C.
                actual = identity(4)
                for factor in (zb, tag, dephase, k2, x, dephase, k1, tag):
                    actual = matmul(actual, factor)
                expected = identity(4)
                for factor in (x, tag, k2, k1, tag):
                    expected = matmul(expected, factor)
                assert actual == expected
                count += 1
    return count


def recovery_and_prefix_guards():
    # Q1 is an illustrative copied/exponential-white model, not a fitted bath.
    gamma, ramsey = F(50, 3849), F(20, 1013)
    big_gamma = ramsey - gamma / 2
    s, d, odd = big_gamma + gamma / 2, big_gamma - gamma / 2, F(1, 128)
    assert s == F(20, 1013) and d == F(20, 1013) - F(50, 3849)
    assert 0 < d < 2 * odd and d < odd
    a, b = d / (2 * odd), F(1)
    p = s * (a * a + b * b) / 2 + odd * a * a
    q = (s * (a * a + b * b) + 2 * d * a * b) / 4
    assert 2 * q - p == d * d / (4 * odd) > 0
    # Identity/Pauli at lambda=1 loses, whereas a physical partial filter wins.
    assert d - odd < 0
    # Lambda=5 diagonal filter quadratic is negative definite, exactly.
    assert s > 0 and s + 5 * odd > 0
    assert s * (s + 5 * odd) - 9 * d * d / 4 > 0
    # Broad weak boundary-tag bound: helper good loss >= mandatory bad.
    # All rate copies and white laws are declared hypotheses of this example.
    ga, gb, gc = F(1, 168), F(1, 80), F(1, 168)
    phi_sum = 2 * (F(1, 26) - F(1, 64))
    gn = ga + 5 * gb / 8 + gc + F(165, 512) * phi_sum + F(6297, 8192) * gamma + big_gamma
    bn = F(183, 256) * (ga + gc) + F(15, 32) * gb + F(27, 512) * phi_sum + F(1097, 8192) * gamma
    gbare = ga + 5 * gb / 8 + gc + F(69, 256) * phi_sum
    bbare = F(119, 128) * (ga + gc) + F(5, 8) * gb + F(27, 256) * phi_sum
    native_vs_bare = gbare + 5 * bbare - gn - 5 * bn
    weak_vs_bare_bound = max(F(0), 5 * odd - 6 * gamma / 2)
    assert big_gamma >= gamma / 2
    assert native_vs_bare == F(373165517, 1453311455232)
    assert weak_vs_bare_bound == F(15, 164224)
    margin = native_vs_bare - weak_vs_bare_bound
    assert margin == F(240421997, 1453311455232) > 0

    # Common-pump paired-sector difference, in units with 2*pi removed.
    from verify_fault_simulation import (ZERO, gaussian, add as gadd,
                                         times, zeros)
    pump_cases = ((gaussian(0), gaussian(0)),
                  (gaussian(F(3, 2), F(4, 5)), gaussian(-2, F(1, 3))),
                  (gaussian(F(-5, 4), F(12, 7)), gaussian(F(2, 3), -1)))
    f, chi, cap = F(10), F(929, 100), F(9)
    epsilon = abs(chi - f)
    for gu, gv in pump_cases:
        hs = []
        for diagonal in ((0, -f / 2, -f / 2), (chi, f / 2, f / 2)):
            h = zeros(3, 3)
            for i, value in enumerate(diagonal):
                h[i][i] = gaussian(value)
            h[0][1], h[0][2] = times(gu, F(1, 2)), times(gv, F(1, 2))
            h[1][0] = (h[0][1][0], -h[0][1][1])
            h[2][0] = (h[0][2][0], -h[0][2][1])
            hs.append(h)
        for i in range(3):
            for j in range(3):
                expected = gaussian(chi if i == 0 else f) if i == j else ZERO
                assert gadd(hs[1][i][j], times(hs[0][i][j], -1)) == expected
    low, high = 1 / (2 * (f + epsilon)), 1 / (2 * (f - epsilon))
    next_low = 3 / (2 * (f + epsilon))
    assert (low, high, next_low) == (F(50, 1071), F(50, 929), F(50, 357))
    assert epsilon * next_low < F(1, 2)  # epsilon_angle*h < pi below this point
    # Start/end leaf return bounds integral |u| by G*h^2/4.
    # Exact CZ needs pi <= Delta*G*h^2/4; pi < 22/7 excludes first band.
    assert F(22, 7) * f * cap * high * high / 2 < 1
    assert next_low > F(1, 10)
    return {"partial_filter_gain_per_T_us": str(d * d / (4 * odd)),
            "lambda5_ordinary_flag_negative_definite": True,
            "lambda5_native_minus_weak_tag_bound_per_T_us": str(margin),
            "paired_sector_common_pump_fixtures": len(pump_cases),
            "first_phase_band_us": [str(low), str(high)],
            "exact_prefix_lower_us": str(next_low),
            "scope": "Exact rational recovery quadratic, finite sector differences and first-band arithmetic; symmetry/CP reductions and continuous speed/return bounds analytic. No full-device or arbitrary-control timing claim."}


def retained_body_and_idle_guards():
    # Model-only coefficient, padding and clock arithmetic; no propagation.
    t0, chi_over_pi, delta_over_pi = F(1, 10), F(929, 50), F(10)
    n = 22
    coefficient = chi_over_pi * delta_over_pi * (4*delta_over_pi+chi_over_pi) * t0**3 / 128
    assert coefficient == F(2721041, 32000000)
    upper = coefficient * F(7, 4) * F(22, 7)**3 / n**2
    assert upper == F(7243411142, 758912000000) < F(1, 100)
    assert 3 / chi_over_pi == F(150, 929) < 2*t0
    flips, pieces = 4*n, 12*n
    clock = 2*t0 + flips*(2*t0)
    assert (flips, pieces, clock) == (88, 264, F(89, 5))
    # A decoupled post-W dephasing idle mixes both physical X records.
    # Rational visibilities are fixtures, not fitted finite-time exponentials.
    idle_cases = 0
    for visibility in (F(0), F(3, 5), F(4, 5), F(1)):
        q = (1-visibility)/2
        assert 0 <= q <= F(1, 2)
        for plus, minus in ((F(1), F(0)), (F(2, 5), F(1, 5)), (F(0), F(3, 7))):
            out_plus = (1-q)*plus+q*minus
            out_minus = (1-q)*minus+q*plus
            assert out_plus+out_minus == plus+minus
            assert out_plus-plus == q*(minus-plus)
            idle_cases += 1
    return {"finite_body_coefficient": str(coefficient)+"*sqrt(3)*pi^3/N^2",
            "N22_operator_error_rational_upper": str(upper),
            "positive_padding_duration_bound_us": str(3/chi_over_pi),
            "finite_helper_flips": flips, "helper_drive_pieces": pieces,
            "closed_model_clock_us": str(clock), "full_flag_idle_mixing_cases": idle_cases,
            "scope": "Exact sufficient-bound/padding/clock and post-idle coefficient fixtures. Finite pulse, Strang defect, reference norm and full CP mixing identities are analytic; no competitive waveform, noise instrument or hardware certificate."}


def verify():
    r = [F(1), F(-3), F(3)]
    pf = [F(0), F(3), F(-3)]
    eta = [F(0), F(0), F(0), F(1)]
    returned_control = [F(1), F(0), F(-12), F(24), F(-12)]
    assert avg(r) == F(5, 8)
    assert avg(returned_control) == F(23, 32)
    assert (F(5, 8) + avg(returned_control) / 8,
            (1 + avg(returned_control)) / 8,
            F(1, 2) + (1 + avg(returned_control)) / 4) == (F(183, 256), F(55, 256), F(119, 128))
    assert 1 - F(183 + 55, 256) == F(9, 128)
    assert (F(3, 4) * avg(r), avg(r) / 4) == (F(15, 32), F(5, 32))
    total_phi, phi_p = avg(pf), avg(mul(pf, pf))
    phi_q = phi_p / 2
    assert (total_phi, phi_p, phi_q) == (F(3, 8), F(27, 128), F(27, 256))
    assert (total_phi - phi_q, phi_q, total_phi - phi_p) == (F(69, 256), F(27, 256), F(21, 128))
    assert (total_phi - phi_q / 2, phi_q / 2, total_phi - phi_p / 2) == (F(165, 512), F(27, 512), F(69, 256))
    assert avg(mul(r, r)) == F(59, 128)
    assert avg(eta) == F(5, 16)
    assert avg(mul(eta, eta)) == F(231, 1024)
    pgg = (1 + avg(mul(r, r))) / 4
    qgg = (1 + 2 * avg(eta) + avg(mul(eta, eta))) / 8
    leak_each = avg(mul(pf, add([F(1)], r))) / 8
    assert (pgg, qgg, leak_each) == (F(187, 512), F(1895, 8192), F(69, 1024))
    assert pgg + 2 * leak_each == F(1, 2)
    assert (1 - qgg, pgg - qgg, 1 - pgg) == (F(6297, 8192), F(1097, 8192), F(325, 512))
    # Both pointers kept, PED still required; all rejects are charged.
    assert (1 - 2 * qgg, 2 * (pgg - qgg), 1 - 2 * pgg) == (F(2201, 4096), F(1097, 4096), F(69, 256))
    # Ordinary physical helper encodings, isolated T1 and ideal completion W.
    ordinary_reject = (F(1), F(0), F(1))
    ordinary_keep = (F(1, 2), F(1, 2), F(0))
    for lam in (F(0), F(1, 2), F(1), F(2), F(10)):
        native_loss = 1 - qgg + lam * (pgg - qgg)
        assert ordinary_reject[0] + lam * ordinary_reject[1] - native_loss == (1895 - 1097 * lam) / 8192
        assert ordinary_keep[0] + lam * ordinary_keep[1] - native_loss == (-2201 + 2999 * lam) / 8192
    echo_cases = echo_instrument_guard()
    from tip_common_rotation_guards import verify as verify_common_rotations
    return {"status": "passed", "helper_T1_rational_moments": 7,
            "data_T1_and_private_dephasing_rational_moments": True,
            "finite_held_phase_echo_operator_cases": echo_cases,
            "complete_pointer_PED_probability_guard": True,
            "recovery_and_prefix_ingredients": recovery_and_prefix_guards(),
            "common_helper_rotation_ingredients": verify_common_rotations(),
            "retained_body_and_idle_ingredients": retained_body_and_idle_guards(),
            "scope": "Exact moments, recovery/rotation fine-map and utility, matrix-unit echo, prefix-band, finite-body bound/clock and full-flag idle ingredients; continuous dynamics, speed and operator-norm proofs, CP reductions and physical bath/control premises analytic."}


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), sort_keys=True))
