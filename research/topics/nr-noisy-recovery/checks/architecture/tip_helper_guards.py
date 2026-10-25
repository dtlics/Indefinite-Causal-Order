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
    return {"status": "passed", "helper_T1_rational_moments": 7,
            "data_T1_and_private_dephasing_rational_moments": True,
            "finite_held_phase_echo_operator_cases": echo_cases,
            "complete_pointer_PED_probability_guard": True,
            "scope": "Exact polynomial moments, isolated-helper utility arithmetic and finite matrix-unit echo instruments; continuum propagator, general echo and physical bath/control proofs analytic."}


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), sort_keys=True))
