"""Exact finite fixtures for a known-anchor planar measurement screen.

Not a device simulation, Haar-common-frame theorem, or native optimum.
All intrinsic filter/PBS failures are retained as parameter-independent
rejects. Extra detector, source, routing and memory losses are unmodeled.
"""
from fractions import Fraction as F
import json

if not __debug__:
    raise RuntimeError('Run exact record fixtures without -O.')

from verify_fault_simulation import (ZERO, ONE, gaussian, add, times,
                                     identity, adjoint, matmul, tensor, zeros)


def scale(a, r):
    return [[times(z, r) for z in row] for row in a]


def plus(a, b):
    return [[add(x, y) for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]


def tr(a):
    z = ZERO
    for i in range(len(a)):
        z = add(z, a[i][i])
    assert z[1] == 0
    return z[0]


def image(k, rho):
    return matmul(matmul(k, rho), adjoint(k))


def derivative_image(k, dk, rho):
    return plus(matmul(matmul(dk, rho), adjoint(k)),
                matmul(matmul(k, rho), adjoint(dk)))


def two_angle_guard():
    i = identity(2)
    z = [[ONE, ZERO], [ZERO, gaussian(-1)]]
    y = [[ZERO, gaussian(0, -1)], [gaussian(0, 1), ZERO]]
    generator = [[ZERO, gaussian(F(-1, 2))], [gaussian(F(1, 2)), ZERO]]
    rho_l = scale(plus(i, y), F(1, 2))
    rho_zero = [[ONE, ZERO], [ZERO, ZERO]]
    rotations = [(F(4, 5), F(3, 5)), (F(12, 13), F(5, 13)), (F(15, 17), F(8, 17))]
    count = 0
    for hi, ki in rotations:
        rin = [[gaussian(hi), gaussian(-ki)], [gaussian(ki), gaussian(hi)]]
        drin = matmul(generator, rin)
        ci = hi*hi-ki*ki
        for ho, ko in rotations:
            rout = [[gaussian(ho), gaussian(-ko)], [gaussian(ko), gaussian(ho)]]
            drout = matmul(generator, rout)
            co = ho*ho-ko*ko
            ordinary_f = [[F(0), F(0)], [F(0), F(0)]]
            native_p = ordinary_p = F(0)
            for b in (-1, 1):
                pb = scale(plus(i, scale(z, b)), F(1, 2))
                mb = matmul(matmul(rout, pb), adjoint(rin))
                dmb = [matmul(matmul(rout, pb), adjoint(drin)),
                       matmul(matmul(drout, pb), adjoint(rin))]
                out = scale(image(mb, rho_zero), F(1, 2))
                dout = [scale(derivative_image(mb, dm, rho_zero), F(1, 2)) for dm in dmb]
                for j in range(2):
                    prob = out[j][j][0]
                    dp = [d[j][j][0] for d in dout]
                    assert prob == (1+b*ci)*(1+b*(-1)**j*co)/8
                    ordinary_p += prob
                    for r in range(2):
                        for c in range(2):
                            ordinary_f[r][c] += dp[r]*dp[c]/prob
                for a in (-1, 1):
                    pa = scale(plus(i, scale(z, a)), F(1, 2))
                    ti, to = (1+a*b*ci)/2, (1+a*b*co)/2
                    for flag in (-1, 1):
                        k = scale(plus(matmul(mb, pa), scale(matmul(pa, mb), flag)), F(1, 4))
                        prob = tr(image(k, rho_l))
                        assert prob == (ti+to+2*flag*ti*to)/32
                        if ci == co:
                            dks = [scale(plus(matmul(dm, pa), scale(matmul(pa, dm), flag)), F(1, 4)) for dm in dmb]
                            assert tr(derivative_image(k, dks[0], rho_l)) == tr(derivative_image(k, dks[1], rho_l))
                        native_p += prob
            assert ordinary_f == [[F(1, 2), F(0)], [F(0), F(1, 2)]]
            assert (native_p, ordinary_p) == (F(1, 4), F(1, 2))
            count += 1
    return count


def check():
    i = identity(2)
    z = [[ONE, ZERO], [ZERO, gaussian(-1)]]
    x = [[ZERO, ONE], [ONE, ZERO]]
    y = [[ZERO, gaussian(0, -1)], [gaussian(0, 1), ZERO]]
    rho_l = scale(plus(i, y), F(1, 2))
    bell = zeros(4, 4)
    for r in (0, 3):
        for c in (0, 3):
            bell[r][c] = gaussian(F(1, 2))
    reports = []
    for p, q in ((3, 1), (2, 1), (3, 2), (4, 3), (1, 1)):
        c = F(p*p-q*q, p*p+q*q)
        s = F(2*p*q, p*p+q*q)
        native_p = native_dp = native_f = F(0)
        ordinary_p = ordinary_dp = ordinary_f = F(0)
        direct_p = direct_dp = direct_f = F(0)
        pointer_f = F(0)
        for a in (-1, 1):
            pa = scale(plus(i, scale(z, a)), F(1, 2))
            for b in (-1, 1):
                qb = scale(plus(i, scale(plus(scale(z, c), scale(x, s)), b)), F(1, 2))
                dqb = scale(plus(scale(z, -s), scale(x, c)), F(b, 2))
                for flag in (-1, 1):
                    k = scale(plus(matmul(qb, pa), scale(matmul(pa, qb), flag)), F(1, 4))
                    dk = scale(plus(matmul(dqb, pa), scale(matmul(pa, dqb), flag)), F(1, 4))
                    prob = tr(image(k, rho_l))
                    dp = tr(derivative_image(k, dk, rho_l))
                    t = (1+a*b*c)/2
                    assert prob == (t+flag*t*t)/16
                    native_p += prob
                    native_dp += dp
                    native_f += dp*dp/prob
        for b in (-1, 1):
            qb = scale(plus(i, scale(plus(scale(z, c), scale(x, s)), b)), F(1, 2))
            dqb = scale(plus(scale(z, -s), scale(x, c)), F(b, 2))
            k, dk = tensor(qb, i), tensor(dqb, i)
            out = scale(image(k, bell), F(1, 2))  # PBS success factor.
            dout = scale(derivative_image(k, dk, bell), F(1, 2))
            for j in range(4):
                prob, dp = out[j][j][0], dout[j][j][0]
                ordinary_p += prob
                ordinary_dp += dp
                if prob:
                    ordinary_f += dp*dp/prob
            # A simpler ordinary probe uses |0>, its known preparation
            # record, Bob's b, and the final target Z readout only.
            rho_zero = [[ONE, ZERO], [ZERO, ZERO]]
            direct = scale(image(qb, rho_zero), F(1, 2))
            ddirect = scale(derivative_image(qb, dqb, rho_zero), F(1, 2))
            pointer_prob, pointer_dp = tr(direct), tr(ddirect)
            assert pointer_prob == (1+b*c)/4
            pointer_f += pointer_dp*pointer_dp/pointer_prob
            for j in range(2):
                prob, dp = direct[j][j][0], ddirect[j][j][0]
                assert prob == (1+b*c)*(1+b*(-1)**j*c)/8
                direct_p += prob
                direct_dp += dp
                if prob:
                    direct_f += dp*dp/prob
        assert (native_p, native_dp) == (F(1, 4), F(0))
        assert (ordinary_p, ordinary_dp) == (F(1, 2), F(0))
        assert (direct_p, direct_dp) == (F(1, 2), F(0))
        assert native_f == 3/(9-c*c)
        assert ordinary_f == 1
        assert direct_f == 1
        assert pointer_f == F(1, 2)
        assert native_f <= F(3, 8)
        reports.append({'cos_Bloch_angle': str(c), 'sin_Bloch_angle': str(s),
                        'native_record_FI_per_pair': str(native_f),
                        'ordinary_Bell_record_FI_per_pair': str(ordinary_f),
                        'ordinary_direct_record_FI_per_pair': str(direct_f),
                        'ordinary_pointer_only_FI_per_pair': str(pointer_f)})
    return {'status': 'passed', 'cases': reports,
            'two_angle_swap_and_ordinary_Fisher_matrix_cases': two_angle_guard(),
            'scope': 'Exact finite known-anchor planar ideal PBS/filter fixtures; no apparatus throughput, full native optimum, Haar-unknown-frame or general physical-instrument certificate.'}


if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
