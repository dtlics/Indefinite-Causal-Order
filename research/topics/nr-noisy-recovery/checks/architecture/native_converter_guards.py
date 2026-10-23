"""Exact finite NR-R19 passive-scattering and equal-power BS-FWM guards.

Standard-library Gaussian-rational arithmetic only. SC1--SC4 and BF1--BF2
are proved analytically in backaction.md. This replay checks finite
examples, not their universal quantifiers, a physical device fit, a full
noise model, or an ordinary-receiver lower bound. No files are generated.
"""
from fractions import Fraction as F
import json

if not __debug__:
    raise RuntimeError("Run exact converter guards without -O.")


def q(real=0, imag=0):
    return (F(real), F(imag))


ZERO, ONE, I = q(), q(1), q(0, 1)


def add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def neg(x):
    return (-x[0], -x[1])


def mul(x, y):
    return (x[0]*y[0] - x[1]*y[1], x[0]*y[1] + x[1]*y[0])


def conj(x):
    return (x[0], -x[1])


def inverse_scalar(x):
    n = x[0]*x[0] + x[1]*x[1]
    if not n:
        raise ZeroDivisionError("Singular Gaussian-rational scalar.")
    return (x[0]/n, -x[1]/n)


def norm2(x):
    return x[0]*x[0] + x[1]*x[1]


def eye(n):
    return [[q(int(j == k)) for k in range(n)] for j in range(n)]


def zeros(n):
    return [[ZERO for _ in range(n)] for _ in range(n)]


def diag(xs):
    return [[x if j == k else ZERO for k in range(len(xs))]
            for j, x in enumerate(xs)]


def dag(a):
    return [[conj(x) for x in row] for row in zip(*a)]


def mm(a, b):
    return [[sumq(mul(x, y) for x, y in zip(row, col))
             for col in zip(*b)] for row in a]


def sumq(xs):
    result = ZERO
    for x in xs:
        result = add(result, x)
    return result


def scale(x, a):
    return [[mul(x, y) for y in row] for row in a]


def plus(a, b):
    return [[add(x, y) for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]


def blocks(a, b, c, d):
    return [x + y for x, y in zip(a, b)] + [x + y for x, y in zip(c, d)]


def inverse_matrix(a):
    n = len(a)
    aug = [list(row) + erow for row, erow in zip(a, eye(n))]
    for j in range(n):
        pivot = next((k for k in range(j, n) if aug[k][j] != ZERO), None)
        if pivot is None:
            raise ArithmeticError("Singular Gaussian-rational matrix.")
        aug[j], aug[pivot] = aug[pivot], aug[j]
        factor = inverse_scalar(aug[j][j])
        aug[j] = [mul(factor, x) for x in aug[j]]
        for k in range(n):
            if k != j:
                factor = aug[k][j]
                aug[k] = [add(x, neg(mul(factor, y)))
                          for x, y in zip(aug[k], aug[j])]
    assert [row[:n] for row in aug] == eye(n)
    result = [row[n:] for row in aug]
    assert mm(a, result) == eye(n) == mm(result, a)
    return result


def reflection(v):
    n = sum(x*x for x in v)
    return [[q(F(j == k) - 2*v[j]*v[k]/n) for k in range(len(v))]
            for j in range(len(v))]


def passive_checks():
    n = 3
    identity, z = eye(n), zeros(n)
    real_frame = mm(reflection([F(1), F(2), F(2)]),
                    reflection([F(1), F(1), F(0)]))
    u = mm(real_frame, diag([ONE, I, q(F(3, 5), F(4, 5))]))
    assert mm(dag(u), u) == identity
    assert u != dag(u)
    dl, dr = diag([q(1), q(2), q(3)]), diag([q(2), q(3), q(4)])
    gamma_l, gamma_r = mm(dl, dl), mm(dr, dr)
    d = blocks(dl, z, z, dr)
    gamma = mm(d, d)

    def physical_scattering(singulars):
        c = mm(u, diag([q(s) for s in singulars]))
        j = mm(mm(dr, c), dl)
        k = blocks(z, dag(j), j, z)
        kt = blocks(z, dag(c), c, z)
        direct = plus(eye(2*n), scale(q(-1), mm(mm(
            d, inverse_matrix(plus(scale(q(F(1, 2)), gamma), scale(I, k)))), d)))
        normalized = plus(eye(2*n), scale(q(-1), inverse_matrix(
            plus(scale(q(F(1, 2)), eye(2*n)), scale(I, kt)))))
        assert direct == normalized
        assert mm(dag(direct), direct) == eye(2*n)
        return direct, j

    matched, j = physical_scattering([F(1, 2)]*n)
    assert matched == scale(I, blocks(z, dag(u), u, z))
    assert mm(mm(dag(j), inverse_matrix(gamma_r)), j) == scale(q(F(1, 4)), gamma_l)

    singulars = [F(1, 2), F(1), F(3, 2)]
    r = [(s*s-F(1, 4))/(s*s+F(1, 4)) for s in singulars]
    t = [s/(s*s+F(1, 4)) for s in singulars]
    assert r == [F(0), F(3, 5), F(4, 5)]
    assert t == [F(1), F(4, 5), F(3, 5)]
    assert all(x*x+y*y == 1 for x, y in zip(r, t))
    bad, bad_j = physical_scattering(singulars)
    rr, tt = diag([q(x) for x in r]), diag([q(x) for x in t])
    expected = blocks(rr, scale(I, mm(tt, dag(u))),
                      scale(I, mm(u, tt)), mm(mm(u, rr), dag(u)))
    assert bad == expected
    assert mm(mm(dag(bad_j), inverse_matrix(gamma_r)), bad_j) != scale(q(F(1, 4)), gamma_l)
    worst, mean = min(x*x for x in t), sum(x*x for x in t)/n
    assert worst == F(9, 25) and mean == F(2, 3)
    return {"unequal_linewidth_normalized_scattering": True,
            "matched_full_odd_exchange": True,
            "mismatch_conversion_worst": str(worst),
            "mismatch_conversion_uniform_mean": str(mean)}


def bragg_checks():
    # BF1 with its known scalar suppressed. v/sqrt(N) has equal power;
    # outer products avoid introducing irrational square roots.
    v = [ONE, I, q(F(3, 5), F(4, 5)), q(-1), q(0, -1), q(F(3, 5), F(-4, 5))]
    n, d = len(v), len(v)//2
    p = [[mul(q(F(1, n)), mul(x, conj(y))) for y in v] for x in v]
    assert mm(p, p) == p == dag(p)
    cases = [ONE, q(-1), I, q(F(3, 5), F(4, 5))]
    for phase in cases:
        assert norm2(phase) == 1
        c = add(phase, q(-1))
        vn = plus(eye(n), scale(c, p))
        assert mm(dag(vn), vn) == eye(n)
        cross = [row[:d] for row in vn[d:]]
        # All 2x2 minors vanish; this finite nonzero case has rank one.
        for j in range(d):
            for k in range(d):
                assert mul(cross[j][k], cross[0][0]) == mul(cross[j][0], cross[0][k])
        for k in range(d):
            transfer = sum(norm2(cross[j][k]) for j in range(d))
            assert transfer == norm2(c)/(4*d) <= F(1, d)
        trace = sumq(vn[j][j] for j in range(n))
        assert norm2(trace) >= (n-2)**2
        if phase == q(-1):
            assert cross[0][0] != ZERO
            assert transfer == F(1, 3)
            assert trace == q(n-2)
    return {"six_frequency_equal_power_cross_block_rank_at_reflection": 1,
            "frequency_input_transfer_at_reflection": "1/3",
            "phase_samples": len(cases)}


def run_checks():
    return {"status": "passed", "passive_scattering": passive_checks(),
            "equal_power_bragg": bragg_checks(),
            "scope": "Exact finite normalized input/output and optical rank guards. Universal proofs and primary physical assumptions are analytic; no hardware certification or ordinary optimum."}


if __name__ == "__main__":
    print(json.dumps(run_checks(), indent=2))
