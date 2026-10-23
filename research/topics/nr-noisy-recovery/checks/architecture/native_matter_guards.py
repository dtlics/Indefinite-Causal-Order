"""Exact finite NR-R19 holonomic, adiabatic-port and BDI-control guards.

Self-contained standard-library rational/Gaussian-rational replay.
Universal control/loop-rank proofs, physical unknown-frame priors,
phase/runtime access and finite-time pulse errors remain analytic.
No laboratory device or native switch advantage is certified.
"""
from fractions import Fraction as F
import json

if not __debug__:
    raise RuntimeError("Run the exact guard without -O.")


def eye(n):
    return [[F(j == k) for k in range(n)] for j in range(n)]


def z(n):
    return [[F(0) for _ in range(n)] for _ in range(n)]


def t(a):
    return [list(row) for row in zip(*a)]


def mm(a, b):
    return [[sum((x*y for x, y in zip(row, col)), F(0))
             for col in zip(*b)] for row in a]


def add(a, b):
    return [[x+y for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]


def scale(x, a):
    return [[x*y for y in row] for row in a]


def blocks(a, b, c, d):
    return [x+y for x, y in zip(a, b)]+[x+y for x, y in zip(c, d)]


def outer(v, w):
    return [[x*y for y in w] for x in v]


def reflection(v):
    norm = sum(x*x for x in v)
    return add(eye(len(v)), scale(-2/norm, outer(v, v)))


def rank(a):
    a = [list(row) for row in a]
    row = 0
    for col in range(len(a[0])):
        pivot = next((j for j in range(row, len(a)) if a[j][col]), None)
        if pivot is None:
            continue
        a[row], a[pivot] = a[pivot], a[row]
        factor = a[row][col]
        a[row] = [x/factor for x in a[row]]
        for j in range(len(a)):
            if j != row:
                factor = a[j][col]
                a[j] = [x-factor*y for x, y in zip(a[j], a[row])]
        row += 1
    return row


def holonomic_checks():
    n = 3
    r = reflection([F(1), F(2), F(2)])
    l = mm(reflection([F(1), F(1), F(1)]),
           reflection([F(2), F(1), F(2)]))
    assert mm(t(r), r) == eye(n) == mm(t(l), l)
    u = mm(l, t(r))
    a, b = eye(2*n), eye(2*n)
    selected = 1
    for j in range(n):
        rj, lj = [row[j] for row in r], [row[j] for row in l]
        # sqrt(2) cancels from the reflection projector.
        fm = reflection(rj+[-x for x in lj])
        fp = reflection(rj+lj)
        assert rank(add(eye(2*n), scale(F(-1), fm))) == 1
        a = mm(fm, a)
        b = mm(fp if j == selected else fm, b)
    rk, lk = [row[selected] for row in r], [row[selected] for row in l]
    h0, h1 = reflection(rk), reflection(lk)
    expected_a = blocks(z(n), t(u), u, z(n))
    expected_b = blocks(z(n), mm(h0, t(u)), mm(u, h0), z(n))
    target = blocks(h0, z(n), z(n), h1)
    assert a == expected_a and b == expected_b
    assert mm(a, b) == target == mm(b, a)
    assert rank(add(eye(2*n), scale(F(-1), a))) == n
    assert rank(add(eye(2*n), a)) == n
    m0, m1 = blocks(h0, z(n), z(n), eye(n)), blocks(eye(n), z(n), z(n), h1)
    assert mm(m1, m0) == target
    assert rank(add(eye(2*n), scale(F(-1), target))) == 2
    assert rank(add(eye(2*n), scale(F(-1), m0))) == 1
    assert rank(add(eye(2*n), scale(F(-1), m1))) == 1
    # Squared durations compare 2*sqrt(2)*T with 2*d*T without floats.
    assert 8 < (2*n)**2
    return {"data_dimension": n, "station_loops_each": n,
            "direct_target_loops": 2, "unknown_dense_frame_identity": True,
            "fixed_remaining_leg_direct_duration": "2 sqrt(2) T",
            "two_station_duration": "6 T"}


# Gaussian-rational scalars suffice for the ideal adiabatic phase example.
def q(re=0, im=0):
    return (F(re), F(im))


def qa(x, y):
    return (x[0]+y[0], x[1]+y[1])


def qm(x, y):
    return (x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0])


def qc(x):
    return (x[0], -x[1])


def qsum(xs):
    out = q()
    for x in xs:
        out = qa(out, x)
    return out


def qmm(a, b):
    return [[qsum(qm(x, y) for x, y in zip(row, col))
             for col in zip(*b)] for row in a]


def qdag(a):
    return [[qc(x) for x in row] for row in zip(*a)]


def stirap_checks():
    n = 3
    # Ideal adiabatic columns g,e,f; Phi phases are pi, pi/2, 0 mod 2pi.
    c, s = [F(-1), F(0), F(1)], [F(0), F(1), F(0)]
    out = [[q() for _ in range(3*n)] for _ in range(3*n)]
    for j in range(n):
        out[2*n+j][j] = q(-1)
        out[j][n+j] = q(0, -s[j])
        out[n+j][n+j] = q(c[j])
        out[j][2*n+j] = q(c[j])
        out[n+j][2*n+j] = q(0, -s[j])
    identity = [[q(int(j == k)) for k in range(3*n)] for j in range(3*n)]
    assert qmm(qdag(out), out) == identity
    for j in range(n):
        assert out[2*n+j][j] == q(-1)
        assert all(out[k][j] == q() for k in range(2*n))
    assert out[n+1][2*n+1] == q(0, -1)
    assert all(out[k][2*n+1] == q() for k in list(range(n))+list(range(2*n, 3*n)))
    return {"initial_g_transfer": "perfect in declared ideal adiabatic model",
            "initial_f_second_mode_excited_leakage": "1",
            "finite_time_dynamics_certified": False}


def qreal(a):
    return [[q(x) for x in row] for row in a]


def qscale(x, a):
    return [[qm(x, y) for y in row] for row in a]


def qconj(a):
    return [[qc(x) for x in row] for row in a]


def bdi_checks():
    n = 3
    frame = reflection([F(1), F(2), F(2)])
    oa = mm(mm(frame, [[F(-1), F(0), F(0)],
                       [F(0), F(-1), F(0)], [F(0), F(0), F(1)]]), t(frame))
    ob = mm(mm(frame, [[F(1), F(0), F(0)],
                       [F(0), F(-1), F(0)], [F(0), F(0), F(1)]]), t(frame))
    assert oa == t(oa) and ob == t(ob)
    assert mm(oa, oa) == eye(n) == mm(ob, ob)
    h = mm(oa, ob)
    assert h == t(h) and mm(h, h) == eye(n)
    assert mm(oa, ob) == mm(ob, oa)
    a, b = blocks(z(n), oa, oa, z(n)), blocks(z(n), ob, ob, z(n))
    target = blocks(h, z(n), z(n), h)
    assert mm(a, b) == target == mm(b, a)

    def dress(real_core, phase):
        core = qreal(real_core)
        return qscale(phase, core[:n])+qscale(qc(phase), core[n:])

    pa, pb = q(F(3, 5), F(4, 5)), q(0, 1)
    product = qmm(dress(b, pb), dress(a, pa))
    fixed_address_block = [row[:n] for row in product[:n]]
    assert fixed_address_block == qscale(qm(pb, qc(pa)), qreal(h))

    phases = [[q(1), q(), q()], [q(), q(0, 1), q()],
              [q(), q(), q(F(3, 5), F(4, 5))]]
    v = qmm(qreal(frame), phases)
    assert qmm(qdag(v), v) == qreal(eye(n))
    symmetry = qmm(v, t(v))
    assert symmetry == t(symmetry)
    assert qmm(qdag(symmetry), symmetry) == qreal(eye(n))
    physical_h = qmm(qmm(v, qreal(h)), qdag(v))
    conjugate_h = qconj(physical_h)
    assert physical_h != conjugate_h
    assert qmm(qmm(qdag(symmetry), physical_h), symmetry) == conjugate_h
    ua = qmm(qmm(qconj(v), qreal(oa)), qdag(v))
    ub = qmm(qmm(qconj(v), qreal(ob)), qdag(v))
    assert ua == t(ua) and ub == t(ub)
    assert qmm(qdag(ua), ub) == physical_h
    assert qmm(qmm(ua, physical_h), qdag(ua)) == conjugate_h
    iz, zz = qreal(eye(n)), qreal(z(n))
    controlled_symmetry = blocks(iz, zz, zz, symmetry)
    address_independent_h = blocks(physical_h, zz, zz, physical_h)
    physical_target = blocks(physical_h, zz, zz, conjugate_h)
    assert qmm(qmm(qdag(controlled_symmetry), address_independent_h),
               controlled_symmetry) == physical_target
    return {"common_real_symmetry_two_query_target": True,
            "static_phase_fixed_address_global_only": True,
            "known_complex_symmetry_wrapper": True,
            "unknown_symmetry_access_certified": False}


def verify_native_matter_guards():
    return {"status": "passed", "holonomic": holonomic_checks(),
            "stirap": stirap_checks(), "bdi": bdi_checks(),
            "scope": "Finite exact paired-frame, ideal-adiabatic and common-symmetry control matrices. Universal proofs, native prior/access, finite-time errors and measured costs are analytic; no native switch margin."}


if __name__ == "__main__":
    print(json.dumps(verify_native_matter_guards(), indent=2))
