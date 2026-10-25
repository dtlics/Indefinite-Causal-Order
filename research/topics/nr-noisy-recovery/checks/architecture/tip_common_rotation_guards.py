"""Exact finite common-R fixtures for the conditional weak-tag theorem.

Standard library only. Rational Gaussian matrices check full retained
fine-operator identities and pointwise geometry, not bath identification,
finite-rate TIP propagation, arbitrary dynamic controls, or physical cost.
"""
from fractions import Fraction as F
import json

if not __debug__:
    raise RuntimeError("Run exact common-rotation guards without -O.")


def g(x=0, y=0):
    return (F(x), F(y))


Z, O = g(), g(1)


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def neg(a):
    return (-a[0], -a[1])


def sub(a, b):
    return add(a, neg(b))


def mul(a, b):
    return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])


def conj(a):
    return (a[0], -a[1])


def norm(a):
    return a[0]**2 + a[1]**2


def zeros(n, m):
    return [[Z for _ in range(m)] for _ in range(n)]


def eye(n):
    a = zeros(n, n)
    for i in range(n):
        a[i][i] = O
    return a


def dag(a):
    return [[conj(a[j][i]) for j in range(len(a))]
            for i in range(len(a[0]))]


def mm(a, b):
    c = zeros(len(a), len(b[0]))
    for i in range(len(a)):
        for k in range(len(b)):
            if a[i][k] != Z:
                for j in range(len(b[0])):
                    if b[k][j] != Z:
                        c[i][j] = add(c[i][j], mul(a[i][k], b[k][j]))
    return c


def kron(a, b):
    return [[mul(a[i//len(b)][j//len(b[0])],
                 b[i % len(b)][j % len(b[0])])
             for j in range(len(a[0])*len(b[0]))]
            for i in range(len(a)*len(b))]


def su2(a, b):
    assert norm(a) + norm(b) == 1
    u = [[a, neg(conj(b))], [b, conj(a)]]
    assert mm(dag(u), u) == eye(2)
    return u


def state(u):
    return [[u[0][0]], [u[1][0]]]


def geometry(u0, u1, r):
    d0, d1 = mm(r, state(u0)), mm(r, state(u1))
    overlap = mm(dag(d0), d1)[0][0]
    a = 1 - norm(overlap)
    p0, p1 = norm(d0[1][0]), norm(d1[1][0])
    t0, t1 = mul(conj(d0[0][0]), d0[1][0]), mul(conj(d1[0][0]), d1[1][0])
    dt2, dp2 = norm(sub(t0, t1)), (p0 - p1)**2
    assert a == dt2 + dp2 and 0 <= a <= 1
    return a, dt2, dp2


def verify():
    unitaries = [eye(2), su2(g(F(3, 5)), g(F(4, 5))),
                 su2(g(F(5, 13)), g(0, F(12, 13))),
                 su2(g(F(5, 13), F(12, 13)), Z),
                 su2(Z, O)]
    pairs = [(unitaries[0], unitaries[1]),
             (unitaries[1], unitaries[2]),
             (unitaries[2], unitaries[4]),
             (unitaries[0], unitaries[0])]
    geometry_count = fine_count = chronological_count = 0
    # The first three durations sum to the full 2T clock (T=1).
    durations = [F(1, 3), F(2, 3), F(1)]
    for u0, u1 in pairs:
        invariant = geometry(u0, u1, eye(2))[0]
        for gamma, big_gamma in [(F(2), F(1)), (F(2), F(3, 2))]:
            integrated = F(0)
            for j, r in enumerate(unitaries):
                a, dt2, dp2 = geometry(u0, u1, r)
                assert a == invariant
                density = gamma*dt2/4 + big_gamma*dp2/2
                assert density >= gamma*a/4
                if j < len(durations):
                    integrated += durations[j]*density
                geometry_count += 1
            assert integrated >= gamma*invariant/2

    # Helper first; system consists of B and a retained two-level auxiliary.
    # All 16 system matrix units span arbitrary fine operators, including
    # B-changing operations and every retained auxiliary input/output.
    ns = 4
    units = []
    for out in range(ns):
        for inp in range(ns):
            k = zeros(ns, ns)
            k[out][inp] = O
            units.append(k)
    helper_units = []
    for out in range(2):
        for inp in range(2):
            l = zeros(2, 2)
            l[out][inp] = O
            helper_units.append(l)
    for u0, u1 in pairs[:3]:
        us = [u0, u1]
        tag = zeros(2*ns, 2*ns)
        for s in range(ns):
            for i in range(2):
                for j in range(2):
                    tag[i*ns+s][j*ns+s] = us[s//2][i][j]
        assert mm(dag(tag), tag) == eye(2*ns)
        for rt in unitaries[:3]:
            for l in helper_units:
                q = mm(mm(dag(rt), l), rt)
                # Retain the actual final frame, then undo it. This is
                # the chronological single insertion identity, not a
                # gate-labelled bath permutation.
                for rf in unitaries[2:4]:
                    after = mm(rf, dag(rt))
                    actual_q = mm(mm(mm(dag(rf), after), l), rt)
                    assert actual_q == q
                    chronological_count += 1
                for k in units:
                    actual = mm(mm(dag(tag), kron(q, k)), tag)
                    for f in range(2):
                        for sout in range(ns):
                            for sin in range(ns):
                                coefficient = mm(mm(dag(us[sout//2]), q), us[sin//2])[f][0]
                                expected = mul(k[sout][sin], coefficient)
                                assert actual[f*ns+sout][sin] == expected
                        fine_count += 1
    return {"pointwise_and_integrated_geometry_fixtures": geometry_count,
            "chronological_common_frame_fixtures": chronological_count,
            "full_retained_fine_operator_fixtures": fine_count,
            "scope": "Exact finite rational rotations and complete matrix-unit spans; analytic arbitrary-R(t) bound under fixed physical white baths and D-independent body only. No physical retained-chi implementation or finite-rate advantage."}


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
