"""Exact finite guards for the bounded-overlap random-unitary certificate.

Matrix ingredients use Q(i); the cube-root geometry uses Q(omega).
Entropy integration and coding achievability are analytic, not replayed.
No third-party dependencies, file writes or import-time output.
"""

from fractions import Fraction as F
import json
import random

if not __debug__:
    raise RuntimeError("Run approximate-unitary guards without -O.")


def z(re=0, im=0):
    return F(re), F(im)


def za(x, y):
    return x[0] + y[0], x[1] + y[1]


def zm(x, y):
    return x[0]*y[0] - x[1]*y[1], x[0]*y[1] + x[1]*y[0]


def zc(x):
    return x[0], -x[1]


def zs(x, t):
    return x[0]*t, x[1]*t


def zn2(x):
    return x[0]*x[0] + x[1]*x[1]


def zsum(values):
    out = z()
    for value in values:
        out = za(out, value)
    return out


def eye(d):
    return tuple(tuple(z(i == j) for j in range(d)) for i in range(d))


def adj(a):
    return tuple(tuple(zc(a[j][i]) for j in range(len(a)))
                 for i in range(len(a)))


def mm(a, b):
    d = len(a)
    return tuple(tuple(zsum(zm(a[i][k], b[k][j]) for k in range(d))
                       for j in range(d)) for i in range(d))


def ma(a, b):
    return tuple(tuple(za(x, y) for x, y in zip(ar, br))
                 for ar, br in zip(a, b))


def ms(a, t):
    return tuple(tuple(zs(x, t) for x in ar) for ar in a)


def imul(a):
    return tuple(tuple((-x[1], x[0]) for x in ar) for ar in a)


def tr(a):
    return zsum(a[i][i] for i in range(len(a)))


def norm2(a):
    return sum(zn2(x) for ar in a for x in ar)


def pauli(label, n):
    d = 1 << n
    x, zz = label & (d-1), label >> n
    phase = (z(1), z(0, 1), z(-1), z(0, -1))[(x & zz).bit_count() % 4]
    rows = [[z() for _ in range(d)] for _ in range(d)]
    for col in range(d):
        rows[col ^ x][col] = zs(phase, (-1) ** ((zz & col).bit_count() & 1))
    return tuple(tuple(row) for row in rows)


def bracket(a, b, n):
    mask = (1 << n)-1
    return (((a & mask) & (b >> n)).bit_count()
            + ((b & mask) & (a >> n)).bit_count()) & 1


def geometry(n, rat):
    d = 1 << n
    a, b = (1-rat*rat)/(1+rat*rat), 2*rat/(1+rat*rat)
    identity = eye(d)
    ps = [pauli(i, n) for i in range(d*d)]
    us = [identity] + [ma(ms(p, a), ms(imul(identity), b)) for p in ps[1:]]
    for u in us:
        assert mm(adj(u), u) == identity
    overlaps, biases = [], []
    for i, u in enumerate(us):
        orow, crow = [], []
        for j, v in enumerate(us):
            overlap = zs(tr(mm(adj(u), v)), F(1, d))
            orow.append(zn2(overlap))
            comm = ma(mm(u, v), ms(mm(v, u), -1))
            cij = 1 - norm2(comm)/(2*d)
            # Independent direct group-commutator trace.
            trace_bias = zs(tr(mm(mm(mm(adj(v), adj(u)), v), u)), F(1, d))
            assert trace_bias[0] == cij
            assert cij == 1 - a**4 * (2 * bracket(i, j, n))
            crow.append(cij)
        overlaps.append(orow)
        biases.append(crow)
    actual_m = max(overlaps[i][j] for i in range(len(us))
                   for j in range(len(us)) if i != j)
    assert actual_m == b*b
    assert d*actual_m < 1
    return us, overlaps, biases, actual_m


def quadratic(weights, coefficients):
    return sum(x*y*coefficients[i][j]
               for i, x in enumerate(weights) for j, y in enumerate(weights))


def choi(weights, us):
    d = len(us[0])
    vectors = [tuple(x for ar in u for x in ar) for u in us]
    return tuple(tuple(zsum(zs(zm(ui[a], zc(ui[b])), wi/F(d))
                             for wi, ui in zip(weights, vectors))
                       for b in range(d*d)) for a in range(d*d))


def tensor_bias(jj, d):
    return zs(zsum(zm(jj[dd*d+a][c*d+b], jj[c*d+dd][b*d+a])
                   for a in range(d) for b in range(d)
                   for c in range(d) for dd in range(d)), d)


def omega_mul(x, y):
    """Multiply a+b*omega, where omega**2=-1-omega."""
    aa, bb = x[0]*y[0], x[1]*y[1]
    return aa-bb, x[0]*y[1]+x[1]*y[0]-bb


def omega_conj(x):
    return x[0]-x[1], -x[1]


def omega_norm2(x):
    return x[0]*x[0]-x[0]*x[1]+x[1]*x[1]


def verify_cube_root():
    powers = ((F(1), F(0)), (F(0), F(1)), (F(-1), F(-1)))
    assert all(omega_norm2(u) == 1 for u in powers)
    assert omega_mul(powers[1], powers[1]) == powers[2]
    assert omega_mul(powers[1], powers[2]) == powers[0]
    assert tuple(sum(u[k] for u in powers) for k in (0, 1)) == (0, 0)
    for i in range(3):
        for j in range(3):
            phase = omega_mul(omega_conj(powers[i]), powers[j])
            overlap = ((1+phase[0])/2, phase[1]/2)
            assert omega_norm2(overlap) == (1 if i == j else F(1, 4))
    # Diagonal phase unitaries commute exactly. H(uniform_3)>log2(2)
    # follows from 3>2, without evaluating any logarithm.
    assert 3 > 2
    cubic_m, cubic_p0, cubic_fe = F(1, 4), F(1, 3), F(1, 2)
    assert 2*cubic_m < 1
    assert cubic_p0+(1-cubic_p0)*cubic_m == cubic_fe
    assert (cubic_fe-cubic_m)/(1-cubic_m) == cubic_p0
    assert F(3) == 2*(1-cubic_m)/(1-2*cubic_m)


def verify():
    rng = random.Random(78311)
    families = weighted_cases = tail_cases = tensor_cases = 0
    for n, rat in ((1, F(0)), (1, F(1, 10)),
                   (2, F(1, 10)), (2, F(1, 6))):
        us, overlaps, biases, m = geometry(n, rat)
        d, k = 1 << n, len(us)
        zeta = 1-d*m
        laws = [[F(1, k)]*k, [F(3, 5)]+[F(2, 5*(k-1))]*(k-1)]
        for _ in range(5):
            raw = [rng.randrange(0, 17) for _ in range(k)]
            laws.append([F(v, sum(raw)) for v in raw])
        for qi, q in enumerate(laws):
            c, purity = quadratic(q, biases), quadratic(q, overlaps)
            e = 1-c
            assert e >= 0 and abs(c) <= d*purity
            assert purity <= (1-m)*sum(x*x for x in q)+m
            fe = sum(qi*overlaps[0][i] for i, qi in enumerate(q))
            assert q[0] <= fe <= q[0]+(1-q[0])*m
            assert (fe-m)/(1-m) <= q[0]
            if m:
                assert fe == q[0]+(1-q[0])*m
            if qi < 2:
                jj = choi(q, us)
                tb = tensor_bias(jj, d)
                assert tb == z(c)
                assert sum(zn2(x) for row in jj for x in row) == purity
                tensor_cases += 1
            for beta in (F(1, 32), F(1, 8), F(1, 2), F(1), F(2), F(8)):
                v = [x if x <= beta/d else F(0) for x in q]
                w = sum(v)
                ev = quadratic(v, biases)
                jpur = quadratic(v, overlaps)
                assert abs(ev) <= d*jpur
                assert jpur <= (1-m)*sum(x*x for x in v)+m*w*w
                assert 0 <= w*w-ev <= e
                assert zeta*w*w-(1-m)*beta*w <= e
                assert zeta*w*w-beta*w <= e
                tail_cases += 1
            weighted_cases += 1
        families += 1

    verify_cube_root()

    # Fully rational sufficient positive confidence calculation.
    d = 1 << 32
    f, m = F(19, 50), F(1, 100*d)
    p_lower = (f-m)/(1-m)
    assert p_lower >= F(379, 1000)
    assert F(4, 99) < F(101, 500)**2
    certificate = (F(379, 1000)-F(101, 500))*32-1-F(621, 1000)*F(100, 33)
    assert certificate > F(278, 100)
    return {"status": "passed", "matrix_arithmetic": "exact Q(i) and Q(omega)",
            "unitary_families": families, "weighted_laws": weighted_cases,
            "exact_tail_inequalities": tail_cases, "tensor_contractions": tensor_cases,
            "cube_root_endpoint_counterexample": True,
            "conservative_positive_certificate": str(certificate),
            "scope": "Exact finite matrix, root-of-unity and rational threshold guards; entropy integration and all-dimension coding claims are analytic."}


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
