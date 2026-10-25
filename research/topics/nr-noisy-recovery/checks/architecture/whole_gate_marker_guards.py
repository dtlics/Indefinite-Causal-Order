"""Exact Q(sqrt(2),sqrt(3)) full fine-isometry fixtures.

Code dimension two plus one retained leakage level. Matrix units span
arbitrary complex gate fine operators; these are algebra fixtures, not
a waveform, noisy-checker or physical-clock certificate.
"""
from fractions import Fraction as F
import json

if not __debug__:
    raise RuntimeError("Run exact whole-gate marker guards without -O.")


def r(a=0, b=0, c=0, d=0):
    return (F(a), F(b), F(c), F(d))  # 1,sqrt2,sqrt3,sqrt6


ZERO, ONE = r(), r(1)


def add(a, b):
    return tuple(x+y for x, y in zip(a, b))


def neg(a):
    return tuple(-x for x in a)


def times(a, b):
    out = [F(0)]*4
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            common = i & j
            out[i ^ j] += x*y*(2 if common & 1 else 1)*(3 if common & 2 else 1)
    return tuple(out)


def zeros(n, m):
    return [[ZERO for _ in range(m)] for _ in range(n)]


def eye(n):
    a = zeros(n, n)
    for i in range(n):
        a[i][i] = ONE
    return a


def trans(a):
    return list(map(list, zip(*a)))


def mm(a, b):
    c = zeros(len(a), len(b[0]))
    for i in range(len(a)):
        for k in range(len(b)):
            if a[i][k] != ZERO:
                for j in range(len(b[0])):
                    if b[k][j] != ZERO:
                        c[i][j] = add(c[i][j], times(a[i][k], b[k][j]))
    return c


def ma(a, b):
    return [[add(a[i][j], b[i][j]) for j in range(len(a[0]))] for i in range(len(a))]


def kron(a, b):
    return [[times(a[i//len(b)][j//len(b[0])], b[i % len(b)][j % len(b[0])])
             for j in range(len(a[0])*len(b[0]))]
            for i in range(len(a)*len(b))]


def columns(vectors):
    return [list(row) for row in zip(*vectors)]


def vector_kron(a, b):
    return [times(x, y) for x in a for y in b]


def scale(a, z):
    return [[times(x, z) for x in row] for row in a]


def verify():
    root2half, root3half = r(0, F(1, 2)), r(0, 0, F(1, 2))
    c = r(0, F(1, 4), 0, F(1, 4))
    s = r(0, F(-1, 4), 0, F(1, 4))
    phi, perp = [c, s], [neg(s), c]
    xphi = [s, c]
    assert mm([phi], [[z] for z in phi]) == [[ONE]]
    assert mm([phi], [[z] for z in xphi]) == [[r(F(1, 2))]]
    a = [root2half, root2half, ZERO, ZERO]
    b = [ZERO, root2half, root2half, ZERO]
    v1 = [r(0, 0, 0, F(-1, 6)), r(0, 0, 0, F(1, 6)),
          r(0, 0, 0, F(1, 3)), ZERO]
    v2 = [r(0, 0, F(1, 3)), r(0, 0, F(-1, 3)), r(0, 0, F(1, 3)), ZERO]
    v3 = [ZERO, ZERO, ZERO, ONE]
    us = columns([vector_kron(phi, [ONE, ZERO]), vector_kron(perp, [ONE, ZERO]),
                  vector_kron(phi, [ZERO, ONE]), vector_kron(perp, [ZERO, ONE])])
    vs = columns([a, v1, v2, v3])
    assert mm(trans(us), us) == mm(trans(vs), vs) == eye(4)
    aux = mm(vs, trans(us))
    assert mm(trans(aux), aux) == eye(4)
    assert mm(aux, [[z] for z in vector_kron(phi, [ONE, ZERO])]) == [[z] for z in a]
    assert mm(aux, [[z] for z in vector_kron(xphi, [ONE, ZERO])]) == [[z] for z in b]

    # Data first, then (marker,control). Code={0,1}, leakage={2}.
    e = [[ONE, ZERO], [ZERO, ONE], [ZERO, ZERO]]
    initial_native = kron(e, [[z] for z in a])
    initial_ordinary = kron(e, [[z] for z in vector_kron(phi, [ONE, ZERO])])
    marker = zeros(12, 12)
    pc0, pc1 = zeros(12, 12), zeros(12, 12)
    for data in range(3):
        for m in range(2):
            for ctrl in range(2):
                inp = 4*data+2*m+ctrl
                out = 4*data+2*(m ^ (data == 2))+ctrl
                marker[out][inp] = ONE
                (pc0 if ctrl == 0 else pc1)[inp][inp] = ONE
    assert mm(trans(marker), marker) == eye(12)
    aux_lift = kron(eye(3), aux)
    full_count = measured_count = 0
    for i in range(3):
        for j in range(3):
            gate = zeros(3, 3)
            gate[i][j] = ONE
            lifted = kron(gate, eye(4))
            switch = ma(mm(mm(pc0, marker), lifted), mm(mm(pc1, lifted), marker))
            native = mm(switch, initial_native)
            ordinary_before_aux = mm(mm(marker, lifted), initial_ordinary)
            ordinary = mm(aux_lift, ordinary_before_aux)
            assert native == ordinary  # full quantum auxiliary/data isometry
            full_count += 1
            # Native measured flags versus one-marker basis measurement
            # and a three-way classical split. Each split Kraus is raw/sqrt3.
            measured = {}
            for sign in (1, -1):
                for m in range(2):
                    k = zeros(3, 2)
                    for data in range(3):
                        for col in range(2):
                            k[data][col] = times(root2half,
                                add(native[4*data+2*m][col],
                                    times(r(sign), native[4*data+2*m+1][col])))
                    measured[(sign, m)] = k
            weak = []
            for bra in (phi, perp):
                k = zeros(3, 2)
                for data in range(3):
                    for col in range(2):
                        for m in range(2):
                            k[data][col] = add(k[data][col],
                                times(bra[m], ordinary_before_aux[4*data+2*m][col]))
                weak.append(k)
            # The control of the ordinary instrument is the unused |0>.
            assert measured[(1, 0)] == weak[0]
            split = scale(weak[1], r(0, 0, F(1, 3)))
            assert measured[(-1, 0)] == scale(split, r(-1))
            assert measured[(1, 1)] == measured[(-1, 1)] == split
            for (sign, m), k in measured.items():
                expected = zeros(3, 2)
                for row in range(3):
                    for col in range(2):
                        if sign == 1 and m == 0:
                            expected[row][col] = times(gate[row][col], r(1 if row < 2 else F(1, 2)))
                        elif row == 2:
                            expected[row][col] = times(gate[row][col], r(F(-1, 2) if (sign, m) == (-1, 0) else F(1, 2)))
                assert k == expected
                measured_count += 1
    return {"full_gate_matrix_unit_isometry_fixtures": full_count,
            "measured_weak_marker_compiler_fixtures": measured_count,
            "known_auxiliary_unitary_verified": True,
            "scope": "Arbitrary whole-gate fine operators under one common dilation and qualified ideal marker; full quantum and measured instruments. No noisy-checker, slot-drift, source control or timing claim."}


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
