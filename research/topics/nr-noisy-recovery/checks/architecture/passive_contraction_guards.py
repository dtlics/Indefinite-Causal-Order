"""Exact passive-loss routed-isometry fixtures, standard library only.

One photon occupies Q, R or a fresh loss port; D is an external retained
control. Tests include every input matrix unit through equality of the
success matrix and complementary erasure effect. They do not certify
real routing, clocks, detector noise, bath stationarity or device rates.
"""
from fractions import Fraction as F
import json

if not __debug__:
    raise RuntimeError("Run exact passive-erasure guards without -O.")


def g(x=0, y=0):
    return (F(x), F(y))


Z, O = g(), g(1)


def plus(a, b):
    return (a[0]+b[0], a[1]+b[1])


def neg(a):
    return (-a[0], -a[1])


def times(a, b):
    return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])


def star(a):
    return (a[0], -a[1])


def zeros(n, m):
    return [[Z for _ in range(m)] for _ in range(n)]


def eye(n):
    a = zeros(n, n)
    for i in range(n):
        a[i][i] = O
    return a


def add(a, b):
    return [[plus(x, y) for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def scale(a, s):
    return [[times(x, g(s)) for x in row] for row in a]


def dagger(a):
    return [[star(a[j][i]) for j in range(len(a))]
            for i in range(len(a[0]))]


def mm(a, b):
    c = zeros(len(a), len(b[0]))
    for i in range(len(a)):
        for k in range(len(b)):
            if a[i][k] != Z:
                for j in range(len(b[0])):
                    if b[k][j] != Z:
                        c[i][j] = plus(c[i][j], times(a[i][k], b[k][j]))
    return c


def diag(values):
    a = zeros(len(values), len(values))
    for i, value in enumerate(values):
        a[i][i] = value
    return a


def su2(a, b):
    u = [[a, neg(star(b))], [b, star(a)]]
    assert mm(dagger(u), u) == eye(2)
    return u


def contraction(u, v, transmitted, lost):
    a = mm(mm(u, diag([g(x) for x in transmitted])), v)
    c = mm(diag([g(x) for x in lost]), v)
    assert add(mm(dagger(a), a), mm(dagger(c), c)) == eye(2)
    return a, c


def initial(nports):
    # Each port has d=2 modes. D first; four input columns D x Q.
    stride = 2*nports
    state = zeros(2*stride, 4)
    for d in range(2):
        for mode in range(2):
            state[d*stride+mode][2*d+mode] = O
    return state


def swap_qr(state, nports, selected):
    stride = 2*nports
    result = [row[:] for row in state]
    for mode in range(2):
        p, q = selected*stride+mode, selected*stride+2+mode
        result[p], result[q] = result[q], result[p]
    return result


def channel(state, nports, a, c, envport, selected=None):
    stride = 2*nports
    result = [row[:] for row in state]
    ds = range(2) if selected is None else [selected]
    for d in ds:
        old = state[d*stride:d*stride+2]
        aq, cq = mm(a, old), mm(c, old)
        for mode in range(2):
            assert state[d*stride+2*envport+mode] == [Z]*4
            result[d*stride+mode] = aq[mode]
            result[d*stride+2*envport+mode] = cq[mode]
    return result


def compiler(a, ca, b, cb):
    # Q,R,A0loss,B1loss,A2loss. These are exact chronological operations,
    # not a manually installed desired successful block.
    n = 5
    state = swap_qr(initial(n), n, 1)
    state = channel(state, n, a, ca, 2)
    state = swap_qr(state, n, 1)
    state = channel(state, n, b, cb, 3)
    state = swap_qr(state, n, 0)
    state = channel(state, n, a, ca, 4)
    state = swap_qr(state, n, 0)
    return state, n


def native_clock(a, ca, b, cb):
    # Q,R,A0loss,B0loss,A1loss,B1loss: independent actual-clock baths.
    n = 6
    state = initial(n)
    state = channel(state, n, a, ca, 2, 0)
    state = channel(state, n, b, cb, 3, 1)
    state = channel(state, n, b, cb, 5, 0)
    state = channel(state, n, a, ca, 4, 1)
    return state, n


def blocks(state, nports):
    stride = 2*nports
    success, loss = [], []
    for d in range(2):
        success += state[d*stride:d*stride+2]
        assert state[d*stride+2:d*stride+4] == zeros(2, 4)
        loss += state[d*stride+4:(d+1)*stride]
    return success, loss


def expected_success(a, b):
    x, y = mm(b, a), mm(a, b)
    s = zeros(4, 4)
    for d, matrix in enumerate([x, y]):
        for i in range(2):
            for j in range(2):
                s[2*d+i][2*d+j] = matrix[i][j]
    return s


def lost_control(state, nports, input_density):
    stride = 2*nports
    out = mm(mm(state, input_density), dagger(state))
    reduced = zeros(2, 2)
    for d in range(2):
        for e in range(2):
            for pos in range(4, stride):
                reduced[d][e] = plus(reduced[d][e], out[d*stride+pos][e*stride+pos])
    return reduced


def verify():
    i = eye(2)
    r = su2(g(F(3, 5)), g(F(4, 5)))
    u = su2(g(F(5, 13)), g(0, F(12, 13)))
    phase = diag([g(F(5, 13), F(12, 13)), O])
    maps = [contraction(i, i, [1, 1], [0, 0]),
            contraction(r, u, [F(3, 5), F(5, 13)], [F(4, 5), F(12, 13)]),
            contraction(u, phase, [F(5, 13), 0], [F(12, 13), 1]),
            contraction(i, i, [0, 0], [1, 1])]
    count = effect_units = 0
    for a, ca in maps:
        for b, cb in maps:
            s = expected_success(a, b)
            effect = add(eye(4), scale(mm(dagger(s), s), -1))
            for builder in [compiler, native_clock]:
                state, n = builder(a, ca, b, cb)
                ss, lost = blocks(state, n)
                assert ss == s
                actual_effect = mm(dagger(lost), lost)
                assert actual_effect == effect
                assert mm(dagger(state), state) == eye(4)
                # Equality of all complementary-effect matrix entries spans
                # the input matrix units, including an arbitrary reference.
                for row in range(4):
                    for col in range(4):
                        assert actual_effect[row][col] == effect[row][col]
                        effect_units += 1
                count += 1
    # Physical chronological loss counterexample: A=I, B=(3/5)I.
    b, cb = scale(i, F(3, 5)), scale(i, F(4, 5))
    ready = [[g(F(1, 4)) if (row % 2) == (col % 2) else Z
              for col in range(4)] for row in range(4)]
    cs, cn = compiler(i, zeros(2, 2), b, cb)
    ns, nn = native_clock(i, zeros(2, 2), b, cb)
    native_lost = lost_control(ns, nn, ready)
    ordinary_lost = lost_control(cs, cn, ready)
    assert native_lost == scale(i, F(8, 25))
    assert ordinary_lost == [[g(F(8, 25)), g(F(8, 25))],
                             [g(F(8, 25)), g(F(8, 25))]]
    # Abstract module-Kraus SWITCH absorber-A retains D+, unlike fresh A0/A2.
    acs, acn = compiler(zeros(2, 2), i, i, zeros(2, 2))
    assert lost_control(acs, acn, ready) == scale(i, F(1, 2))
    abstract_lost = [[g(F(1, 2)), g(F(1, 2))],
                     [g(F(1, 2)), g(F(1, 2))]]
    assert abstract_lost != lost_control(acs, acn, ready)
    return {"chronological_routed_isometries": count,
            "complementary_effect_matrix_unit_fixtures": effect_units,
            "physical_timed_loss_control_counterexample": True,
            "abstract_module_loss_control_counterexample": True,
            "scope": "Exact rational complex contractions, full successful blocks and coarse-erasure effects. No real routing/bath/detector/clock qualification or arbitrary-channel simulation."}


if __name__ == "__main__":
    print(json.dumps({"status": "passed", **verify()}, indent=2))
