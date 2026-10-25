"""Exact rational full-instrument guard for the thermal dual-rail example.

Standard balanced fresh control independent of the unknown logical payload.
One supplied abstract-channel point, not a hardware control/bath certificate
or a lower bound against arbitrary ordinary interventions.
"""
from fractions import Fraction as F
import json

if not __debug__:
    raise RuntimeError("Run exact dual-rail guards without -O.")


def zeros(n, m):
    return [[F(0) for _ in range(m)] for _ in range(n)]


def eye(n):
    a = zeros(n, n)
    for i in range(n):
        a[i][i] = F(1)
    return a


def trans(a):
    return list(map(list, zip(*a)))


def mm(a, b):
    c = zeros(len(a), len(b[0]))
    for i in range(len(a)):
        for k in range(len(b)):
            if a[i][k]:
                for j in range(len(b[0])):
                    if b[k][j]:
                        c[i][j] += a[i][k]*b[k][j]
    return c


def kron(a, b):
    return [[a[i//len(b)][j//len(b[0])]*b[i % len(b)][j % len(b[0])]
             for j in range(len(a[0])*len(b[0]))]
            for i in range(len(a)*len(b))]


def plus(a, b, sign=F(1), scale=F(1)):
    return [[scale*(a[i][j]+sign*b[i][j]) for j in range(len(a[0]))]
            for i in range(len(a))]


def project(a, rows):
    return [[a[i][j] for j in (2, 1)] for i in rows]


def pnorm(ks):
    return sum(x*x for k in ks for row in k for x in row)/2


def apply(ks, rho):
    out = zeros(2, 2)
    for k in ks:
        out = plus(out, mm(mm(k, rho), trans(k)))
    return out


def apply_cross(left, right, rho):
    out = zeros(2, 2)
    for a, b in zip(left, right):
        out = plus(out, mm(mm(a, rho), trans(b)))
    return out


def pauli_map(weights, rho):
    i, x, y, z = ([[F(1), F(0)], [F(0), F(1)]],
                  [[F(0), F(1)], [F(1), F(0)]],
                  [[F(0), F(-1)], [F(1), F(0)]],
                  [[F(1), F(0)], [F(0), F(-1)]])
    # Real -iY has the same conjugation and trace-overlap magnitudes as Y.
    out = zeros(2, 2)
    for w, p in zip(weights, (i, x, y, z)):
        term = mm(mm(p, rho), trans(p))
        out = [[out[a][b]+w*term[a][b] for b in range(2)] for a in range(2)]
    return out


def replacement(diagonal, rho):
    trace = rho[0][0]+rho[1][1]
    return [[diagonal[0]*trace, F(0)], [F(0), diagonal[1]*trace]]


def verify():
    u = x = F(9, 25)
    v, rootx = 1-u, F(3, 5)
    b = u*v*(1-x)**2
    lam = F(3, 2)
    ks = [ [[F(4, 5), F(0)], [F(0), F(12, 25)]],
           [[F(0), F(16, 25)], [F(0), F(0)]],
           [[F(9, 25), F(0)], [F(0), F(3, 5)]],
           [[F(0), F(0)], [F(12, 25), F(0)]] ]
    completeness = zeros(2, 2)
    for k in ks:
        completeness = plus(completeness, mm(trans(k), k))
    assert completeness == eye(2)
    full = [kron(a, c) for a in ks for c in ks]
    podd, peven = zeros(4, 4), zeros(4, 4)
    for j in (1, 2):
        podd[j][j] = F(1)
    for j in (0, 3):
        peven[j][j] = F(1)
    native = {(s, parity): [] for s in (1, -1) for parity in (0, 1)}
    ordinary = {(marker, parity): [] for marker in (0, 1) for parity in (0, 1)}
    for a in full:
        for c in full:
            ac, ca = mm(a, c), mm(c, a)
            for sign in (1, -1):
                switched = plus(ac, ca, F(sign), F(1, 2))
                native[(sign, 0)].append(project(switched, (2, 1)))
                native[(sign, 1)].append(project(switched, (0, 3)))
            for marker, middle in ((0, podd), (1, peven)):
                chronological = mm(mm(c, middle), a)
                ordinary[(marker, 0)].append(project(chronological, (2, 1)))
                ordinary[(marker, 1)].append(project(chronological, (0, 3)))
    wp = [x*x+b*(1+6*x+x*x)/4+b*b/2,
          b*(1+6*x+x*x)/4, b*(1+6*x+x*x)/4, b*(1+x)**2/4]
    wm = [b*(1-x)**2/4-b*b/2,
          b*(1-x)**2/4, b*(1-x)**2/4, b*(1+x)**2/4]
    assert min(wp+wm) >= 0
    p1 = x+2*b
    po = p1*p1
    qo = (po+3*x*x)/4
    ordinary_good_weights = [qo]+[(po-x*x)/4]*3
    a0, a1 = v+u*x, u+v*x
    e00, e11 = v*(1-x)*a0, u*(1-x)*a1
    t00, t11 = v*(1-x*x)*(v+u*x*x), u*(1-x*x)*(u+v*x*x)
    c00, c11 = 2*v*rootx*(1-x)*a0*a0, 2*u*rootx*(1-x)*a1*a1
    dep_bad = b*(1+x*x-2*b)
    units = []
    for i in range(2):
        for j in range(2):
            e = zeros(2, 2)
            e[i][j] = F(1)
            units.append(e)
    full_map_cases = 0
    for rho in units:
        for sign, weights in ((1, wp), (-1, wm)):
            assert apply(native[(sign, 0)], rho) == pauli_map(weights, rho)
            assert apply(native[(sign, 1)], rho) == replacement(
                [(t00+sign*c00)/2, (t11+sign*c11)/2], rho)
            full_map_cases += 2
        assert apply(ordinary[(0, 0)], rho) == pauli_map(ordinary_good_weights, rho)
        assert apply(ordinary[(1, 0)], rho) == replacement([dep_bad, dep_bad], rho)
        assert apply(ordinary[(0, 1)], rho) == replacement([p1*e00, p1*e11], rho)
        assert apply(ordinary[(1, 1)], rho) == replacement([t00-p1*e00, t11-p1*e11], rho)
        full_map_cases += 4
    assert sum(pnorm(group) for group in native.values()) == 1
    assert sum(pnorm(group) for group in ordinary.values()) == 1
    # Complete orthogonal flag cross blocks vanish before any receiver
    # chooses a measurement, including control +/- coherence.
    cross_cases = 0
    for groups in (native, ordinary):
        keys = list(groups)
        for ia, ka in enumerate(keys):
            for kb in keys[ia+1:]:
                for rho in units:
                    assert apply_cross(groups[ka], groups[kb], rho) == zeros(2, 2)
                    cross_cases += 1
    go = qo-lam*(po-qo)
    gp = wp[0]-lam*(sum(wp)-wp[0])
    gm = wm[3]-lam*(sum(wm)-wm[3])
    assert go == F(-3124950111, 152587890625)
    assert gp == F(-13218092127, 152587890625)
    assert gm == F(1042255872, 152587890625) > 0
    assert max(F(0), go) == 0
    # Bounded stronger cadence at a different exact parameter point.
    # z^2=1/2, u=1/2 makes per-step p=(1+z^2)/2=3/4 exactly.
    xh = F(1, 2)
    bh = F(1, 4)*(1-xh)**2
    pmh = bh*(1-xh+xh*xh)-bh*bh/2
    qmh = bh*(1+xh)**2/4
    assert pmh == F(23, 512) and qmh == F(18, 512)
    assert qmh-3*(pmh-qmh) == F(3, 512)
    poh = (xh+2*bh)**2
    qoh = (poh+3*xh*xh)/4
    assert qoh-3*(poh-qoh) < 0
    qph = xh*xh+bh*(1+6*xh+xh*xh)/4+bh*bh/2
    pph = xh*xh+2*bh*(1+xh)**2-pmh
    assert qph-3*(pph-qph) < 0
    p4 = F(3, 4)**4
    q4 = (p4+3*F(1, 4))/4
    bad4 = p4-q4
    assert (p4, q4, bad4) == (F(81, 256), F(273, 1024), F(51, 1024))
    assert q4-3*bad4 == F(15, 128) == 20*F(3, 512)
    return {"full_abstract_native_and_ordinary_map_fixtures": full_map_cases,
            "kraus_pairs_per_scheme": len(full)**2,
            "all_launched_mass_each_scheme": "1",
            "retained_control_parity_crossblock_fixtures": cross_cases,
            "native_best_flag_policy_utility": str(gm),
            "ordinary_best_terminal_recovery_utility": "0",
            "separate_m4_cadence_fixture_utility": "15/128",
            "scope": "Standard fresh balanced-control abstract GAD SWITCH versus one coherent midpoint parity marker; arbitrary joint control/target terminal TNI CP recovery via orthogonal-block Pauli/replacement proof. No preencoded payload/control, physical port or all-ordinary converse."}


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
