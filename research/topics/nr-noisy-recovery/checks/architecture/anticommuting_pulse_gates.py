"""Exact anticommuting-pulse instruments and achievable ordinary benchmarks.

The pulse identity family checks full data/reference matrix units at a
rational-trigonometric setting, including dense complex axes, multiplicity,
both switch flags, rollback and the two cost ledgers. The ordinary family
checks a literal random-order CP map, its uncomposed Choi-plane coordinates,
an exact algebraic error interval and an expected-query ledger.
All-angle timing and global diamond arguments remain analytic. No general
adaptive ordinary optimum, control-port grant or hardware-rate claim follows.
Both pulse arithmetic engines use standard-library exact fractions. The
separate source-parameter activation ledger is a floating-point scalar
diagnostic, not an exact noisy-gate certificate. Import/API is quiet,
predicates remain active under optimization, and no files are written.
"""
from fractions import Fraction as F
from itertools import product
import json
import sys

sys.dont_write_bytecode = True
from bosonic_order_gates import R, require
from anticommuting_pulse_dual import replay as exact_query_certificate
from pulse_activation_ledger import verify as activation_ledger
from retained_photon_serial import (
    G, zeros as gzeros, eye as geye, mm as gmm, adj as gadj,
    kron as gkron, scale as gscale, add as gadd,
)


def g_unit(n, i, j):
    out = gzeros(n)
    out[i][j] = G(1)
    return out

def g_cp(k, rho, weight=1):
    return gscale(gmm(gmm(k, rho), gadj(k)), weight)

def pulse_identities():
    x = [[G(), G(1)], [G(1), G()]]
    z = [[G(1), G()], [G(), G(-1)]]
    a4, b4 = (gkron(x, geye(2)), gkron(z, z))
    v = [G(1), G(0, 1), G(1), G(2)]
    house = gadd(geye(4), gscale([[p * q.conj() for q in v] for p in v], F(-2, 7)))
    require(gmm(gadj(house), house) == geye(4), 'dense complex axis-change unitary')
    fixtures = ((x, z), (a4, b4), (gmm(gmm(house, a4), gadj(house)), gmm(gmm(house, b4), gadj(house))))
    require(fixtures[2] != fixtures[1] and
            any(value.i != 0 for operator in fixtures[2] for row in operator for value in row),
            'the complex conjugated fixture changes the axes nontrivially')
    entries = units = 0
    for a, b in fixtures:
        n = len(a)
        identity = geye(n)
        require(a == gadj(a) and b == gadj(b), 'Hermitian involutions')
        require(gmm(a, a) == identity and gmm(b, b) == identity, 'involution normalization')
        require(gadd(gmm(a, b), gmm(b, a)) == gzeros(n), 'anticommutation promise')
        outer = gadd(gscale(identity, 3), gscale(a, G(0, -1)))
        inner = gadd(gscale(identity, 5), gscale(b, G(0, -3)))
        target = gadd(gscale(identity, 4), gscale(gadd(a, b), G(0, -3)))
        euler = gmm(gmm(outer, inner), outer)
        require(euler == gscale(target, 10), 'literal three-pulse Euler identity')
        require(gmm(gadj(target), target) == gscale(identity, 34), 'target normalization')
        pulse_a = gadd(gscale(identity, 4), gscale(a, G(0, -3)))
        pulse_b = gadd(gscale(identity, 4), gscale(b, G(0, -3)))
        word_ba, word_ab = (gmm(pulse_b, pulse_a), gmm(pulse_a, pulse_b))
        plus = gadd(word_ba, word_ab)
        minus = gadd(word_ba, gscale(word_ab, -1))
        require(plus == gscale(target, 8), 'sum of chronological words')
        require(minus == gscale(gmm(a, b), 18), 'complete failure word and sign')
        require(gadd(gscale(gmm(gadj(plus), plus), F(1, 2500)), gscale(gmm(gadj(minus), minus), F(1, 2500))) == identity, 'both native flags complete the input-independent instrument')
        corrected = gmm(gmm(b, a), minus)
        for i, j in product(range(n), repeat=2):
            rho = g_unit(n, i, j)
            require(g_cp(euler, rho, F(1, 3400)) == g_cp(target, rho, F(1, 34)), 'full data/reference ordinary Euler map')
            require(g_cp(plus, rho, F(1, 2500)) == g_cp(target, rho, F(16, 625)), 'native plus full data/reference map')
            require(g_cp(corrected, rho, F(1, 2500)) == gscale(rho, F(81, 625)), 'minus inverse restores unknown data/reference')
            entries += n * n
            units += 1
    q = F(1, 9)
    require(2 * (1 + q) / (1 - q) == F(5, 2), 'corrected-RUS call ledger')
    require(2 + 3 * q == F(7, 3), 'three-pulse terminal repair policy ledger')
    return {'axis_fixtures': len(fixtures), 'full_input_matrix_units': units, 'full_output_coefficients_per_identity': entries, 'scope': 'One exact rational-trigonometric setting, dense complex axis changes and multiplicity; full native flags/Euler/rollback maps. All-angle timing, adaptive-query optimum, noise and hardware ports remain analytic or unestablished.'}


def z(a=0, b=0):
    return (R(a), R(b))

def za(a, b):
    return (a[0] + b[0], a[1] + b[1])

def zm(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])

def zs(a, b):
    return (a[0] * b, a[1] * b)

def zc(a):
    return (a[0], -a[1])

def eye(d):
    return [[z(int(i == j)) for j in range(d)] for i in range(d)]

def scale(a, c):
    return [[zm(c, x) for x in row] for row in a]

def add(a, b):
    return [[za(x, y) for x, y in zip(row, other)] for row, other in zip(a, b)]

def adj(a):
    return [[zc(a[j][i]) for j in range(len(a))] for i in range(len(a))]

def mm(a, b):
    return [[sumz([zm(a[i][k], b[k][j]) for k in range(len(a))]) for j in range(len(a))] for i in range(len(a))]

def sumz(values):
    out = z()
    for x in values:
        out = za(out, x)
    return out

def cp_coeff(ks):
    return {(i, j, r, s): sumz([zm(k[r][i], zc(k[s][j])) for k in ks]) for i in range(2) for j in range(2) for r in range(2) for s in range(2)}

def inner(a, b):
    c = mm(adj(a), b)
    return zs(sumz([c[i][i] for i in range(2)]), F(1, 2))

def ordinary_benchmark():
    I = eye(2)
    X = [[z(), z(1)], [z(1), z()]]
    Y = [[z(), z(0, -1)], [z(0, 1), z()]]
    Z = [[z(1), z()], [z(), z(-1)]]
    base = add(scale(I, z(F(9, 13))), scale(add(X, Z), z(0, -F(6, 13))))
    extra = scale(Y, z(0, F(4, 13)))
    u = add(base, extra)
    v = add(base, scale(extra, z(-1)))
    require(mm(adj(u), u) == I and mm(adj(v), v) == I, 'word unitarity')
    kp = scale(add(u, v), z(F(1, 2)))
    km = scale(add(u, scale(v, z(-1))), z(F(1, 2)))
    require(add(mm(adj(kp), kp), mm(adj(km), km)) == I, 'complete random order')
    left = cp_coeff([u, v])
    right = cp_coeff([kp, km])
    require(all((zs(left[k], F(1, 2)) == right[k] for k in left)), 'all matrix-unit CP entries')
    target = add(scale(I, z(R(0, F(1, 2)))), scale(add(X, Z), z(0, -F(1, 2))))
    require(mm(adj(target), target) == I, 'target unitary')
    q = R(F(16, 169))
    require(mm(adj(km), km) == scale(I, z(q)), 'literal minus effect')
    minus_i_H = scale(add(X, Z), z(0, R(0, -F(1, 2))))
    cp0, cph = (inner(I, kp), inner(minus_i_H, kp))
    ut0, uth = (inner(I, target), inner(minus_i_H, target))
    require(cp0 == z(F(9, 13)) and cph == z(R(0, F(6, 13))), 'literal accepted Choi coordinates')
    require(ut0 == z(R(0, F(1, 2))) and uth == z(R(0, F(1, 2))), 'literal target Choi coordinates')
    require(all((v[1] == 0 for v in (cp0, cph, ut0, uth))), 'real quaternion coordinates')
    aa = cp0[0] ** 2 - ut0[0] ** 2
    bb = cph[0] ** 2 - uth[0] ** 2
    ab = cp0[0] * cph[0] - ut0[0] * uth[0]
    require(aa == R(-F(7, 338)) and bb == R(-F(25, 338)) and (ab == R(-F(1, 2), F(54, 169))), 'derived uncomposed Choi plane')
    determinant = aa * bb - ab * ab
    d2 = R(F(153, 338), -F(54, 169))
    require(aa + bb == -q and determinant == -d2, 'uncomposed Choi plane spectrum')
    disc = q * q + 4 * d2
    require(disc == R(F(51970, 28561), -F(36504, 28561)) and disc > 0, 'exact discriminant')
    lo, hi = (F(10233, 100000), F(10234, 100000))
    require(2 * lo - q > 0 and (2 * lo - q) ** 2 < disc < (2 * hi - q) ** 2, 'exact half-diamond interval')
    require(disc < (F(2, 9) - q) ** 2, 'strictly better than 1/9 random-order angle')
    require(F(1, 3) * 3 + F(2, 3) * 2 == F(7, 3), 'mean query ledger')
    return {'status': 'passed', 'full_matrix_unit_CP_entries': len(left), 'exact_half_diamond_interval': [str(lo), str(hi)], 'mean_7over3_half_diamond_interval': [str(F(2, 3) * lo), str(F(2, 3) * hi)], 'scope': 'Exact Gaussian-Qsqrt2 finite CP, unitary, Choi-plane, algebraic interval and mean-ledger guards. Global diamond equality, arbitrary encoded multiplicity and bare-pulse restricted optimum remain analytic; no numerical comb optimum or all-ordinary converse.'}


def verify():
    activation = activation_ledger()
    require(activation.get("status") == "passed", "source activation ledger passed")
    return {
        "status": "passed",
        "pulse_identities": pulse_identities(),
        "ordinary_benchmark": ordinary_benchmark(),
        "ordinary_exact_query_certificate": exact_query_certificate(),
        "source_activation_cost_diagnostic": activation,
        "scope": "Exact finite pulse/Euler/flag/rollback and random-order Choi-plane/algebraic-interval ingredients; source-parameter scalar activation costs are separately labelled floating-point diagnostics. Universal timing/diamond proofs, any adaptive ordinary optimum and physical controls/noise/clocks remain separate."
    }


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True))
