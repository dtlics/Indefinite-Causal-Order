"""Finite exact guards for measured reflection/noise order on commuting inputs.

Uses the existing Gaussian-rational engine. All general CPTP, reference,
pinching-norm and physical-access statements remain analytic.
"""
from verify_fault_simulation import (F, ZERO, ONE, gaussian, add, times,
                                     zeros, identity, adjoint, matmul, tensor,
                                     require)


def plus(a, b):
    return [[add(x, y) for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def scale(a, c):
    return [[times(x, c) for x in row] for row in a]


def mu(n, i, j):
    a = zeros(n, n)
    a[i][j] = ONE
    return a


def tr(a):
    z = ZERO
    for i in range(len(a)):
        z = add(z, a[i][i])
    return z


def image(ks, a):
    out = zeros(len(ks[0]), len(ks[0]))
    for k in ks:
        out = plus(out, matmul(matmul(k, a), adjoint(k)))
    return out


def projectors(v):
    return {s: scale(plus(identity(len(v)), scale(v, s)), F(1, 2))
            for s in (1, -1)}


def switched(ks, v, rho, rdim=1):
    out = {}
    for s in (1, -1):
        ls = [tensor(scale(plus(matmul(v, k), scale(matmul(k, v), s)),
                           F(1, 2)), identity(rdim)) for k in ks]
        out[s] = image(ls, rho)
    return out


def ordinary(ks, v, rho, rdim=1):
    ps = projectors(v)
    er = [tensor(k, identity(rdim)) for k in ks]
    out = {s: zeros(len(rho), len(rho)) for s in (1, -1)}
    records = {}
    for p in (1, -1):
        pv = tensor(ps[p], identity(rdim))
        mid = image(er, matmul(matmul(pv, rho), pv))
        for y in (1, -1):
            py = tensor(ps[y], identity(rdim))
            leaf = matmul(matmul(py, mid), py)
            records[(p, y)] = leaf
            out[p * y] = plus(out[p * y], leaf)
    return out, records


def outer(v):
    col = [[x] for x in v]
    return matmul(col, adjoint(col))


def verify():
    z = [[ONE, ZERO], [ZERO, gaussian(-1)]]
    tilted = [[gaussian(F(3, 5)), gaussian(0, F(-4, 5))],
              [gaussian(0, F(4, 5)), gaussian(F(-3, 5))]]
    unitary = [[gaussian(F(3, 5)), gaussian(0, F(4, 5))],
               [gaussian(0, F(4, 5)), gaussian(F(3, 5))]]
    ad0 = [[ONE, ZERO], [ZERO, gaussian(F(3, 5))]]
    ad1 = [[ZERO, gaussian(F(4, 5))], [ZERO, ZERO]]
    ad = [ad0, ad1]
    ad_rot = [matmul(unitary, k) for k in ad]
    v3 = identity(3)
    v3[2][2] = gaussian(-1)
    u3 = identity(3)
    for i, j, x in ((0, 0, gaussian(F(3, 5))),
                    (0, 2, gaussian(0, F(4, 5))),
                    (2, 0, gaussian(0, F(4, 5))),
                    (2, 2, gaussian(F(3, 5)))):
        u3[i][j] = x
    a3 = identity(3)
    a3[2][2] = gaussian(F(3, 5))
    b3 = zeros(3, 3)
    b3[0][2] = gaussian(F(4, 5))
    ad3 = [matmul(u3, a3), matmul(u3, b3)]
    fixtures = [(z, ad), (tilted, ad_rot), (v3, ad3),
                (identity(2), ad), (scale(identity(2), -1), ad)]
    mixed_cases = reference_cases = fixed_sector_cases = 0
    for v, ks in fixtures:
        d = len(v)
        require(adjoint(v) == v and matmul(v, v) == identity(d),
                'V is not a Hermitian reflection')
        eff = zeros(d, d)
        for k in ks:
            eff = plus(eff, matmul(adjoint(k), k))
        require(eff == identity(d), 'E is not trace preserving')
        rho = scale(identity(d), F(1, d))
        native = switched(ks, v, rho)
        classical, records = ordinary(ks, v, rho)
        require(native == classical, 'maximally mixed full output mismatch')
        require(add(tr(native[1]), tr(native[-1])) == ONE,
                'complete flag probabilities not normalized')
        ps = projectors(v)
        ei, ev = image(ks, identity(d)), image(ks, v)
        for s in (1, -1):
            formula = scale(plus(plus(matmul(matmul(v, ei), v), ei),
                                 scale(plus(matmul(v, ev), matmul(ev, v)), s)),
                            F(1, 4 * d))
            require(native[s] == formula, 'four-term switched identity')
            require(add(tr(native[s]), ZERO) ==
                    add(tr(records[(s, 1)]), tr(records[(-s, -1)])),
                    'destructive (s,y) record law')
            mixed_cases += 1
        for p in (1, -1):
            rank = tr(ps[p])
            require(rank[1] == 0 and 0 <= rank[0] <= d, 'invalid spectral rank')
            if rank == ZERO:
                continue
            # Projected matrix units span the whole sector, including complex
            # within-sector reference correlations and nonpositive units.
            pr = tensor(ps[p], identity(2))
            for i in range(2 * d):
                for j in range(2 * d):
                    x = matmul(matmul(pr, mu(2 * d, i, j)), pr)
                    if x == zeros(2 * d, 2 * d):
                        continue
                    native = switched(ks, v, x, 2)
                    classical, _ = ordinary(ks, v, x, 2)
                    require(native == classical, 'commuting input/reference map')
                    for s in (1, -1):
                        py = tensor(ps[s * p], identity(2))
                        final = matmul(matmul(py, image([tensor(k, identity(2))
                                                        for k in ks], x)), py)
                        require(native[s] == final, 'fixed-sector final-only check')
                        fixed_sector_cases += 1
                    reference_cases += 1
    # A positive, complex, reference-entangled state in a degenerate sector.
    ket = [ZERO] * 6
    ket[0], ket[3] = gaussian(F(3, 5)), gaussian(0, F(4, 5))
    rho = plus(scale(outer(ket), F(3, 4)), scale(mu(6, 5, 5), F(1, 4)))
    require(tr(rho) == ONE, 'complex correlated state normalization')
    require(switched(ad3, v3, rho, 2) == ordinary(ad3, v3, rho, 2)[0],
            'degenerate-sector entanglement not preserved')
    # Off-sector coherence is outside the equality. This also saturates the
    # state pinching bound: epsilon=16/25, offdiagonal norm=12/25.
    psi = [gaussian(F(3, 5)), gaussian(0, F(4, 5))]
    rho = outer(psi)
    native = switched([identity(2)], z, rho)
    classical, _ = ordinary([identity(2)], z, rho)
    diff = plus(native[1], scale(classical[1], -1))
    require(diff != zeros(2, 2) and tr(diff) == ZERO, 'scope counterexample absent')
    require(matmul(diff, diff) == scale(identity(2), F(144, 625)),
            'pinching-distance saturation failed')
    # Retained order control is stronger than its measured-X classical output.
    u = [[gaussian(F(3, 5)), gaussian(F(4, 5))],
         [gaussian(F(-4, 5)), gaussian(F(3, 5))]]
    w0, w1 = matmul(z, u), matmul(u, z)
    raw = zeros(4, 4)
    for b, wb in enumerate((w0, w1)):
        for c, wc in enumerate((w0, w1)):
            block = scale(matmul(wb, adjoint(wc)), F(1, 4))
            for i in range(2):
                for j in range(2):
                    raw[2 * b + i][2 * c + j] = block[i][j]
    y = [[ZERO, gaussian(0, -1)], [gaussian(0, 1), ZERO]]
    require(tr(matmul(tensor(y, y), raw)) == gaussian(F(24, 25)),
            'retained-control witness missing')
    return {'status': 'passed', 'mixed_flag_outputs': mixed_cases,
            'commuting_reference_projected_units': reference_cases,
            'fixed_sector_final_only_outputs': fixed_sector_cases,
            'complex_degenerate_sector_state': True,
            'offsector_pinching_bound_saturated': '12/25',
            'retained_control_Y_Y_witness': '24/25',
            'scope': 'Finite exact reflection/CPTP fixtures only; universal identities, trace-norm bound and physical spectral-instrument access analytic.'}


if __name__ == '__main__':
    import json
    print(json.dumps(verify(), sort_keys=True))
