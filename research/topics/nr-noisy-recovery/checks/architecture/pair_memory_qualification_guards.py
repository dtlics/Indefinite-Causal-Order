"""Exact ordinary dedicated-pair and parallel phase-memory ingredients.

Checks remain active under -O and import is quiet. No explicit data-file
I/O is performed; caller -B or its bytecode flag keeps module loading
cache-free. Channel/model, confidence and all-recovery proofs remain
analytic. Noise/SPAM/stationarity and physical control costs are premises.
"""
from fractions import Fraction as F
from itertools import product
from math import isqrt
from random import Random
import json
import sys

sys.dont_write_bytecode = True
from retained_photon_serial import G, add, adj, blockdiag, cp_equal, eye, kron, mm, require, scale, zeros

g = G
O, I = G(), G(1)
ID = eye(2)
X = [[O, I], [I, O]]
Y = [[O, G(0, -1)], [G(0, 1), O]]
Z = [[I, O], [O, G(-1)]]


def gadd(a, b):
    return a+b


def mul(a, b):
    return a*b


def cj(a):
    return a.conj()


def sc(a, x):
    return a*F(x)


def n2(a):
    return (a*a.conj()).r


def tensor(items):
    out = [[I]]
    for item in items:
        out = kron(out, item)
    return out


def diagonal_kraus_correlation(diagonals):
    """PSD is constructive: C_uv=sum_a k_a,u conj(k_a,v)."""
    dim = len(diagonals[0])
    c = [[sum((row[u]*row[v].conj() for row in diagonals), G())
          for v in range(dim)] for u in range(dim)]
    require(all(c[u][u] == 1 for u in range(dim)) and c == adj(c),
            "diagonal Kraus Gram has unit diagonal and is Hermitian")
    return c


def corr(terms):
    """A nonnegative mixture of unit-phase diagonals proves PSD by construction."""
    dim = len(terms[0][1])
    require(sum(p for p, _ in terms) == 1, "mixture normalization")
    c = zeros(dim)
    for p, phases in terms:
        require(p >= 0 and len(phases) == dim, "mixture weights/dimension")
        require(all(n2(x) == 1 for x in phases), "nonunit diagonal")
        for u, v in product(range(dim), repeat=2):
            c[u][v] = gadd(c[u][v], sc(mul(phases[u], cj(phases[v])), p))
    require(all(c[u][u] == I for u in range(dim)), "unit diagonal")
    require(all(c[u][v] == cj(c[v][u]) for u, v in product(range(dim), repeat=2)),
         "Hermitian correlation")
    return c


def mean(c, observable):
    # rho=E(|+...+><+...+|)=C/dim.
    result = O
    for u, v in product(range(len(c)), repeat=2):
        result = gadd(result, mul(c[u][v], observable[v][u]))
    result = sc(result, F(1, len(c)))
    require(result.i == 0, "nonreal observable mean")
    return result.r


def extract(c):
    a, b, cc, d = [mean(c, kron(p, q))
                   for p, q in ((X, X), (Y, Y), (X, Y), (Y, X))]
    return g(a-b, -cc-d), g(a+b, cc-d)


def rad(a=O, b=O, r=F(0)):
    """a+b*sqrt(r), Gaussian-rational coefficients; canonical for rational roots."""
    nr, dr = isqrt(r.numerator), isqrt(r.denominator)
    if nr*nr == r.numerator and dr*dr == r.denominator:
        return (gadd(a, sc(b, F(nr, dr))), O)
    return (a, b)


def ra(x, y, r):
    return rad(gadd(x[0], y[0]), gadd(x[1], y[1]), r)


def rm(x, y, r):
    return rad(gadd(mul(x[0], y[0]), sc(mul(x[1], y[1]), r)),
               gadd(mul(x[0], y[1]), mul(x[1], y[0])), r)


def rc(x, r):
    return rad(cj(x[0]), cj(x[1]), r)


def rs(x, scale, r):
    return rad(sc(x[0], scale), sc(x[1], scale), r)


def check_code(c, pair, inferred):
    u, v = pair
    require(c[u][v] == inferred, "complex parity extraction sign")
    require(n2(inferred) <= 1, "coherence disk")
    r = n2(inferred)
    one, root = rad(I, O, r), rad(O, I, r)
    # U=diag(1,L/|L|) removes the channel's off-diagonal phase.
    phase = one if r == 0 else rad(O, sc(inferred, 1/r), r)
    require(rm(phase, rc(phase, r), r) == one, "unitary phase correction")
    phases = [one, phase]
    fe_sum = rad(O, O, r)
    count = 0
    for i, j in product(range(2), repeat=2):
        physical = zeros(4)
        physical[pair[i]][pair[j]] = c[pair[i]][pair[j]]
        expected = zeros(4)
        coefficient = I if i == j else (inferred if i == 0 else cj(inferred))
        expected[pair[i]][pair[j]] = coefficient
        require(physical == expected, "encoded/reference matrix unit")
        post = rm(rm(phases[i], rad(coefficient, O, r), r), rc(phases[j], r), r)
        require(post == (one if i == j else root), "corrected coherence")
        fe_sum = ra(fe_sum, post, r)
        count += 1
    require(rs(fe_sum, F(1, 4), r) == rad(g(F(1, 2)), g(F(1, 2)), r),
         "optimal entanglement fidelity expression")
    return count


def marginal_pair(c, n, left, right):
    rest = [j for j in range(n) if j not in (left, right)]
    out = zeros(4)
    for a, b in product(range(4), repeat=2):
        for zbits in product((0, 1), repeat=len(rest)):
            us, vs = [0]*n, [0]*n
            us[left], us[right] = a >> 1, a & 1
            vs[left], vs[right] = b >> 1, b & 1
            for j, bit in zip(rest, zbits):
                us[j] = vs[j] = bit
            u = sum(bit << (n-1-j) for j, bit in enumerate(us))
            v = sum(bit << (n-1-j) for j, bit in enumerate(vs))
            out[a][b] = gadd(out[a][b], sc(c[u][v], F(1, 2**len(rest))))
    return out


def y_distribution(c, n):
    dim = 2**n
    minus_i = [I, g(0, -1), g(-1), g(0, 1)]
    result = []
    for x in range(dim):
        bra = [sc(minus_i[u.bit_count() % 4], (-1)**((x & u).bit_count()))
               for u in range(dim)]
        p = O
        for u, v in product(range(dim), repeat=2):
            p = gadd(p, mul(mul(bra[u], c[u][v]), cj(bra[v])))
        p = sc(p, F(1, dim*dim))
        require(p.i == 0 and p.r >= 0, "Y bitstring probability")
        result.append(p.r)
    require(sum(result) == 1, "Y distribution normalization")
    return result


def dedicated_pair_guards():
    fixtures = [corr([(F(1), [I]*4)]),
                corr([(F(1, 4), [g((-1)**((u & z).bit_count())) for u in range(4)])
                      for z in range(4)]),
                corr([(F(1), [I, g(0, 1), g(-1), g(F(3, 5), F(4, 5))])]),
                corr([(F(1, 2), [I]*4),
                      (F(1, 2), [I, g(0, 1), g(0, 1), g(-1)])])]
    rng = Random(173610)
    pool = [I, g(-1), g(0, 1), g(0, -1),
            g(F(3, 5), F(4, 5)), g(F(3, 5), F(-4, 5))]
    for _ in range(8):
        weights = [rng.randrange(1, 8) for _ in range(5)]
        den = sum(weights)
        fixtures.append(corr([(F(w, den), [rng.choice(pool) for _ in range(4)])
                              for w in weights]))
    general = diagonal_kraus_correlation([
        [G(1), G(), G(F(3, 5)), G(F(3, 5))],
        [G(), G(1), G(F(4, 5)), G(0, F(4, 5))]])
    require(general[2][3] == G(F(9, 25), F(-16, 25)) and general[0][1] == 0,
            "declared general complex Schur Gram and zero coherence")
    fixtures.extend([general, corr([(F(1), [I, I, I, g(-1)])])])
    units = single_means = 0
    for c in fixtures:
        lp, lm = extract(c)
        units += check_code(c, (0, 3), lp)
        units += check_code(c, (1, 2), lm)
        for pair in ((0, 2), (1, 3), (0, 1), (2, 3)):
            u, v = pair
            units += check_code(c, pair, c[u][v])
            rho = zeros(4)
            for a, b in product(pair, repeat=2):
                rho[a][b] = c[a][b]/2
            for pauli, expected in ((X, c[u][v].r), (Y, -c[u][v].i)):
                observable = kron(pauli, ID) if u ^ v == 2 else kron(ID, pauli)
                measured = sum((rho[a][b]*observable[b][a] for a, b in product(range(4), repeat=2)), G())
                require(measured == expected, "targeted context-specific single Ramsey mean")
                single_means += 1
    cycle = [I, g(0, -1), g(-1), g(0, 1)]
    signs = [(1, 1, -1, -1), (1, -1, 1, -1)]
    large, distributions, pairs = [], [], []
    for ss in signs:
        diag = []
        for u in range(16):
            charge = sum(ss[j]*(1-2*((u >> (3-j)) & 1)) for j in range(4))
            require(charge % 2 == 0, "even charge")
            diag.append(cycle[(charge//2) % 4])
        c = corr([(F(1, 2), [I]*16), (F(1, 2), diag)])
        large.append(c)
        distributions.append(y_distribution(c, 4))
        pair = marginal_pair(c, 4, 0, 1)
        pairs.append(extract(pair))
    require(pairs == [(g(), I), (I, g())], "opposite labelled DFS decisions")
    def swap23(u):
        return u ^ 6 if ((u >> 2) ^ (u >> 1)) & 1 else u
    for u, v in product(range(16), repeat=2):
        require(large[1][u][v] == large[0][swap23(u)][swap23(v)],
             "complete four-qubit state permutation")
    for c in large:
        require(mean(c, tensor([X, X, ID, ID])) == F(1, 2), "pair XX")
        # All 16 coefficients of (aX+bY)^tensor4, not an angle-grid proof.
        for word in product((0, 1), repeat=4):
            expected = F(1, 2) if sum(word) in (0, 4) else F(0)
            require(mean(c, tensor([Y if bit else X for bit in word])) == expected,
                 "exact all-angle global-parity polynomial coefficient")
        for a, b in ((F(1), F(0)), (F(0), F(1)), (F(3, 5), F(4, 5))):
            m = [[O, g(a, -b)], [g(a, b), O]]
            require(mean(c, tensor([m]*4)) == (a**4+b**4)/2, "global parity line")
    for index, probs in zip((3, 5), distributions):
        require(probs == [F(17, 32) if x == index else F(1, 32) for x in range(16)],
             "full labelled Y bitstrings")
        require(sum((-1)**x.bit_count()*p for x, p in enumerate(probs)) == F(1, 2),
             "global YYYY normalization")
    yy = [sum((-1)**(((x >> 3) & 1)+((x >> 2) & 1))*p
              for x, p in enumerate(probs)) for probs in distributions]
    require(yy == [F(1, 2), F(-1, 2)], "same-record pair YY")
    tv = sum(abs(a-b) for a, b in zip(*distributions))/2
    require(tv == F(1, 2), "labelled distribution distinguishability")
    return {"status": "passed", "PSD_unit_diagonal_fixtures": len(fixtures),
            "general_diagonal_Kraus_Gram_fixtures": 1,
            "declared_codes_per_fixture": 6, "encoded_reference_matrix_units": units,
            "pair_setting_means": 4*len(fixtures), "contextual_single_setting_means": single_means,
            "four_qubit_labelled_models": 2, "full_state_permutation_entries": 256,
            "global_parity_polynomial_words_per_model": 16, "full_Y_bitstrings_per_model": 16,
            "global_YYYY_mean": "1/2", "pair_YY_means": ["1/2", "-1/2"],
            "labelled_distribution_total_variation": "1/2",
            "scope": "finite Schur pair/spectator-context channel, phase-score and full-record ingredients; no full Schur tomography, spectator-independent general bath, noise-model or architecture-optimum certificate"}


def recovery_parseval_guards():
    """Finite identities used in the separate analytic CPTP recovery bound."""
    recoveries = [([ID], "identity"), ([X], "Pauli"),
                  ([[[G(1), G()], [G(), G(F(3, 5))]],
                    [[G(), G(F(4, 5))], [G(), G()]]], "amplitude damping"),
                  ([scale(ID, F(3, 5)), scale(Z, F(4, 5))], "phase mixture"),
                  ([[[G(F(3, 5)), G(F(4, 5))],
                     [G(F(-4, 5)), G(F(3, 5))]]], "rotation")]
    cases = 0
    for kraus, label in recoveries:
        effect = zeros(2)
        for a in kraus:
            effect = add(effect, mm(adj(a), a))
            norm = sum((n2(value) for row in a for value in row), F())
            traces = []
            for p in (ID, X, Y, Z):
                ap = mm(a, p)
                traces.append(n2(ap[0][0]+ap[1][1]))
            require(sum(traces) == 2*norm, "Pauli Parseval per Kraus operator")
        require(effect == ID, "declared recovery is trace preserving: "+label)
        weights = []
        for p in (ID, X, Y, Z):
            weights.append(sum((n2(mm(a, p)[0][0]+mm(a, p)[1][1])/4 for a in kraus), F()))
        require(sum(weights) == 1 and all(w >= 0 for w in weights), "normalized Bell/Parseval weights")
        for p in (F(1, 2), F(3, 5), F(1)):
            require(p*weights[0]+(1-p)*weights[3] <= p,
                    "aligned dephasing recovery score ingredient")
            cases += 1
    return {"status": "passed", "recovery_fixtures": len(recoveries),
            "aligned_score_ingredients": cases,
            "scope": "finite Parseval/normalization ingredients; the any-CPTP recovery theorem remains analytic"}


def parallel_phase_guards():
    n, edges = 3, [(0, 1), (1, 2)]
    law = [(F(1, 3), [G(1), G(0, 1), G(0, -1)]),
           (F(1, 6), [G(F(3, 5), F(-4, 5)), G(F(3, 5), F(-4, 5)), G(-1)]),
           (F(1, 2), [G(0, -1), G(0, 1), G(F(5, 13), F(12, 13))])]
    require(sum(w for w, _ in law) == 1, "probability law")
    require(all(z*z.conj() == 1 for _, zs in law for z in zs), "unit phase fixtures")
    catalogue = [(j,) for j in range(n)]+[(j, k, sign) for j, k in edges for sign in (1, -1)]

    def multiplier(q, zs):
        return zs[q[0]] if len(q) == 1 else zs[q[0]]*(zs[q[1]] if q[2] == 1 else zs[q[1]].conj())

    target = [sum((w*multiplier(q, zs) for w, zs in law), G()) for q in catalogue]
    measured = [G() for _ in catalogue]
    total_probability = F()
    events = 0
    for w, zs in law:
        for axes in product(("X", "Y"), repeat=n):
            for bits in product((1, -1), repeat=n):
                prob = w/F(2**n)
                for axis, bit, z in zip(axes, bits, zs):
                    prob *= (1+bit*(z.r if axis == "X" else -z.i))/2
                require(prob >= 0, "conditional product probabilities")
                total_probability += prob
                for index, q in enumerate(catalogue):
                    j = q[0]
                    if len(q) == 1:
                        value = G(2*bits[j]) if axes[j] == "X" else G(0, -2*bits[j])
                    else:
                        k, sign = q[1:]
                        r, a = bits[j]*bits[k], axes[j]+axes[k]
                        if a == "XX":
                            value = G(4*r)
                        elif a == "YY":
                            value = G(-4*r if sign == 1 else 4*r)
                        elif a == "XY":
                            value = G(0, -4*r if sign == 1 else 4*r)
                        else:
                            value = G(0, -4*r)
                    require(-4 <= value.r <= 4 and -4 <= value.i <= 4, "component range")
                    measured[index] += prob*value
                events += 1
    require(total_probability == 1 and measured == target, "all simultaneous estimator expectations")

    channel_units = 0
    for q, coherence in zip(catalogue, target):
        size = 2 if len(q) == 1 else 4
        code = eye(2) if size == 2 else zeros(4, 2)
        if size == 4:
            for bit in range(2):
                code[2*bit+(bit if q[2] == 1 else 1-bit)][bit] = G(1)
        kraus = []
        for weight, zs in law:
            if size == 2:
                unitary = [[zs[q[0]], G()], [G(), G(1)]]
            else:
                j, k = q[:2]
                unitary = zeros(4)
                for a, b in product(range(2), repeat=2):
                    unitary[2*a+b][2*a+b] = (zs[j] if a == 0 else G(1))*(zs[k] if b == 0 else G(1))
            kraus.append((weight, mm(unitary, code)))
        for i, j in product(range(2), repeat=2):
            factor = G(1) if i == j else (coherence if i == 0 else coherence.conj())
            for row, col in product(range(size), repeat=2):
                actual = sum((w*k[row][i]*k[col][j].conj() for w, k in kraus), G())
                require(actual == factor*code[row][i]*code[col][j].conj(),
                        "complete encoded/reference Eij map")
            channel_units += 1
    # The exact factors in the requested component-Hoeffding calculation.
    require(F(2, 8**2)*F(1, 2) == F(1, 64), "epsilon complex-error exponent")
    require(2*2*len(catalogue) == 4*(n+2*len(edges)), "two tails/components union factor")

    def regret_case(true, cal, estimates, true_radii, estimated_radii, epsilon, kappa):
        for t, c, h, tr, hr in zip(true, cal, estimates, true_radii, estimated_radii):
            require(t*t.conj() == tr*tr and h*h.conj() == hr*hr, "exact catalogue radii")
            require(((h-c)*(h-c).conj()).r <= epsilon*epsilon
                    and ((c-t)*(c-t).conj()).r <= kappa*kappa, "uniform error and drift")
        chosen = max(range(len(estimates)), key=lambda i: estimated_radii[i])
        radius = estimated_radii[chosen]
        correction = estimates[chosen].conj()/radius if radius else G(1)
        score = (correction*true[chosen]).r
        require((max(true_radii)-score)/2 <= epsilon+kappa, "actual production Fe regret")
        require(radius-epsilon-kappa <= score
                and max(true_radii) <= radius+epsilon+kappa, "fidelity certificate")

    regret_case([G(F(2, 5)), G(F(4, 5))], [G(F(2, 5)), G(F(4, 5))],
                [G(F(3, 5)), G(F(3, 5))], [F(2, 5), F(4, 5)], [F(3, 5)]*2, F(1, 5), F())
    regret_case([G(0, F(1, 10))], [G(0, F(1, 10))], [G()], [F(1, 10)], [F()], F(1, 10), F())
    regret_case([G(F(3, 5), F(4, 5))], [G(F(3, 5), F(4, 5))],
                [G(F(3, 10), F(2, 5))], [F(1)], [F(1, 2)], F(1, 2), F())
    regret_case([G(F(2, 5)), G(F(4, 5))], [G(F(3, 5))]*2,
                [G(F(3, 5))]*2, [F(2, 5), F(4, 5)], [F(3, 5)]*2, F(), F(1, 5))

    regret_case([G(F(1, 5)), G(F(4, 5))], [G(F(1, 5)), G(F(4, 5))],
                [G(F(1, 5)), G(F(4, 5))], [F(1, 5), F(4, 5)], [F(1, 5), F(4, 5)], F(), F())

    # Equal local marginals need not fix which parity code is useful.
    roots = [G(1), G(0, 1), G(-1), G(0, -1)]
    common_plus = sum((z*z for z in roots), G())/4
    common_minus = sum((z*z.conj() for z in roots), G())/4
    require(sum(roots, G()) == 0 and common_plus == 0 and common_minus == 1,
            "common phase has zero singles but a protected odd code")
    require(sum((z*z.conj() for z in roots), G())/4 == 1
            and sum((z*z for z in roots), G())/4 == 0,
            "opposite phase instead protects the even code")
    cz = corr([(F(1), [G(1), G(1), G(1), G(-1)])])
    require(cz[0][2] == 1 and cz[1][3] == -1
            and (cz[0][2]+cz[1][3])/2 == 0,
            "actual CZ Schur map has incompatible fixed and plus-spectator single multipliers")

    # Independent diagonal channel SWITCHes factor the control exactly.
    da = [[[G(F(3, 5)), G()], [G(), G(1)]], [[G(F(4, 5)), G()], [G(), G()]]]
    db = [[[G(1), G()], [G(), G(F(5, 13))]], [[G(), G()], [G(), G(F(12, 13))]]]
    for family in (da, db):
        effect = zeros(2)
        for a in family:
            effect = add(effect, mm(adj(a), a))
        require(effect == eye(2), "declared diagonal channel is trace preserving")
    switch_units = 0
    switch_effect = zeros(4)
    for a in da:
        for b in db:
            switched = blockdiag(mm(b, a), mm(a, b))
            ordinary = kron(eye(2), mm(b, a))
            require(mm(a, b) == mm(b, a) and switched == ordinary,
                    "abstract independent diagonal SWITCH keeps the full control register")
            switch_units += cp_equal(switched, ordinary)
            switch_effect = add(switch_effect, mm(adj(switched), switched))
    require(switch_effect == eye(4), "full control/data SWITCH is complete")
    # Persistent shared-bath completion is a different interface.
    identity, x, z = eye(2), [[G(), G(1)], [G(1), G()]], [[G(1), G()], [G(), G(-1)]]
    an = add(eye(4), scale(kron(z, x), G(0, -1)))
    bn = add(eye(4), scale(kron(z, z), G(0, -1)))
    require(mm(adj(an), an) == scale(eye(4), 2)
            and mm(adj(bn), bn) == scale(eye(4), 2), "shared-bath contacts after sqrt2 normalization")
    for unitary_n in (an, bn):
        for i, j, row, col in product(range(2), repeat=4):
            actual = sum((unitary_n[2*row+eo][2*i+ei]*unitary_n[2*col+eo][2*j+ei].conj()/4
                          for ei, eo in product(range(2), repeat=2)), G())
            require(actual == G(int(row == i and col == j))*F(1 if i == j else 0),
                    "each reduced shared-bath map is complete Z dephasing")
    minus = scale(add(mm(bn, an), scale(mm(an, bn), -1)), F(1, 4))
    require(mm(adj(minus), minus) == scale(eye(4), F(1, 4)),
            "same reduced diagonal maps do not fix shared-bath SWITCH control")
    return {"status": "passed", "sites": n, "eligible_edges": len(edges),
            "catalogue_size": len(catalogue), "enumerated_axis_outcome_phase_events": events,
            "encoded_reference_matrix_units": channel_units, "exact_regret_fixtures": 5,
            "independent_diagonal_SWITCH_control_input_matrix_units": switch_units,
            "shared_bath_minus_probability": "1/4",
            "scope": "declared classical-phase and exact statistical-constant ingredients only; general proof, iid/noise/SPAM premises, real costs and hardware interfaces are not certified"}


def verify():
    return {"status": "passed", "arithmetic": "exact Gaussian and quadratic rationals",
            "dedicated_pair": dedicated_pair_guards(),
            "recovery_parseval": recovery_parseval_guards(),
            "parallel_classical_phase": parallel_phase_guards(),
            "scope": "exact finite ordinary-memory calibration ingredients under two distinct declared models. General Schur/code/recovery and statistical proofs remain analytic; SPAM, launch independence, production matching, gates, reset, memory and physical time are premises, not hardware certificates."}


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True))
