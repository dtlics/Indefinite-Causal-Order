"""Exact finite checks for the sparse local Pauli-Lindblad scalar estimator.

Log eigenvalues are formal rational linear functions of rates. Separate
Bernoulli tests use rational t=exp(-2r); those r can be logarithmic. All-n,
conditioning, concentration and physical-model claims remain analytic.
"""
if not __debug__:
    raise RuntimeError("Run without -O: exact verification requires assertions")

from fractions import Fraction as F
import json


def chi(a, b, n):
    sign = 1
    for i in range(n):
        x, y = (a >> (2*i)) & 3, (b >> (2*i)) & 3
        if x and y and x != y:
            sign = -sign
    return sign


def generators(n, edges):
    return ([a << (2*i) for i in range(n) for a in (1, 2, 3)]
            + [(a << (2*i)) ^ (b << (2*j))
               for i, j in edges for a in (1, 2, 3) for b in (1, 2, 3)])


def invert(n, edges, logs, clip_pairs=False):
    rates = {}
    for i, j in edges:
        for a in (1, 2, 3):
            for b in (1, 2, 3):
                label = (a << (2*i)) ^ (b << (2*j))
                value = sum((logs[(u << (2*i)) ^ (v << (2*j))]
                             * chi(a, u, 1)*chi(b, v, 1)
                             for u in range(4) for v in range(4)), F(0))/16
                rates[label] = max(F(0), value) if clip_pairs else value
    for i in range(n):
        for a in (1, 2, 3):
            label = a << (2*i)
            value = sum((logs[u << (2*i)]*chi(a, u, 1)
                         for u in range(4)), F(0))/4
            for j, k in edges:
                if i in (j, k):
                    other = k if i == j else j
                    value -= sum((rates[label ^ (b << (2*other))]
                                  for b in (1, 2, 3)), F(0))
            rates[label] = value
    return rates


def law(gs, theta):
    result = {0: F(1)}
    for g, event in zip(gs, theta):
        updated = {}
        for label, probability in result.items():
            updated[label] = updated.get(label, F(0)) + probability*(1-event)
            flipped = label ^ g
            updated[flipped] = updated.get(flipped, F(0)) + probability*event
        result = updated
    assert sum(result.values(), F(0)) == 1
    return result


def eigenvalue(p, z, n):
    return sum((probability*chi(a, z, n) for a, probability in p.items()), F(0))


def eta(p, q, n):
    return sum((pa*qb*chi(a, b, n) for a, pa in p.items()
                for b, qb in q.items()), F(0))


def verify_lindblad_statistic():
    inversion_rates = perturb_rates = l1_cases = eigen_cases = scalar_cases = 0
    character_coefficients = tv_cases = 0
    graphs = ((1, ()), (2, ((0, 1),)),
              (3, ((0, 1), (1, 2))), (3, ((0, 1), (0, 2), (1, 2))))
    for n, edges in graphs:
        gs = generators(n, edges)
        rates = {g: F(0) if j % 5 == 0 else F(1+j % 4, 50)
                 for j, g in enumerate(gs)}
        probes = set(gs) | {0}
        logs = {z: sum((r*(chi(g, z, n)-1) for g, r in rates.items()), F(0))
                for z in probes}
        assert invert(n, edges, logs) == rates
        inversion_rates += len(gs)
        gamma, bound = F(1, 100), 3*n+27*len(edges)
        for seed in (0, 1):
            noisy = {z: value + (gamma*(-1)**(z+seed) if z else 0)
                     for z, value in logs.items()}
            for clip_pairs in (False, True):
                estimated = invert(n, edges, noisy, clip_pairs)
                for g in gs:
                    occupied = [i for i in range(n) if (g >> (2*i)) & 3]
                    degree = sum(occupied[0] in edge for edge in edges)
                    factor = 1 if len(occupied) == 2 else 1+3*degree
                    assert abs(estimated[g]-rates[g]) <= factor*gamma
                    perturb_rates += 1
                clipped = {g: max(F(0), r) for g, r in estimated.items()}
                assert sum((abs(clipped[g]-rates[g]) for g in gs), F(0)) <= bound*gamma
                assert all(abs(clipped[g]-rates[g]) <= abs(estimated[g]-rates[g])
                           for g in gs)
                l1_cases += 1
        # t is rational, while its integrated rate r=-log(t)/2 may not be.
        ts = [[F(4+j % 3, 8) for j in range(len(gs))],
              [F(3+j % 3, 7) for j in range(len(gs))]]
        distributions = [law(gs, [(1-t)/2 for t in row]) for row in ts]
        assert all(len(p) == 4**n and min(p.values()) > 0 for p in distributions)
        for row, p in zip(ts, distributions):
            for z in range(4**n):
                expected = F(1)
                for g, t in zip(gs, row):
                    if chi(g, z, n) == -1:
                        expected *= t
                assert eigenvalue(p, z, n) == expected
                eigen_cases += 1
        p, q = distributions
        assert eta(p, q, n) == sum((qb*eigenvalue(p, b, n)
                                    for b, qb in q.items()), F(0))
        scalar_cases += 1
        original = [(1-t)/2 for t in ts[0]]
        changed = [t+F((-1)**j, 200) for j, t in enumerate(original)]
        changed_law = law(gs, changed)
        tv = sum((abs(p[a]-changed_law[a]) for a in p), F(0))/2
        assert tv <= sum((abs(x-y) for x, y in zip(original, changed)), F(0))
        tv_cases += 1

    # Character projection checked on every Pauli coefficient. Linearity
    # extends this identity to every rational state and measurement operator.
    for n in (1, 2):
        labels = range(4**n)
        for z in labels:
            for t in labels:
                projection = F(sum(chi(r, z, n)*chi(r, t, n) for r in labels), 4**n)
                assert projection == F(z == t)
                for depth in (0, 1, 3):
                    eigen = F(2+(t % 3), 5)
                    assert projection*eigen**depth == F(z == t)*eigen**depth
                    character_coefficients += 1

    # H swaps X and Z: equal even-cycle orbit products do not determine
    # their individual eigenvalues or this task's scalar against fixed B.
    pa = law([1, 3], [F(1, 4), F(1, 8)])
    pa_prime = law([1, 3], [F(1, 8), F(1, 4)])
    qb = law([3], [F(1, 4)])
    ea = [eigenvalue(pa, z, 1) for z in (1, 2, 3)]
    eb = [eigenvalue(pa_prime, z, 1) for z in (1, 2, 3)]
    assert ea == [F(3, 4), F(3, 8), F(1, 2)]
    assert eb == [F(1, 2), F(3, 8), F(3, 4)]
    assert ea[0]*ea[2] == eb[0]*eb[2] and ea[1] == eb[1]
    assert eta(pa, qb, 1) == F(7, 8) and eta(pa_prime, qb, 1) == F(15, 16)
    return {
        "status": "passed", "arithmetic": "exact rational",
        "local_rate_inversion_coefficients": inversion_rates,
        "perturbed_rate_coordinate_bounds": perturb_rates,
        "rate_l1_and_clipping_cases": l1_cases,
        "bernoulli_factorized_eigenvalues": eigen_cases,
        "full_support_scalar_expectations": scalar_cases,
        "bernoulli_total_variation_couplings": tv_cases,
        "complete_spam_character_coefficients": character_coefficients,
        "clifford_orbit_identifiability_counterexample": True,
        "scope": ("Finite n=1,2,3 local-model identities and coefficient-complete SPAM "
                  "projection; all-n proofs, log conditioning, concentration, rate-to-event "
                  "Lipschitz, graph covers and physical access remain analytic.")
    }


if __name__ == "__main__":
    print(json.dumps(verify_lindblad_statistic(), sort_keys=True))
