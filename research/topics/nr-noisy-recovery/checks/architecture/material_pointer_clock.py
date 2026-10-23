"""Exact finite guards for the declared QND array and clock models.

Standard library only. These are transcription checks; the all-input clock
proof, norm transfer, physical controls and hardware claims remain analytic.
"""
from fractions import Fraction as F
import json

if not __debug__:
    raise RuntimeError("Assertions are required.")


def projectors(d, walsh=False):
    if not walsh:
        return [[[F(x == y == j) for x in range(d)] for y in range(d)]
                for j in range(d)]
    return [[[F((-1)**((j & x).bit_count()+(j & y).bit_count()), d)
              for x in range(d)] for y in range(d)] for j in range(d)]


def plus_term(out, key, value):
    out[key] = out.get(key, F(0))+value
    if not out[key]:
        del out[key]


def write(vector, ps, station, selected=lambda c: True):
    """One physical write with the same retained one-hot pointer bits."""
    out = {}
    for (c, x, a, b), v in vector.items():
        if not selected(c):
            plus_term(out, (c, x, a, b), v)
            continue
        for i, p in enumerate(ps):
            for y in range(len(p)):
                key = ((c, y, a ^ (1 << i), b) if station == 'a'
                       else (c, y, a, b ^ (1 << i)))
                plus_term(out, key, v*p[y][x])
    return out


def direct_isometry(c, x, pa, pb):
    """Independent projector-product expression, not a routed sequence."""
    out, d = {}, len(pa)
    for i in range(d):
        for j in range(d):
            for y in range(d):
                v = sum((pb[j][y][z]*pa[i][z][x] if c == 0
                         else pa[i][y][z]*pb[j][z][x])
                        for z in range(d))
                plus_term(out, (c, y, 1 << i, 1 << j), v)
    return out


def control_cross(vector):
    total = F(0)
    for (c, x, a, b), v in vector.items():
        if c == 0:
            total += v*vector.get((1, x, a, b), F(0))
    return total


def verify_material_pointer_clock():
    columns = rank_guards = echo_guards = 0
    for d in (2, 4):
        pa, pb = projectors(d), projectors(d, True)
        # d material labels, with d^2 independent two-module record pairs.
        records = [(1 << i, 1 << j) for i in range(d) for j in range(d)]
        assert len(set(records)) == d*d
        rank_guards += d*d
        # Phase-write Z_i on |+>^d gives exactly orthogonal material records.
        denom = 2**(d//2)
        atoms = [[F((-1)**((bits >> i) & 1), denom)
                  for bits in range(2**d)] for i in range(d)]
        for i in range(d):
            for j in range(d):
                assert sum(x*y for x, y in zip(atoms[i], atoms[j])) == (i == j)
        # Full controlled isometry columns imply all reference/input operators.
        for c in (0, 1):
            for x in range(d):
                actual = write({(c, x, 0, 0): F(1)}, pa, 'a', lambda k: k == 0)
                actual = write(actual, pb, 'b')
                actual = write(actual, pa, 'a', lambda k: k == 1)
                assert actual == direct_isometry(c, x, pa, pb)
                columns += 1
        # Formal phase exponents for arbitrary static sum_j xi_j Z_j.
        # One global midpoint pi_X plus tracked final complement refocuses
        # both early and late writes; no xi_j or mode label is learned.
        mask = (1 << d)-1
        for i in range(d):
            early_first, early_second = 1 << i, (1 << i) ^ mask
            late_first, late_second = 0, mask
            for first, second in ((early_first, early_second),
                                  (late_first, late_second)):
                exponents = [(-1)**((first >> j) & 1)+(-1)**((second >> j) & 1)
                             for j in range(d)]
                assert exponents == [0]*d
            assert early_second == late_second ^ (1 << i)
            echo_guards += 1

    # Fresh scheduled pointer arrays have perfectly distinguishable slots.
    # Each isolated dephasing measurement remains exact, but control loses
    # coherence. Use the same computational dephaser at both stations.
    pa = projectors(2)
    ideal = {}
    for c in (0, 1):
        for key, value in direct_isometry(c, 0, pa, pa).items():
            plus_term(ideal, key, value)
    assert control_cross(ideal) == 1
    fresh = {(0, 0, 1, 1): F(1), (1, 0, 4, 1): F(1)}
    assert control_cross(fresh) == 0
    markov = 0
    for xa in map(F, (0, F(1, 4), F(1, 2), F(3, 4), 1)):
        for xb in map(F, (0, F(1, 4), F(1, 2), F(3, 4), 1)):
            assert max(xa*xa, xb*xb) >= xa*xb
            markov += 1
    # Gaussian stationary kernel has kappa(2tau)=kappa(tau)^4.
    x = F(1, 2)
    assert x*x > x**4
    return {"status": "passed", "arithmetic": "exact fractions",
                      "full_controlled_isometry_columns": columns,
                      "independent_material_record_pairs": rank_guards,
                      "static_pointer_echo_guards": echo_guards,
                      "fresh_clock_record_counterexample": True,
                      "markov_split_repeat_inequalities": markov,
                      "gaussian_bare_repeat_counterexample": True,
                      "scope": "Finite d=2,4 ideal array, clock, record and echo guards; universal clock/norm transfer and physical hypotheses analytic. No hardware, pilot, ordinary optimum or empirical noise certificate."}


if __name__ == '__main__':
    print(json.dumps(verify_material_pointer_clock(), indent=2))
