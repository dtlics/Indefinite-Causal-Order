"""Exact finite partial-meter switch checks; oscillator physics is analytic.

Weights are rational Kraus probabilities, so no square-root rounding enters.
The continuum oscillator Gram/force proofs, diamond upper bound and physical
clock hypotheses remain in architecture-baselines.md. No optimum is tested.
"""
from fractions import Fraction as F
import json

if not __debug__:
    raise RuntimeError("Exact partial-meter checks require assertions.")


def zero(d):
    return [[F(0) for _ in range(d)] for _ in range(d)]


def eye(d):
    return [[F(x == y) for y in range(d)] for x in range(d)]


def scale(a, r):
    return [[r*x for x in row] for row in a]


def add(*arrays):
    return [[sum(items, F(0)) for items in zip(*rows)]
            for rows in zip(*arrays)]


def transpose(a):
    return list(map(list, zip(*a)))


def mul(a, b):
    d, out = len(a), zero(len(a))
    for x in range(d):
        for k in range(d):
            if a[x][k]:
                for y in range(d):
                    out[x][y] += a[x][k]*b[k][y]
    return out


def projectors(d, walsh=False):
    if not walsh:
        return [[[F(x == y == j) for y in range(d)] for x in range(d)]
                for j in range(d)]
    return [[[F((-1)**((j & x).bit_count()+(j & y).bit_count()), d)
              for y in range(d)] for x in range(d)] for j in range(d)]


def partial_terms(ps, r):
    return [(r, eye(len(ps)))] + [(1-r, p) for p in ps]


def block(data, terms_a, terms_b, left_control, right_control):
    """A full control-matrix block; no initial |+> assumption."""
    out = zero(len(data))
    for wa, ka in terms_a:
        for wb, kb in terms_b:
            left = mul(kb, ka) if left_control == 0 else mul(ka, kb)
            right = mul(kb, ka) if right_control == 0 else mul(ka, kb)
            out = add(out, scale(mul(mul(left, data), transpose(right)), wa*wb))
    return out


def verify_mechanical_pointer_strength():
    full_control_blocks = minus_laws = gram_eigenpairs = choi_eigenpairs = 0
    for d in (2, 4):
        ps = projectors(d)
        for r in (F(0), F(1, 4), F(3, 4), F(1)):
            # Purified thermal record Gram matrix (1-r)I+rJ.
            gram = [[F(x == y)*(1-r)+r for y in range(d)] for x in range(d)]
            vectors = [([F(1)]*d, 1+(d-1)*r)]
            for k in range(1, d):
                v = [F(0)]*d
                v[0], v[k] = F(1), F(-1)
                vectors.append((v, 1-r))
            for v, lam in vectors:
                assert [sum((gram[x][y]*v[y] for y in range(d)), F(0))
                        for x in range(d)] == [lam*x for x in v]
                gram_eigenpairs += 1
            # Nonzero Choi block of Id-Delta on |ii> support: (J-I)/d.
            choi = [[F(x != y, d) for y in range(d)] for x in range(d)]
            for v, _ in vectors:
                lam = F(d-1, d) if v == [F(1)]*d else F(-1, d)
                assert [sum((choi[x][y]*v[y] for y in range(d)), F(0))
                        for x in range(d)] == [lam*x for x in v]
                choi_eigenpairs += 1
            assert (F(d-1, d)+(d-1)*F(1, d))/2 == 1-F(1, d)

        for other_basis in (False, True):
            qs = projectors(d, other_basis)
            da, db = [(F(1), p) for p in ps], [(F(1), q) for q in qs]
            visibility = sum((sum((p[x][y]*q[y][x] for x in range(d)
                                  for y in range(d)), F(0))**2
                              for p in ps for q in qs), F(0))/d
            assert visibility == (F(1, d) if other_basis else F(1))
            # Full E_A,E_B switch minus unchanged-control serial output.
            # Every C,S matrix unit tests the reference-preserving channel.
            for ra, rb in ((F(0), F(0)), (F(1, 4), F(2, 3)),
                           (F(3, 4), F(1, 2)), (F(1), F(2, 3))):
                ta, tb = partial_terms(ps, ra), partial_terms(qs, rb)
                for cl in (0, 1):
                    for cr in (0, 1):
                        for x in range(d):
                            for y in range(d):
                                data = zero(d)
                                data[x][y] = F(1)
                                actual = add(block(data, ta, tb, cl, cr),
                                             scale(block(data, ta, tb, 0, 0), -1))
                                pure_difference = add(block(data, da, db, cl, cr),
                                                      scale(block(data, da, db, 0, 0), -1))
                                assert actual == scale(pure_difference, (1-ra)*(1-rb))
                                full_control_blocks += 1
                data = scale(eye(d), F(1, d))
                cross = block(data, ta, tb, 0, 1)
                tr_cross = sum((cross[k][k] for k in range(d)), F(0))
                q = (1-tr_cross)/2
                assert q == (1-ra)*(1-rb)*(1-visibility)/2
                for nu in (F(0), F(1, 3), F(1)):
                    assert (1-nu*tr_cross)/2 == (1-nu)/2+nu*q
                    minus_laws += 1

    # Exact rational *upper* bound p<=A, not a floating exp estimate.
    single_force_A = 4*F(1, 25)**2
    product_upper = single_force_A**2
    assert single_force_A == F(4, 625)
    assert product_upper == F(16, 390625)
    assert product_upper/2 == F(8, 390625)
    return {
        "status": "passed", "arithmetic": "exact rational matrices",
        "full_control_matrix_blocks": full_control_blocks,
        "same_mub_and_visibility_minus_laws": minus_laws,
        "record_gram_eigenpairs": gram_eigenpairs,
        "choi_witness_eigenpairs": choi_eigenpairs,
        "ideal_ground_state_force_product_upper": str(product_upper),
        "scope": ("Finite d=2,4 partial-dephaser/full-control identities and rational "
                  "force guards. Thermal Gaussian continuum, diamond bounds, statistical "
                  "launch law and actual hardware/time records remain analytic. No "
                  "optimal ordinary strategy, native advantage or priority claim.")
    }


if __name__ == '__main__':
    print(json.dumps(verify_mechanical_pointer_strength(), indent=2))
