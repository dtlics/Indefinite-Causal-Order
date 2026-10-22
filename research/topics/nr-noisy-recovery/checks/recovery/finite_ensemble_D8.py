"""Exact finite-ensemble and payoff reduction; no optimization dependencies.

This script derives an operational corollary of the separately certified
D8, gamma=1/10 gate-product frontier. It does not replace that certificate.
The D8 source replay checks the quantum causal-comb inequality.
"""
if not __debug__:
    raise RuntimeError('Exact finite-ensemble checks require Python without -O.')

from fractions import Fraction as F
import itertools
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ZERO = (0, 0)
ONE = (1, 0)


def gadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def gmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def scale(a, s):
    return [[(s * z[0], s * z[1]) for z in row] for row in a]


def add(a, b):
    return [[gadd(x, y) for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]


def eye(n):
    return [[ONE if i == j else ZERO for j in range(n)] for i in range(n)]


def matmul(a, b):
    rows, inner, cols = len(a), len(b), len(b[0])
    return [[(sum(a[i][k][0] * b[k][j][0] - a[i][k][1] * b[k][j][1]
                  for k in range(inner)),
              sum(a[i][k][0] * b[k][j][1] + a[i][k][1] * b[k][j][0]
                  for k in range(inner))) for j in range(cols)] for i in range(rows)]


def kron(a, b):
    return [[gmul(a[i][j], b[k][l])
             for j in range(len(a[0])) for l in range(len(b[0]))]
            for i in range(len(a)) for k in range(len(b))]


def gf8_mul(a, b):
    out = 0
    while b:
        if b & 1:
            out ^= a
        b >>= 1
        a <<= 1
        if a & 8:
            a ^= 0b1011  # x^3+x+1
    return out


def gf8_trace(a):
    a2 = gf8_mul(a, a)
    ans = a ^ a2 ^ gf8_mul(a2, a2)
    assert ans in (0, 1)
    return ans


def slope_z(s, x):
    return sum(gf8_trace(gf8_mul(1 << i, gf8_mul(s, x))) << i for i in range(3))


def symplectic(a, b):
    x, z = a
    y, w = b
    return ((x & w).bit_count() + (z & y).bit_count()) % 2


def pauli(x, z):
    ident = eye(2)
    px = [[ZERO, ONE], [ONE, ZERO]]
    py = [[ZERO, (0, -1)], [(0, 1), ZERO]]
    pz = [[ONE, ZERO], [ZERO, (-1, 0)]]
    a = [[ONE]]
    for i in range(3):
        a = kron(a, {(0, 0): ident, (1, 0): px, (0, 1): pz, (1, 1): py}[
            ((x >> i) & 1, (z >> i) & 1)])
    return a


def finite_ensemble():
    """72 rank-one projectors from a complete set of nine 3-qubit MUBs.

    All matrix arithmetic here is exact Gaussian-integer arithmetic.
    N below equals 8 times a pure-state projector.
    """
    D = 8
    I = eye(D)
    classes = [([(1 << i, slope_z(s, 1 << i)) for i in range(3)],
                [(x, slope_z(s, x)) for x in range(1, 8)]) for s in range(8)]
    classes.append(([(0, 1 << i) for i in range(3)], [(0, z) for z in range(1, 8)]))
    all_members = [x for _, members in classes for x in members]
    assert len(set(all_members)) == 63
    assert set(all_members) == {(x, z) for x in range(8) for z in range(8)
                                if x or z}
    projectors = []
    for basis, (generators, members) in enumerate(classes):
        assert all(symplectic(a, b) == 0 for a in members for b in members)
        matrices = [pauli(*g) for g in generators]
        assert all(matmul(g, g) == I for g in matrices)
        assert all(matmul(a, b) == matmul(b, a) for a in matrices for b in matrices)
        for signs in itertools.product((-1, 1), repeat=3):
            N = I
            for sign, g in zip(signs, matrices):
                N = matmul(N, add(I, scale(g, sign)))
            assert matmul(N, N) == scale(N, D)
            assert sum(N[i][i][0] for i in range(D)) == D
            assert sum(N[i][i][1] for i in range(D)) == 0
            projectors.append((basis, signs, N))
    # First and second exact moments, with denominators removed.
    first = [[ZERO for _ in range(D)] for _ in range(D)]
    second = [[ZERO for _ in range(D * D)] for _ in range(D * D)]
    for _, _, N in projectors:
        first = add(first, N)
        second = add(second, kron(N, N))
    assert first == scale(I, 72)
    swap = [[ONE if i // D == j % D and i % D == j // D else ZERO
             for j in range(D * D)] for i in range(D * D)]
    assert second == scale(add(eye(D * D), swap), D * D)
    # Verify all cross-basis overlaps exactly, without eigenvectors.
    for bi, _, N in projectors:
        for bj, _, M in projectors:
            product = matmul(N, M)
            tr = (sum(product[i][i][0] for i in range(D)),
                  sum(product[i][i][1] for i in range(D)))
            assert tr[1] == 0
            if bi != bj:
                assert tr[0] == D
            else:
                assert tr[0] in (0, D * D)
    return {
        "dimension": D, "bases": 9, "states": 72,
        "arithmetic": "exact Gaussian integers",
        "rank_one_projectors": "N^2=8N and Tr N=8 for all72 N",
        "first_moment": "average |psi><psi| = I/8",
        "second_moment": "average (|psi><psi|)^tensor2 = (I+SWAP)/72",
        "all_MUB_overlaps_checked": True,
        "basis_Pauli_generators_x_z": [g for g, _ in classes],
    }


def rational(x):
    return {"exact": str(x), "decimal": float(x)}


def derive_payoffs():
    certificate = json.loads((HERE.parent / "algebra" /
                              "brauer_exact_certificate_D8_g1_10_heralded.json").read_text())
    D = certificate["metadata"]["D"]
    lam = F(certificate["witness"]["Lambda"])
    a = D * F(certificate["witness"]["T"])
    p = F(11583, 12800)
    q = F(10405, 12800)
    passed = (D * q + p) / (D + 1)
    rows = []
    for penalty in (F(1), F(4), F(5)):
        k = (1 + penalty) * D / (D + 1)
        effective_lam = (penalty - F(1, D)) / (1 + penalty)
        # For every 0<=p_ord<=1, q_ord-lam*p_ord<=a.
        ordinary_bound = k * (a + max(F(0), lam - effective_lam))
        switch_score = (1 + penalty) * passed - penalty * p
        rows.append({"accepted_pass_reward": 1, "accepted_failure_penalty": str(penalty),
                     "erasure_reward": 0, "requires_minimum_yield": False,
                     "switch_score": rational(switch_score),
                     "ordinary_upper": rational(ordinary_bound),
                     "score_gap_lower": rational(switch_score - ordinary_bound)})
    # Independent algebraic reduction of the variable-length cost extension.
    # Its quantum stopping/prefix argument is in the expected-cost method note.
    k = 1 - lam
    b = 3 * lam + a - 2
    assert k > 0 and a <= k
    assert 2 * lam >= 1 + F(1, 32)
    assert b >= F(1, 63) and b <= F(7, 16)
    A = 1 / (1 - b)
    B = F(16, 9) - A
    assert A >= 0 and B >= 0
    # A(q-bp)+B(q-p) = (16q-7p)/9.
    assert A + B == F(16, 9) and A * b + B == F(7, 9)
    rate = k / (1 - b)
    switch_utility = 2 * passed - p
    expected_cost = {
        "scope": "arbitrary variable-length ordinary protocols; all queries charged",
        "source_cost_frontier": "q <= b*p + k*E[N]",
        "k": rational(k), "b": rational(b),
        "nonnegative_combination_A": rational(A),
        "nonnegative_combination_B": rational(B),
        "ordinary_utility_per_expected_query_upper": rational(rate),
        "ordinary_utility_at_mean_two_queries_upper": rational(2 * rate),
        "switch_utility_gap_at_mean_two_queries_lower": rational(switch_utility - 2 * rate),
        "ordinary_mean_queries_for_switch_utility_lower": rational(switch_utility / rate),
    }
    bare_q = F(5203, 6400)
    bare_utility = F(2 * D, D + 1) * bare_q - F(D - 1, D + 1)
    visibility = F(9, 10)
    visible_p = visibility * p + (1 - visibility) / 2
    visible_q = visibility * q + (1 - visibility) * bare_q / 2
    visible_utility = F(2 * D, D + 1) * visible_q - F(D - 1, D + 1) * visible_p
    assert visible_utility == visibility * switch_utility + (1 - visibility) * bare_utility / 2
    threshold = (2 * rate - bare_utility / 2) / (switch_utility - bare_utility / 2)
    visibility_audit = {
        "model": "multiply switch control off-diagonal terms by nu; all else ideal",
        "utility_formula": "V(nu)=nu*V_switch+(1-nu)*V_bare/2",
        "bare_utility": rational(bare_utility),
        "minimum_visibility_for_strict_mean_two_query_advantage": rational(threshold),
        "visibility": rational(visibility), "accept_probability": rational(visible_p),
        "accepted_pass_mass": rational((D * visible_q + visible_p) / (D + 1)),
        "utility": rational(visible_utility),
        "gap_over_ordinary_mean_two_query_upper": rational(visible_utility - 2 * rate),
    }
    return {
        "existing_exact_certificate": "../algebra/brauer_exact_certificate_D8_g1_10_heralded.json",
        "lambda": rational(lam), "a": rational(a),
        "switch_accept_probability": rational(p),
        "switch_accepted_pass_mass": rational(passed),
        "switch_accepted_fail_mass": rational(p - passed),
        "switch_erasure_probability": rational(1 - p),
        "payoffs": rows, "expected_query_extension": expected_cost,
        "control_visibility": visibility_audit,
    }


if __name__ == "__main__":
    result = {"status": "passed", "scope": "finite-ensemble and corollary arithmetic only",
              "finite_ensemble": finite_ensemble(), "payoff_reduction": derive_payoffs()}
    (HERE / "application_recovery_game_audit.json").write_text(json.dumps(result, indent=2))
    print(json.dumps(result, indent=2))
