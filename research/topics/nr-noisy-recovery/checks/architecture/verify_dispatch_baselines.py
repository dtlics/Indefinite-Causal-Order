"""Exact Choi certificates for ordinary NR-R12 dispatch baselines.

Only the standard library and Gaussian-rational arithmetic are used.  All
physical input matrix units are included.  These finite checks supplement
the analytic all-dimension proofs; they do not optimize a query frontier.
Nothing is written.  Run without -O so the imported proof guards remain on.
"""

from fractions import Fraction as F
from itertools import product
import json
import sys


if not __debug__:
    raise RuntimeError("Exact dispatch baseline checks require Python without -O.")

sys.dont_write_bytecode = True

from verify_dispatch import (
    ZERO, ONE, require, gaussian, add, times, zeros, identity, adjoint,
    matmul, diagonal_blocks, vectorize, inner, add_outer, scaled, plus,
    trace, pairs, normalized_choi, require_tp_choi,
)


def outer(matrix, weight=F(1)):
    vector = vectorize(matrix)
    result = zeros(len(vector), len(vector))
    add_outer(result, vector, weight)
    return result


def operator_basis(d):
    """Rational orthogonal data basis: (operator, squared HS norm).

    Its normalized vectors define a valid orthonormal Bell measurement.
    A unitary Weyl Bell basis gives the same sum over nonidentity outcomes.
    Keeping their aggregate is enough for the physical all-outcome channel.
    """
    yield identity(d), F(d)
    for i, j in product(range(d), repeat=2):
        if i != j:
            q = zeros(d, d)
            q[i][j] = ONE
            yield q, F(1)
    for k in range(1, d):
        q = zeros(d, d)
        for i in range(k):
            q[i][i] = ONE
        q[k][k] = gaussian(-k)
        yield q, F(k*(k+1))


def block_at(matrix, counter):
    d = len(matrix)
    other = zeros(d, d)
    return diagonal_blocks(matrix, other) if counter == 0 else diagonal_blocks(other, matrix)


def projector_certificate(projector, rank, label):
    require(projector == adjoint(projector), label+" is not Hermitian.")
    require(matmul(projector, projector) == projector, label+" is not a projector.")
    require(trace(projector) == gaussian(rank), label+" has the wrong rank.")


def gamma_star_certificate(d):
    dimension, rank = 2*d, 2*d*d-1
    m = F(1, rank)
    i = identity(dimension)
    z = diagonal_blocks(identity(d), scaled(identity(d), -1))
    phi_i = normalized_choi([(F(1), i)])
    phi_z = normalized_choi([(F(1), z)])
    # This Kraus representation is exactly the projector on block-diagonal
    # operators after deleting the Z tensor I direction.  It is equivalent
    # to the known uniform r-unitary Weyl mixture, with no irrational entries.
    kraus = [(m, i)]
    support = zeros(dimension*dimension, dimension*dimension)
    counter_support = []
    counter_identity = []
    for counter in range(2):
        p = zeros(dimension*dimension, dimension*dimension)
        for q, norm in operator_basis(d):
            block = block_at(q, counter)
            p = plus(p, outer(block, 1/norm))
            if q != identity(d):
                kraus.append((dimension*m/norm, block))
        support = plus(support, p)
        counter_support.append(p)
        counter_identity.append(outer(block_at(identity(d), counter), F(1, d)))
    support_star = plus(support, scaled(phi_z, -1))
    j_star = normalized_choi(kraus)
    projector_certificate(support_star, rank, "Gamma-star support")
    require(j_star == scaled(support_star, m), "Gamma-star full Choi certificate failed.")
    require_tp_choi(j_star, dimension, dimension)
    require(matmul(support_star, phi_i) == phi_i, "Identity is outside the allowed support.")
    return kraus, j_star, support_star, counter_support, counter_identity


def mixed_frontier_checks(d, a, b, certificate):
    dimension, m = 2*d, F(1, 2*d*d-1)
    kraus, j_star, support_star, _, _ = certificate
    w = diagonal_blocks(matmul(b, a), matmul(a, b))
    phi_w = normalized_choi([(F(1), w)])
    require(matmul(support_star, phi_w) == phi_w,
            "A target is not trace-matched to the fallback support.")
    complement = plus(support_star, scaled(phi_w, -1))
    projector_certificate(complement, 2*d*d-2, "Target complement")
    remainder = scaled(complement, m/(1-m))
    require_tp_choi(remainder, dimension, dimension)
    require(inner(vectorize(phi_w), vectorize(j_star)) == gaussian(m),
            "Pointwise zero-call fidelity failed.")
    count = 0
    for cost, acceptance in product([F(0), F(1), F(2), F(3)],
                                    [F(1, 3), F(2, 3), F(1)]):
        s = min(acceptance, cost/3)
        accepted = [(s, w)]+[((acceptance-s)*weight, k) for weight, k in kraus]
        j = normalized_choi(accepted)
        normalized = scaled(j, 1/acceptance)
        require_tp_choi(normalized, dimension, dimension)
        require(trace(j) == gaussian(acceptance), "Acceptance trace failed.")
        q = m*acceptance+(1-m)*s
        require(inner(vectorize(phi_w), vectorize(j)) == gaussian(q),
                "Mean-cost accepted good Bell weight failed.")
        rate = 1-s/acceptance
        delta = rate*(1-m)
        positive, negative = scaled(phi_w, delta), scaled(complement, rate*m)
        require(plus(phi_w, scaled(normalized, -1)) == plus(positive, scaled(negative, -1)),
                "Mean-cost Bell trace-distance witness failed.")
        require(trace(positive) == trace(negative) == gaussian(delta),
                "Mean-cost trace-distance norm failed.")
        require(normalized == plus(scaled(phi_w, 1-delta), scaled(remainder, delta)),
                "Mean-cost matching CPTP diamond upper bound failed.")
        require(3*s <= cost, "Mean query budget exceeded.")
        count += 1
    return count


def hard_two_checks(d, a, b, u, v, certificate):
    """u,v are unnormalized real filter amplitudes; weights handle roots."""
    dimension, h = 2*d, u*u+v*v
    _, _, _, counter_support, counter_identity = certificate
    ba, ab = matmul(b, a), matmul(a, b)
    w = diagonal_blocks(ba, ab)
    i = identity(dimension)
    z = diagonal_blocks(identity(d), scaled(identity(d), -1))
    phi_i = normalized_choi([(F(1), i)])
    phi_z = normalized_choi([(F(1), z)])
    # A cyclic shift is a known traceless unitary at every d>=2.
    correction = zeros(d, d)
    for k in range(d):
        correction[(k+1) % d][k] = ONE
    require(matmul(adjoint(correction), correction) == identity(d), "Correction is not unitary.")
    require(trace(correction) == ZERO, "Correction is not traceless.")
    success = [
        (1/h, diagonal_blocks(scaled(ba, u), scaled(ab, v/d))),
        (1/h, diagonal_blocks(scaled(ba, v/d), scaled(ab, u))),
    ]
    all_outcomes = list(success)
    for q, norm in list(operator_basis(d))[1:]:
        # These are the nonidentity Bell subspaces after the same known
        # physical output correction.  The oracle order remains classical.
        all_outcomes.append((v*v/(h*d*norm), block_at(
            matmul(correction, matmul(b, matmul(q, a))), 0)))
        all_outcomes.append((v*v/(h*d*norm), block_at(
            matmul(correction, matmul(a, matmul(q, b))), 1)))
    full = normalized_choi(all_outcomes)
    require_tp_choi(full, dimension, dimension)
    target = normalized_choi([(F(1), w)])
    expected_fidelity = u*u/(2*h)+u*v/(h*d)+v*v/(h*d*d)
    require(inner(vectorize(target), vectorize(full)) == gaussian(expected_fidelity),
            "Pointwise hard-two all-outcome fidelity failed.")
    relative = normalized_choi([(weight, matmul(adjoint(w), k)) for weight, k in all_outcomes])
    # Explicit PSD decomposition, rather than finite numerical eigenvalues:
    # the two residual summands are orthogonal projectors of rank d^2-2.
    residual_projectors = []
    for counter, word in [(0, ba), (1, ab)]:
        conjugated_r = matmul(adjoint(word), matmul(correction, word))
        bad_direction = outer(block_at(conjugated_r, counter), F(1, d))
        residual = plus(plus(counter_support[counter], scaled(counter_identity[counter], -1)),
                        scaled(bad_direction, -1))
        projector_certificate(residual, d*d-2, "Hard-two residual")
        residual_projectors.append(residual)
    f = v*v/(2*h*d*d)
    z_coefficient = (u-v/d)*(u-v/d)/(2*h)+f
    residual_choi = plus(scaled(phi_z, z_coefficient),
                        scaled(plus(*residual_projectors), f))
    require(relative == plus(scaled(phi_i, expected_fidelity), residual_choi),
            "Hard-two exact PSD complement decomposition failed.")
    require(matmul(phi_i, residual_choi) == zeros(dimension*dimension, dimension*dimension),
            "Hard-two Bell witness is not orthogonal to complement.")
    require_tp_choi(scaled(residual_choi, 1/(1-expected_fidelity)), dimension, dimension)
    require(trace(residual_choi) == gaussian(1-expected_fidelity),
            "Hard-two exact diamond norm failed.")
    # Keeping only the identity Bell outcomes gives a counter dephaser.
    p = (u*u+v*v/(d*d))/h
    q = (u+v/d)*(u+v/d)/(2*h)
    success_relative = normalized_choi([(weight, matmul(adjoint(w), k)) for weight, k in success])
    require_tp_choi(scaled(success_relative, 1/p), dimension, dimension)
    require(trace(success_relative) == gaussian(p), "Hard-two heralded yield failed.")
    require(success_relative == plus(scaled(phi_i, q), scaled(phi_z, p-q)),
            "Hard-two complete heralded counter-dephaser Choi failed.")
    return 1


def main():
    mixed, hard_two = 0, 0
    for d in [2, 3]:
        certificate = gamma_star_certificate(d)
        for a, b in pairs(d):
            mixed += mixed_frontier_checks(d, a, b, certificate)
            for u, v in [(F(1), F(1)), (F(1), F(d)), (F(3), F(4))]:
                hard_two += hard_two_checks(d, a, b, u, v, certificate)
    require(F(2, 3)+F(1, 21) == F(5, 7), "Qubit mean-two fidelity arithmetic failed.")
    require(F(1, 3)*(1-F(1, 7)) == F(2, 7), "Qubit mean-two diamond arithmetic failed.")
    require(F(1, 3)+F(2, 21) == F(3, 7), "Qubit visibility comparison arithmetic failed.")
    require(F(1, 2)+F(1, 8) == F(5, 8), "Qubit hard-two heralded yield failed.")
    require(F(9, 16)/F(5, 8) == F(9, 10), "Qubit hard-two conditional fidelity failed.")
    print(json.dumps({
        "status": "passed", "data_dimensions": [2, 3],
        "unitary_pairs": 4, "accepted_mean_cost_full_choi_cases": mixed,
        "hard_two_full_choi_cases": hard_two,
        "arithmetic": "exact Gaussian rational, standard library",
        "scope": "Achievable nonzero-cost families; zero-query minimax and all-dimension claims need the analytic proof.",
    }, sort_keys=True))


if __name__ == "__main__":
    main()
