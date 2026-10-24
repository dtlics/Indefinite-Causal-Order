"""Exact ordinary carrier Bell-analyzer ingredients.

Gaussian-rational finite-frequency contact fixtures retain the complete
known photon source and one normalized accepted photon mode. The analytic
carrier isolation, general mode-existence proof, cooling/filter/clock
premises and infinite-motion model remain in methods/moving-caps.md.
This standard-library module imports quietly and writes no files.
"""
from fractions import Fraction as F
import json

from retained_photon_serial import G, mm, adj, require


def norm(z):
    return z.r * z.r + z.i * z.i


def bell_matrix(c0, b, c1):
    x, y = c0 - b, c1 - b
    require(x != 0 or y != 0, "nonzero entangling contrast")
    u = G(norm(y) - norm(x)) / (2 * (x - y).conj()) if x != y else G()
    gamma = u - b
    matrix = [[u + x, u], [u, u + y]]
    gram = mm(matrix, adj(matrix))
    require(gram[0][1] == 0 and gram[1][0] == 0 and gram[0][0] == gram[1][1],
            "exact maximally entangled amplitude matrix")
    require(gram[0][0].r > 0 and gram[0][0].i == 0, "positive Bell weight")
    return gamma, matrix, gram[0][0].r


def exact_verify():
    f = [G(F(1, 3)), G(0, F(2, 3)), G(F(2, 3))]
    require(sum(norm(z) for z in f) == 1, "normalized three-frequency packet")
    alpha, beta, h = F(3, 5), F(4, 5), F(3, 5)
    cases = [
        ([G(F(-3, 5))] * 3, [G(F(4, 5))] * 3),
        ([G(F(-3, 5)), G(F(-3, 5), F(4, 5)), G(F(-4, 5))],
         [G(F(4, 5)), G(F(5, 13), F(12, 13)), G(F(3, 5), F(-1, 5))]),
        ([G(F(-1, 2)), G(0, F(-2, 3)), G(F(-3, 5), F(1, 5))],
         [G(F(1, 2)), G(0, F(2, 3)), G(F(3, 5), F(-1, 5))]),
        ([G(F(-1, 5)), G(F(2, 5)), G(0, F(3, 5))],
         [G(F(4, 5)), G(F(3, 5), F(1, 5)), G(F(-1, 5), F(1, 5))]),
    ]
    projections = entries = 0
    probabilities = []
    for r0, r1 in cases:
        require(all(norm(z) <= 1 for z in r0 + r1), "physical local elastic contractions")
        q = [alpha * h * z for z in f]
        field = [[beta * f[k] * r0[k] * r0[k] for k in range(3)],
                 [beta * f[k] * r0[k] * r1[k] for k in range(3)],
                 [beta * f[k] * r0[k] * r1[k] for k in range(3)],
                 [beta * f[k] * r1[k] * r1[k] for k in range(3)]]
        coefficients = [sum((f[k].conj() * row[k] for k in range(3)), G()) for row in field]
        gamma, matrix, s2 = bell_matrix(coefficients[0], coefficients[1], coefficients[3])
        h0 = sum(norm(z) for z in q)
        xi = [gamma.conj() * z / h0 for z in q]
        require(sum((xi[k].conj() * q[k] for k in range(3)), G()) == gamma,
                "minimal H mode scalar")
        analyzer_norm = sum(norm(z) for z in xi) + sum(norm(z) for z in f)
        require(analyzer_norm == 1 + norm(gamma) / h0, "complete photonic analyzer norm")
        projected = []
        for row in field:
            value = sum((xi[k].conj() * q[k] + f[k].conj() * row[k] for k in range(3)), G()) / 2
            projected.append(value)
        require(projected == [matrix[0][0] / 2, matrix[0][1] / 2,
                              matrix[1][0] / 2, matrix[1][1] / 2], "literal full photon projection")
        p = sum(norm(z) for z in projected) / analyzer_norm
        require(p == s2 / (2 * analyzer_norm) and 0 < p <= 1, "one normalized outcome probability")
        # Known local unitary M^dagger/s maps the normalized state to Phi+.
        corrected = mm(adj(matrix), matrix)
        require(corrected == [[G(s2), G()], [G(), G(s2)]], "local Bell-frame correction")
        probabilities.append(str(p))
        projections += 1
        entries += 4
    # Abstract degeneracies exercise equal-modulus and equal-vector cases.
    for x, y in [(G(1), G(0, 1)), (G(1, 2), G(1, 2)), (G(), G(1)),
                 (G(2), G(F(20001, 10000), F(1, 10000)))]:
        bell_matrix(x + G(F(1, 3)), G(F(1, 3)), y + G(F(1, 3)))
    no_contrast_rejected = False
    try:
        bell_matrix(G(F(1, 3)), G(F(1, 3)), G(F(1, 3)))
    except ValueError:
        no_contrast_rejected = True
    require(no_contrast_rejected, "a product-only analyzer cannot produce a Bell witness")
    return {"physical_frequency_fixtures": len(cases), "exact_photon_projections": projections,
            "projection_entries": entries, "degeneracy_cases": 4,
            "zero_contrast_rejected": no_contrast_rejected,
            "one_outcome_probabilities": probabilities}


def verify():
    return {
        "status": "passed",
        "rank_one_carrier_analyzer": exact_verify(),
        "scope": (
            "Exact finite rational contact/projection/normalization and local-frame "
            "ingredients only. The general complex-mode theorem and exact carrier "
            "isolation are analytic; no physical analyzer, infinite-cutoff or rate "
            "certificate is supplied. One accepted photon outcome is counted."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2, sort_keys=True))
