"""Finite exact replays for the ordinary local Pauli-overlap estimator.

Analytic all-dimension, calibration and physical-access claims belong to
architecture-baselines.md. No numerical or strategy-optimality certificate.
"""

from fractions import Fraction as F
from itertools import product
import json
import sys

if sys.flags.optimize:
    raise RuntimeError("Run exact replays without Python optimization")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def gadd(a, b):
    return a[0] + b[0], a[1] + b[1]


def gmul(a, b):
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


ZERO, ONE, I = (F(0), F(0)), (F(1), F(0)), (F(0), F(1))
PAULIS = (
    ((ONE, ZERO), (ZERO, ONE)),
    ((ZERO, ONE), (ONE, ZERO)),
    ((ZERO, (F(0), F(-1))), (I, ZERO)),
    ((ONE, ZERO), (ZERO, (F(-1), F(0)))),
)


def multiply(a, b):
    return tuple(tuple(gadd(gmul(a[i][0], b[0][j]),
                           gmul(a[i][1], b[1][j]))
                       for j in range(2)) for i in range(2))


def conjugated_sign(a, k):
    """Sign from the explicit P_a P_k P_a matrix, independent of label rules."""
    actual = multiply(multiply(PAULIS[a], PAULIS[k]), PAULIS[a])
    if actual == PAULIS[k]:
        return 1
    negative = tuple(tuple((-x, -y) for x, y in row) for row in PAULIS[k])
    require(actual == negative, "Pauli conjugation has a real sign")
    return -1


def character(a, b):
    return -1 if a and b and a != b else 1


def local_moments(a, b, w=F(1, 3), sa=F(1), sb=F(1),
                  estimated_sa=None, estimated_sb=None):
    """Sum all axis pairs and actual observed binary-sign outcomes."""
    esa = sa if estimated_sa is None else estimated_sa
    esb = sb if estimated_sb is None else estimated_sb
    mean, second, mass = F(0), F(0), F(0)
    for k, ell in product(range(1, 4), repeat=2):
        axis_probability = w / 3 if k == ell else (1 - w) / 6
        coefficient = 3 / w if k == ell else -6 / (1 - w)
        u, v = conjugated_sign(a, k), conjugated_sign(b, ell)
        for observed_u, observed_v in product((-1, 1), repeat=2):
            probability = (axis_probability * (1 + observed_u * sa * u) / 2
                           * (1 + observed_v * sb * v) / 2)
            U = (1 - observed_u / esa) / 2
            W = (1 - observed_v / esb) / 2
            value = 1 + coefficient * U * W
            mass += probability
            mean += probability * value
            second += probability * value * value
    require(mass == 1, "Complete output distribution")
    return mean, second


def support(label):
    return frozenset(i for i, a in enumerate(label) if a)


def check_support_promise(law, strength):
    n = len(next(iter(law)))
    require(sum(law.values()) == 1 and min(law.values()) >= 0, "Probability law")
    for bits in product((False, True), repeat=n):
        selected = frozenset(i for i, included in enumerate(bits) if included)
        probability = sum(p for label, p in law.items() if selected <= support(label))
        require(probability <= strength ** len(selected), "Local-stochastic promise")


def full_eta(p, q):
    return sum(pa * qb * product_sign(a, b)
               for a, pa in p.items() for b, qb in q.items())


def product_sign(a, b):
    value = 1
    for x, y in zip(a, b):
        value *= character(x, y)
    return value


def joint_moments(p, q, moments, referenced=0):
    mean, second = F(0), F(0)
    for a, pa in p.items():
        for b, qb in q.items():
            first = F(product_sign(a[:referenced], b[:referenced]))
            square = F(1)
            for x, y in zip(a[referenced:], b[referenced:]):
                mu, moment = moments[x, y]
                first *= mu
                square *= moment
            mean += pa * qb * first
            second += pa * qb * square
    return mean, second


def verify_local_overlap():
    axes_cases, noisy_cases, calibration_cases = 0, 0, 0
    base_moments = {}
    for a, b in product(range(4), repeat=2):
        require(conjugated_sign(a, b) == character(a, b), "Explicit Pauli character")
        for w in (F(1, 4), F(1, 3), F(2, 5), F(1, 2), F(3, 4)):
            mean, second = local_moments(a, b, w)
            expected = (F(1) if not a or not b else
                        1 + 6 / w + 12 / (1 - w) if a == b else
                        -3 + 3 / w + 18 / (1 - w))
            require(mean == character(a, b) and second == expected,
                    "Weighted-axis mean and second moment")
            if w == F(1, 3):
                base_moments[a, b] = mean, second
            axes_cases += 1

    noisy_moments = {}
    for sa, sb in product((F(1), F(4, 5), F(1, 2)), repeat=2):
        ta, tb = (sa ** -2 - 1) / 4, (sb ** -2 - 1) / 4
        for a, b in product(range(4), repeat=2):
            for w in (F(1, 3), F(2, 5)):
                mean, second = local_moments(a, b, w, sa, sb)
                ideal = base_moments[a, b][1] if w == F(1, 3) else (
                    F(1) if not a or not b else F(36) if a == b else F(69, 2))
                single = F(54) if w == F(1, 3) else F(55)
                double = F(81) if w == F(1, 3) else F(165, 2)
                predicted = ideal + single * (ta * bool(b) + tb * bool(a)) + double * ta * tb
                require(mean == character(a, b) and second == predicted,
                        "Calibrated binary-output law")
                if sa == F(4, 5) and sb == F(1, 2) and w == F(1, 3):
                    noisy_moments[a, b] = mean, second
                noisy_cases += 1

    # Correlated support laws, not independent per-site error distributions.
    alpha, beta = F(1, 4), F(1, 3)
    p = {(0, 0, 0): 1 - alpha ** 2, (1, 2, 0): alpha ** 2}
    q = {(0, 0, 0): 1 - beta ** 2, (2, 3, 0): beta ** 2}
    check_support_promise(p, alpha)
    check_support_promise(q, beta)
    correlated_cases = 0
    for referenced in (0, 1, 2, 3):
        mean, second = joint_moments(p, q, base_moments, referenced)
        require(mean == full_eta(p, q), "Correlated labels and exact partial-reference signs")
        require(second <= (1 + 36 * alpha * beta) ** (3 - referenced),
                "Correlated local-stochastic bound")
        correlated_cases += 1
    ta, tb = (F(4, 5) ** -2 - 1) / 4, (F(1, 2) ** -2 - 1) / 4
    mean, second = joint_moments(p, q, noisy_moments)
    require(mean == full_eta(p, q), "Noisy correlated-label mean")
    require(second <= (1 + 36 * alpha * beta + 54 * (ta * beta + tb * alpha)
                       + 81 * ta * tb) ** 3, "Noisy support-polynomial bound")

    # Directly enumerate the calibration-biased full experimental distribution.
    for sa, sb, esa, esb in ((F(4, 5), F(3, 4), F(5, 6), F(4, 5)),
                            (F(4, 5), F(3, 4), F(3, 4), F(2, 3))):
        da, db = abs(sa / esa - 1), abs(sb / esb - 1)
        biased = {}
        for a, b in product(range(4), repeat=2):
            biased[a, b] = local_moments(a, b, sa=sa, sb=sb,
                                         estimated_sa=esa, estimated_sb=esb)
            bound = 3 * da * bool(b) + 3 * db * bool(a) + F(9, 4) * da * db
            require(abs(biased[a, b][0] - character(a, b)) <= bound,
                    "Single-site calibration-bias bound")
            calibration_cases += 1
        mean, _ = joint_moments(p, q, biased)
        bound = (1 + 3 * (da * beta + db * alpha) + F(9, 4) * da * db) ** 3 - 1
        require(abs(mean - full_eta(p, q)) <= bound, "All-site calibration-bias example")

    # Full-support independent X/Z generator laws, evaluated without the formula.
    generator_cases = 0
    for r in (F(1, 20), F(1, 5), F(1, 2), F(3, 4)):
        # Label encoding I,X,Y,Z; X^x Z^z has Y label for x=z=1.
        local = {0: (1 - r) ** 2, 1: r * (1 - r),
                 2: r * r, 3: r * (1 - r)}
        for n in (1, 2, 3):
            law = {}
            for label in product(range(4), repeat=n):
                probability = F(1)
                for a in label:
                    probability *= local[a]
                law[label] = probability
            require(full_eta(law, law) == (1 - 2 * r * r) ** (2 * n),
                    "Full-support generator eta")
            require(law[(0,) * n] == (1 - r) ** (2 * n), "Identity probability")
            nonzero_labels = [v for v in product(range(4), repeat=n) if any(v)]
            for site in range(n):
                count = sum(bool(v[site]) for v in nonzero_labels)
                require(F(count, len(nonzero_labels)) == F(3 * 4 ** (n - 1), 4 ** n - 1),
                        "Uniform nonzero Clifford orbit site count")
            generator_cases += 1

    # Equal marginals do not imply the independent-draw target: a=b always commutes.
    nonidentity = {(1,): F(1, 3), (2,): F(1, 3), (3,): F(1, 3)}
    require(full_eta(nonidentity, nonidentity) == F(-1, 3), "Independent-draw guard")
    require(sum(pa * product_sign(a, a) for a, pa in nonidentity.items()) == 1,
            "Correlated-draw guard")
    return {"status": "passed", "arithmetic": "exact rational and Gaussian-rational",
            "weighted_axis_pauli_cases": axes_cases,
            "binary_visibility_pauli_cases": noisy_cases,
            "correlated_support_partial_reference_cases": correlated_cases,
            "calibration_bias_pauli_cases": calibration_cases,
            "full_support_generator_cases": generator_cases,
            "uniform_axis_second_moments": ["1", "37", "33"],
            "two_fifths_axis_second_moments": ["1", "36", "69/2"],
            "limitations": ["Finite identities and examples, not an all-dimension proof.",
                            "No hardware, optimality, generic SPAM or native-advantage claim."]}


if __name__ == "__main__":
    print(json.dumps(verify_local_overlap(), indent=2))
