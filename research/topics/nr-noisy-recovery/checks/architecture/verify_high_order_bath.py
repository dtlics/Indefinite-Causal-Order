"""Exact finite guards for NR-R14's four-contact hidden-bath counterexample.

No third-party dependencies, numerical tolerances, or generated files.
The universal access/support argument is analytic in backaction.md.
"""

from fractions import Fraction as F
from itertools import combinations, product
import json

if not __debug__:
    raise RuntimeError("Run exact high-order bath checks without -O.")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def cadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def cmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def bits(index, n):
    return tuple((index >> (n - 1 - j)) & 1 for j in range(n))


def index_of(bitstring):
    result = 0
    for bit in bitstring:
        result = 2 * result + bit
    return result


def ghz_density(sign):
    rho = [[F(0) for _ in range(16)] for _ in range(16)]
    rho[0][0] = rho[15][15] = F(1, 2)
    rho[0][15] = rho[15][0] = F(sign, 2)
    return rho


def marginal(rho, keep):
    keep = tuple(keep)
    discard = tuple(j for j in range(4) if j not in keep)
    dim = 1 << len(keep)
    out = [[F(0) for _ in range(dim)] for _ in range(dim)]
    for row in range(16):
        rb = bits(row, 4)
        for col in range(16):
            cb = bits(col, 4)
            if any(rb[j] != cb[j] for j in discard):
                continue
            out[index_of(rb[j] for j in keep)][index_of(cb[j] for j in keep)] += rho[row][col]
    return out


def x_product_expectation(rho, subset):
    mask = sum(1 << (3 - j) for j in subset)
    return sum((rho[row][row ^ mask] for row in range(16)), F(0))


def coherence(rho, signs, c, s):
    # Expand product_j (c I - i s signs[j] X_j) exactly on the actual GHZ state.
    total = (F(0), F(0))
    for size in range(5):
        for subset in combinations(range(4), size):
            coefficient = (F(1), F(0))
            for j in range(4):
                coefficient = cmul(coefficient, (F(0), -s * signs[j]) if j in subset else (c, F(0)))
            expectation = x_product_expectation(rho, subset)
            total = cadd(total, (expectation * coefficient[0], expectation * coefficient[1]))
    return total


def choi_guard(real_coherence):
    # Normalized Choi state of the logical dephasing channel.
    matrix = [[F(0) for _ in range(4)] for _ in range(4)]
    matrix[0][0] = matrix[3][3] = F(1, 2)
    matrix[0][3] = matrix[3][0] = real_coherence / 2
    require(sum(matrix[j][j] for j in range(4)) == 1, "Choi trace")
    require(abs(real_coherence) <= 1, "Choi positive eigenvalues")
    for a, b in product(range(2), repeat=2):
        reduced = sum(matrix[2 * a + t][2 * b + t] for t in range(2))
        require(reduced == (F(1, 2) if a == b else 0), "Choi TP partial trace")


def verify_high_order_bath():
    rho_plus, rho_minus = ghz_density(1), ghz_density(-1)
    marginal_count = 0
    for size in range(4):
        for keep in combinations(range(4), size):
            require(marginal(rho_plus, keep) == marginal(rho_minus, keep), "proper GHZ marginal mismatch")
            marginal_count += 1
    for sign, rho in ((1, rho_plus), (-1, rho_minus)):
        for size in range(5):
            for subset in combinations(range(4), size):
                expected = F(1) if size == 0 else F(sign) if size == 4 else F(0)
                require(x_product_expectation(rho, subset) == expected, "X moment")
    c, s = F(3, 5), F(4, 5)
    require(c * c + s * s == 1, "physical rational phase")
    channel_count = 0
    for sign, rho in ((1, rho_plus), (-1, rho_minus)):
        for signs in product((-1, 1), repeat=4):
            predicted = c**4 + sign * product_of(signs) * s**4
            require(coherence(rho, signs, c, s) == (predicted, F(0)), "full four-contact coherence")
            choi_guard(predicted)
            channel_count += 1
    good_l, bad_l = F(337, 625), F(-7, 25)
    good_f, bad_f = (1 + good_l) / 2, (1 + abs(bad_l)) / 2
    require(good_f == F(481, 625), "good corrected Bell fidelity")
    require(bad_f == F(16, 25), "bad optimally phase-corrected Bell fidelity")
    require(good_f - bad_f == F(81, 625), "reversed schedule gap")
    return {
        "status": "passed",
        "result": "NR-R14",
        "arithmetic": "exact Fraction and Gaussian rational",
        "proper_ghz_marginals": marginal_count,
        "x_moments": 32,
        "reference_complete_logical_choi_cases": channel_count,
        "rational_phase": {"cos_2theta": "3/5", "sin_2theta": "4/5"},
        "corrected_schedule_fidelities": ["481/625", "16/25"],
        "corrected_schedule_gap": "81/625",
        "scope": (
            "Finite proper-marginal and normalized logical Choi guards at a rational phase; "
            "the all-instrument support/clock-access proof, pi/8 values, independence and "
            "operational sampling bounds remain analytic, with no native advantage claim."
        ),
    }


def product_of(values):
    result = 1
    for value in values:
        result *= value
    return result


if __name__ == "__main__":
    print(json.dumps(verify_high_order_bath(), sort_keys=True))
