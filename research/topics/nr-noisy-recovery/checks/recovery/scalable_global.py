"""Exact scalar/polynomial corollary checks for scalable quantum recovery.

No SDP, numerical eigensolver or third-party package is used. The separately
proved acceptance witness and design-transfer norms are inputs.
This checks the dimension algebra, polynomial positivity certificates, gaps
and the conservative approximate-design loss.
"""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent


def trim(p):
    p = list(map(F, p))
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def add(p, q):
    r = [F(0)] * max(len(p), len(q))
    for i, x in enumerate(p):
        r[i] += x
    for i, x in enumerate(q):
        r[i] += x
    return trim(r)


def scale(p, c):
    return trim([F(c) * x for x in p])


def mul(p, q):
    r = [F(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            r[i + j] += x * y
    return trim(r)


def shift(p, s):
    return trim([sum(F(p[j]) * comb(j, i) * F(s) ** (j - i)
                     for j in range(i, len(p))) for i in range(len(p))])


def value(p, x):
    return sum(F(c) * F(x) ** i for i, c in enumerate(p))


def deriv(p):
    return trim([i * p[i] for i in range(1, len(p))] or [0])


def rat(x):
    return {"exact": str(x), "decimal": float(x)}


def params(D):
    D = F(D)
    beta = 2 / D**2
    lam = F(81, 100) + F(19, 50) / D**2
    k = 1 - lam
    a = (1 - beta) * F(81, 100) * F(19, 100) * F(3, 2) / D
    b = 3 * lam + a - 2
    p = F(181, 200) - F(1, 200) / D**2
    q = F(81, 100) + F(37, 200) / D**2
    R = (2 * D * q - (D - 1) * p) / (D + 1)
    return beta, lam, k, a, b, p, q, R


def replay():
    # b numerator over20000D^3 and factorization of1-b.
    b_num = [-9234, 22800, 4617, 8600]
    one_minus_b_num = add([0, 0, 0, 20000], scale(b_num, -1))
    assert one_minus_b_num == mul(scale([-2, 0, 1], 19), [-243, 600])
    # ((D-1)/(2D)-b)*20000D^3.
    threshold_num = add([0, 0, -10000, 10000], scale(b_num, -1))
    assert threshold_num == list(map(F, [9234, -22800, -14617, 1400]))
    threshold_shift = shift(threshold_num, 16)
    assert threshold_shift == list(map(F, [1636882, 584656, 52583, 1400]))
    assert all(x > 0 for x in threshold_shift)
    # -b' = [4617D^2+45600D-27702]/(20000D^4).
    minus_b_prime_num = [-27702, 45600, 4617]
    assert shift(minus_b_prime_num, 16) == list(map(F, [1883850, 193344, 4617]))
    assert all(x > 0 for x in shift(minus_b_prime_num, 16))
    # R' - L' has the stated positive denominator. Derive its numerator
    # independently from R and L, then certify H(D)>0 for D>=1.
    H = add(scale(mul([0, 0, 0, 1], mul([1, 1], [1, 1])), 9720000),
            scale(mul([-1, 36, 75, 19], mul([-243, 600], [-243, 600])), -1))
    assert H == list(map(F, [59049, -2417364, 6428925, 17508069, -2019600, 2880000]))
    H_shift = shift(H, 1)
    assert H_shift == list(map(F, [22439079, 69286293, 75635532,
                                 38229669, 12380400, 2880000]))
    assert all(x > 0 for x in H_shift)
    # R -143/200 is positive, with numerator38D^2+75D-1.
    switch_positive_num = [-1, 75, 38]
    assert all(x > 0 for x in shift(switch_positive_num, 1))
    table = []
    for D in (16, 32, 64, 128, 256):
        beta, lam, k, a, b, p, q, R = params(D)
        assert a / k == F(243, 200 * D)
        assert 1 - b == k * (3 - F(243, 200 * D))
        assert 2 * k / (1 - b) == F(400 * D, 600 * D - 243)
        assert k > 0 and a <= k and 2 * lam >= 1 + beta
        assert b >= F(1, D * D - 1) and b <= F(D - 1, 2 * D)
        assert R - F(143, 200) == F(38 * D * D + 75 * D - 1,
                                    200 * D * D * (D + 1))
        table.append({"D": D, "ordinary_mean_two_upper": rat(2 * k / (1 - b)),
                      "switch_utility": rat(R), "gap_lower": rat(R - 2 * k / (1 - b))})
    _, _, k16, a16, b16, _, _, R16 = params(16)
    L16 = 2 * k16 / (1 - b16)
    L8 = F(15385600, 22294617)
    R8 = F(85399, 115200)
    exact_gap = R16 - L16
    assert L16 == F(6400, 9357) < L8 < F(143, 200)
    assert R8 - L8 > exact_gap == F(354881891, 8144332800)
    delta = F(1, 1000)
    # General-D approximate-transfer coefficient checks at their extremal
    # values. k grows, t=243/(200D) falls, b falls and r=(D-1)/(2D) grows.
    assert k16 - a16 > delta
    assert F(15, 32) - b16 > delta
    assert F(43, 100) >= F(1, 255) + F(1, 2000)
    L16_app = 2 * k16 / (1 - b16 - delta)
    L8_app = F(1061606400, 1535768573)
    app_gap = R16 - L16_app
    assert L16_app == F(15443200, 22537481) < L8_app
    assert app_gap == F(830391550503, 19616623462400) > F(1, 25)
    assert R8 - L8_app > app_gap
    result = {
        "status": "passed", "arithmetic": "exact rational and integer polynomial",
        "source_Haar_frontier": "lambda=81/100+19/(50D^2), a=4617(D^2-2)/(20000D^3)",
        "a_over_k": "243/(200D)",
        "ordinary_mean_two_upper_for_D_ge16": "400D/(600D-243)",
        "threshold_polynomial_at_D16_plus_x": [str(x) for x in threshold_shift],
        "gap_derivative_positive_polynomial_at_D1_plus_x": [str(x) for x in H_shift],
        "ordinary_upper_D16": rat(L16), "D8_ordinary_upper": rat(L8),
        "all_n_ge3_Haar_or_exact_design_gap": rat(exact_gap),
        "design_requirement": "||sixth_twirl(mu)-sixth_twirl(Haar)||_diamond <=1/(2000D^10)",
        "uniform_frontier_intercept_inflation_upper": str(delta),
        "approximate_ordinary_upper_D16": rat(L16_app),
        "approximate_ordinary_upper_D8": rat(L8_app),
        "all_n_ge3_approximate_design_gap": rat(app_gap),
        "sample_rows_not_used_to_prove_uniform_claim": table,
    }
    (HERE / "application_scalable_recovery_audit.json").write_text(json.dumps(result, indent=2))
    return result


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Exact checks require assertions; run without -O.")
    print(json.dumps(replay(), indent=2))
