"""Exact outward delay examples for a causal truncation of an all-pass inverse.

Arithmetic guards are finite. The analytic Fourier/L1/contraction arguments
are in communication.md. This is not a passive-network synthesis certificate.
Import is quiet and guards remain active under -O and -OO.
"""
from fractions import Fraction as F
from math import comb, factorial


def require(ok, message):
    if not ok:
        raise ArithmeticError(message)


def exact_input(x, name):
    require(type(x) in (int, F), f"{name} must be an exact integer or Fraction")
    return F(x)


def tail_polynomial(m, x):
    x = exact_input(x, "tail argument")
    require(type(m) is int and m >= 1 and x >= 0, "invalid tail parameters")
    return sum(F(comb(m, k) * 2 ** k) *
               sum(x ** j / factorial(j) for j in range(k))
               for k in range(1, m + 1))


def exp_lower(x, terms=200):
    x = exact_input(x, "Taylor argument")
    require(x >= 0 and type(terms) is int and terms >= 1,
            "positive exact Taylor parameters required")
    term = F(1)
    total = term
    for j in range(1, terms + 1):
        term *= x / j
        total += term
    return total


def tail_upper(m, x, terms=200):
    return tail_polynomial(m, x) / exp_lower(x, terms)


def ceil_grid(x, digits=12):
    x = exact_input(x, "ceiling argument")
    require(type(digits) is int and digits >= 0, "invalid decimal grid digits")
    scale = 10 ** digits
    q = (x.numerator * scale + x.denominator - 1) // x.denominator
    return F(q, scale)


def floor_grid(x, digits=12):
    x = exact_input(x, "floor argument")
    require(type(digits) is int and digits >= 0, "invalid decimal grid digits")
    scale = 10 ** digits
    return F(x.numerator * scale // x.denominator, scale)


def decimal_fixed(x, digits=12):
    x = exact_input(x, "decimal argument")
    require(type(digits) is int and digits >= 0, "invalid decimal grid digits")
    require((x * 10 ** digits).denominator == 1, "value is not on decimal grid")
    n = (x * 10 ** digits).numerator
    return f"{n // 10 ** digits}.{n % 10 ** digits:0{digits}d}"


def verify():
    # Direct residue expansion gives coefficients -2a (-1)^k binom(m,k+1)
    # (2x)^k/k!, where x=-at. The following are coefficient guards for all
    # powers used in the table, not a substitute for the general derivation.
    coefficient_cases = 0
    for m in range(1, 10):
        for k in range(m):
            # i from the upper contour, (-it)^k at t=-x/a, and
            # (2ia)^(k+1) together contribute i^(2k+2).
            i_power = ((1, 0), (0, 1), (-1, 0), (0, -1))[(2 * k + 2) % 4]
            require(i_power[1] == 0, "residue coefficient is not real")
            residue_coefficient = F(i_power[0] * comb(m, k + 1) * 2 ** (k + 1), factorial(k))
            laguerre_coefficient = -2 * F((-1) ** k * comb(m, k + 1) * 2 ** k, factorial(k))
            require(residue_coefficient == laguerre_coefficient, "inverse impulse sign/coefficient")
            coefficient_cases += 1
        require(sum(comb(m, k) * 4 ** k for k in range(1, m + 1)) == 5 ** m - 1,
                "Chernoff constant identity")
    rows = []
    for target in (F(1, 1000), F(1, 10000)):
        for m in (1, 3, 4, 5, 7, 8, 9):
            x = next(n for n in range(1, 101) if tail_upper(m, F(n)) <= target)
            bound = tail_upper(m, F(x))
            shown_epsilon = ceil_grid(bound)
            require(shown_epsilon <= target and bound <= shown_epsilon,
                    "outward tail rounding")
            error = 2 * shown_epsilon / (1 + shown_epsilon)
            survival = ((1 - shown_epsilon) / (1 + shown_epsilon)) ** 2
            err_hi = ceil_grid(error)
            survival_lo = floor_grid(survival)
            require(err_hi >= error and survival_lo <= survival,
                    "outward contraction/survival rounding")
            rows.append({"target": str(target), "power_m": m, "X_equals_aT": x,
                         "tail_epsilon_upper": decimal_fixed(shown_epsilon),
                         "operator_error_upper": decimal_fixed(err_hi),
                         "minimum_survival_lower": decimal_fixed(survival_lo)})
    composition = []
    for target in (F(1, 1000), F(1, 10000)):
        for n in (4, 8):
            powers = [n - 1, 1, n]
            selected = [next(r for r in rows if r["target"] == str(target) and r["power_m"] == m)
                        for m in powers]
            total_x = sum(r["X_equals_aT"] for r in selected)
            parallel_x = selected[0]["X_equals_aT"] + max(
                selected[1]["X_equals_aT"], selected[2]["X_equals_aT"])
            error = 6 * target / (1 + target)
            survival = ((1 - target) / (1 + target)) ** 6
            composition.append({"N": n, "per_stage_target": str(target),
                                "inverse_powers": powers, "total_X_if_common_a": total_x,
                                "padded_parallel_X_if_common_a": parallel_x,
                                "operator_error_upper": decimal_fixed(ceil_grid(error)),
                                "filter_only_minimum_survival_lower": decimal_fixed(floor_grid(survival))})
    require([r["total_X_if_common_a"] for r in composition] == [39, 63, 47, 71],
            "three-filter delay transcription")
    require([r["padded_parallel_X_if_common_a"] for r in composition] == [31, 55, 37, 61],
            "parallel filter and whole-pair padding delay transcription")
    return {"status": "passed", "arithmetic": "standard-library exact rational",
            "exponential_lower_bound": "sum(j=0..200) X^j/j! <= exp(X)",
            "coefficient_guards": coefficient_cases,
            "delay_units": "T=X/a", "rows": rows, "three_filter_composition": composition,
            "scope": "uniform whole-real-frequency transfer-function bounds for a formal causal "
                     "truncation/normalization; not a finite passive device realization, bandwidth fit, "
                     "controller cost or protected-memory clock"}


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, sort_keys=True))
