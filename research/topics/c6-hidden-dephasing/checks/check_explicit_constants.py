"""Exact arithmetic for the current C6 scalar majorants.

This checks the arithmetic after the analytic radical and dimension estimates,
not those estimates or the physical recording-to-cache comparison.
"""
from fractions import Fraction
import json


def main():
    # For 1 <= q <= R/100 and d=R^16, the paper bounds each error
    # by its coefficient times q^2/R^2, with q^2/R^2 <= 1/10000.
    # See paper/main.tex, sec:c6-recording, final paragraph.
    terms = {
        "haar_pair": 18 * 2 * 3,
        "twice_forward_error": 2 * 2,
        "creator_error": 14 * 6,
        "twice_birth_error": 2 * 4,
        "raw_and_uniform_cache": 2 + 6,
    }
    paper_bound = Fraction(sum(terms.values()), 10000)
    assert paper_bound == Fraction(212, 10000)

    # ICO.C6Bounds.error_le uses a 209/10000 majorant for its
    # non-uniform cache expression. C6UniformBounds drops the nonnegative
    # old cache term and adds the uniform cache allowance 6/10000.
    intermediate_bound = Fraction(108 + 4 + 84 + 8 + 2 + 3, 10000)
    formal_bound = intermediate_bound + Fraction(6, 10000)
    assert formal_bound == Fraction(215, 10000)
    assert paper_bound <= formal_bound < Fraction(1, 3)
    assert (1 + formal_bound) / 2 < Fraction(2, 3)

    # d>=2 implies the single-switch MUB plus probability <=3/4.
    # Four independent repetitions therefore suffice uniformly.
    switch_error = Fraction(3, 4) ** 4
    assert switch_error == Fraction(81, 256) < Fraction(1, 3)

    print(json.dumps({
        "status": "PASS",
        "arithmetic": "exact integers and rational fractions",
        "paper_terms_in_1e_minus_4": terms,
        "paper_distance_majorant": str(paper_bound),
        "formal_distance_majorant": str(formal_bound),
        "formal_majorant_numerator_over_10000": 215,
        "switch_elementary_channel_calls": 8,
        "switch_error_upper_bound": str(switch_error),
        "scope": "Arithmetic only, conditional on the analytic majorants in the paper and Lean; not an all-degree or physical-endpoint check."
    }, indent=2))


if __name__ == "__main__":
    main()

