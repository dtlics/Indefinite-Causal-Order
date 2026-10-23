"""Exact scalar consequences of NR-R07 in architecture-baselines.md.

The cited Threshold Search theorem and the analytic learning reduction are
inputs, not proved by this arithmetic replay.  This verifier prints JSON and
creates no files; the runner owns reports under the build directory.
"""
from __future__ import annotations

if not __debug__:
    raise RuntimeError("Exact reuse checks require assertions; do not use -O.")

from fractions import Fraction as F
import json


def item(value):
    return {"fraction": str(value), "decimal": float(value)}


def main():
    top_pair_weight = F(81, 100)
    uniform_other_weight_upper = F(3, 800)  # 3/(100n), at n=8.
    gap = top_pair_weight - uniform_other_weight_upper
    xi, failure = F(1, 400), F(1, 100)
    assert gap == F(129, 160)
    assert 0 < uniform_other_weight_upper < top_pair_weight < 1

    # A selected candidate with f_h > r-xi obeys x_h > 1-xi/g.
    individual_fidelity_lower = 1 - xi / gap
    product_fidelity_lower = 1 - 4 * xi / gap
    good_event_score_lower = 2 * product_fidelity_lower - 1
    calibrated_score_lower = 1 - 8 * xi / gap - 2 * failure
    # The displayed score is a conservative lower bound on the exact
    # good/bad event mixture when the bad event is assigned score -1.
    mixture_score_lower = (1 - failure) * good_event_score_lower - failure
    assert individual_fidelity_lower == F(643, 645)
    assert product_fidelity_lower == F(637, 645)
    assert calibrated_score_lower == F(6161, 6450)
    assert mixture_score_lower >= calibrated_score_lower

    search_threshold = top_pair_weight - xi / 2
    search_accuracy = xi / 2
    assert top_pair_weight > search_threshold
    assert search_threshold - search_accuracy == top_pair_weight - xi

    # Haar acceptance <=.905 plus the allowed .0005 source loss.
    specified_switch_upper = F(181, 200) + F(1, 2000)
    assert specified_switch_upper == F(1811, 2000)
    assert calibrated_score_lower > specified_switch_upper

    # m training pairs cost 2m calls, fitting 2L calls for L>=m.
    # In the strict-round policy, m rejected inputs among L=20m leave 19/20
    # of the learned score; no rejected payload or training call is erased.
    online_score_lower = F(19, 20) * calibrated_score_lower
    assert online_score_lower == F(117059, 129000)
    assert online_score_lower > specified_switch_upper
    strict_crossover = calibrated_score_lower / (calibrated_score_lower - specified_switch_upper)
    assert strict_crossover < 20
    assert calibrated_score_lower - specified_switch_upper == F(12821, 258000)
    assert online_score_lower - specified_switch_upper == F(499, 258000)

    # Check monotonicity of the supplied weight bound 3/(100n), not that
    # the actual channel weights obey it; that premise is proved in prose.
    for n in (8, 9, 16, 64, 1024):
        mu_n = F(3, 100 * n)
        assert mu_n <= uniform_other_weight_upper
        assert top_pair_weight - mu_n >= gap

    # The metric counterexample in the current note: balanced reflections
    # differing on exactly two basis vectors have normalized trace 1-4/D.
    # At any even D>=4, opposite relative eigenvalues give half-diamond 1;
    # the finite check below verifies the displayed Choi-fidelity expression.
    reflection_examples = []
    for d in (4, 8, 16, 64):
        c = [1] * (d // 2) + [-1] * (d // 2)
        h = list(c)
        h[0], h[d // 2] = h[d // 2], h[0]
        assert sum(c) == sum(h) == 0
        normalized_overlap = F(sum(a * b for a, b in zip(c, h)), d)
        assert normalized_overlap == 1 - F(4, d)
        # The equal superposition of basis vectors 0 and 1 gives orthogonal
        # outputs.  Work with its rational density matrix to avoid sqrt(2).
        state = [[F(0) for _ in range(d)] for _ in range(d)]
        for i in (0, 1):
            for j in (0, 1):
                state[i][j] = F(1, 2)
        c_output = [[c[i] * state[i][j] * c[j] for j in range(d)] for i in range(d)]
        h_output = [[h[i] * state[i][j] * h[j] for j in range(d)] for i in range(d)]
        output_overlap = sum((c_output[i][j] * h_output[j][i]
                              for i in range(d) for j in range(d)), F(0))
        assert output_overlap == 0
        reflection_examples.append({"dimension": d,
                                    "normalized_trace": str(normalized_overlap),
                                    "Choi_fidelity": str(normalized_overlap**2),
                                    "orthogonal_output_witness_overlap": str(output_overlap)})

    report = {
        "status": "passed", "arithmetic": "standard-library exact Fraction arithmetic",
        "scope": ("Scalar consequences and finite metric examples of NR-R07 reused calibration; "
                  "not the Threshold Search theorem, its sample-count constants, candidate "
                  "implementation cost, or hardware runtime."),
        "top_pair_weight": item(top_pair_weight),
        "uniform_other_pair_weight_upper": item(uniform_other_weight_upper),
        "uniform_spectral_gap": item(gap),
        "threshold_deficit_xi": item(xi),
        "threshold_search_accuracy": item(search_accuracy),
        "threshold": item(search_threshold),
        "learning_failure_probability": item(failure),
        "good_learning_event_product_Bell_fidelity_lower": item(product_fidelity_lower),
        "calibrated_mean_score_lower": item(calibrated_score_lower),
        "specified_switch_actual_score_upper": item(specified_switch_upper),
        "offline_score_gap_lower": item(calibrated_score_lower - specified_switch_upper),
        "first_m_of_20m_rounds_rejected_score_lower": item(online_score_lower),
        "online_score_gap_lower": item(online_score_lower - specified_switch_upper),
        "online_rounds_over_training_pairs_strict_crossover": item(strict_crossover),
        "calibration_queries": "2m ordinary calls for m joint Choi copies",
        "query_crossover": "offline L>=m; strict two-call rounds use L=20m with m rejected training inputs",
        "cited_sample_bound": "O(((log^2 M+log(1/delta))*log(1/delta))/xi^2), with no numerical theorem constant",
        "finite_reflection_metric_examples": reflection_examples,
        "limitations": ["Known candidate synthesis and quantum memory are premises of the query comparison.",
                        "Training must have one persistent frame and the stated independent-copy source.",
                        "The candidate support and approximate-source acceptance allowance are analytic premises, not checked here."],
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
