"""Check finite parameter substitutions with exact rational arithmetic.

This script does NOT verify C5/C4 or their Haar-recording/causal-comb proofs.
It verifies the stated finite corollaries' numerical consequences assuming
those inputs. Python standard library only.
"""
from fractions import Fraction as F
from pathlib import Path
import json


def main() -> None:
    # Model-validation game: hidden rank-one dephaser versus its Haar average.
    n = 768
    d = 1 << n
    q = 10**12
    assert q <= (1 << (n // 16)) // 100
    assert 2 * q < d
    # sqrt(d - 2q) >= 2^383; use a rational majorant of the source bound.
    root_lower = 1 << ((n - 2) // 2)
    assert d - 2*q >= root_lower**2
    trace_bound = (
        F(18 * (2*q) * (2*q+1), 1 << (n//8))
        + F(4*q, root_lower)
        + F(q*q, d)
        + F(q, d+1)
    )
    causal_score = F(1,2) + trace_bound/2
    misses = F(d+3, 2*(d+1))**7
    switch_worst = 1-misses
    switch_average = 1-misses/2
    assert causal_score < F(500455, 10**6)
    assert switch_worst > F(99,100)
    assert switch_average > F(996,1000)

    # C4-derived projection game, perfect switch completeness.
    n2, r, q2 = 256, 1 << 120, 1 << 56
    d2 = 1 << n2
    assert q2 <= r
    gram = F(r*r,d2)
    collision = F(q2*(q2-1),2*r)
    causal_projection = F(1,2) + F(13,3)*gram + collision
    assert causal_projection < F(502020, 10**6)
    # Check a round-number budget also fits the same ceiling.
    assert 7 * 10**16 < q2

    results = {
        "verification_scope": "Exact arithmetic for parameter substitutions only; C5/C4 are assumed.",
        "model_validation": {
            "target_qubits": n,
            "ordinary_query_budget": q,
            "ordinary_score_upper": float(causal_score),
            "switch_queries": 14,
            "switch_average_success": float(switch_average),
            "switch_worst_hypothesis_success": float(switch_worst),
            "strict_verified_claims": ["ordinary < 0.500455", "switch worst-case > 0.99", "switch balanced-prior > 0.996"]
        },
        "projection_game": {
            "target_qubits": n2,
            "reference_qubits": n2,
            "control_qubits": 1,
            "mixture_components_per_channel": r,
            "ordinary_query_budget": q2,
            "ordinary_score_upper_exact": str(causal_projection),
            "ordinary_score_upper": float(causal_projection),
            "switch_queries": 2,
            "switch_success_exact": 1,
            "strict_verified_claim": "ordinary < 0.502020"
        }
    }
    out = Path(__file__).with_name("constants.json")
    out.write_text(json.dumps(results, indent=2)+"\n")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
