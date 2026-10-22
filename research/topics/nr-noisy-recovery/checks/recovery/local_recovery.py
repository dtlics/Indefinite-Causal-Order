"""Frozen exact scalar stitching of the local-noise recovery theorem.

The physical local-noise fidelity/acceptance proofs and design-twirl norm
bounds are separately audited inputs. This script checks their common
constants, expected-cost conditions, final score gaps and visibility loss.
No candidate optimization, SDP or floating-point proof step is used.
"""
from fractions import Fraction as F
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent


def rat(x):
    return {"exact": str(x), "decimal": float(x)}


def replay():
    r = F(81, 100)
    k = 1 - r
    A = F(4617, 2560000) + F(3, 200) * F(65536, 65535)**2 + F(1, 512)
    assert A == F(2749735788563, 146597076480000)
    b = 3 * r + A - 2
    assert b == F(65786478674963, 146597076480000)
    Dmin = 256
    beta = F(2, Dmin**2)
    kap0 = F(1, Dmin**2 - 1)
    rho = F(Dmin - 1, 2 * Dmin)
    e = F(1, 1000)
    delta = F(1, 2000)
    e_actual_max = (1 + r) * delta
    # The rates' Bernoulli step is the inequality
    # (1+1/(9n))^n >=1+n/(9n)=10/9 for n positive integer.
    for n in (8, 9, 16, 32, 64):
        assert (1 + F(1, 9 * n))**n >= F(10, 9)
    # All extremal coefficient checks, valid for D>=256.
    assert r > beta
    assert 0 < A + e < k
    assert 2 * r >= 1 + beta
    assert b + e >= kap0 + delta
    assert b + e < rho
    assert e_actual_max < e
    L_Haar = 2 * k / (1 - b)
    L_mu = 2 * k / (1 - b - e)
    R_Haar_lower = F(143, 200)
    # |dq|,|dp|<=delta gives payoff error<(2+1)delta.
    R_mu_lower = R_Haar_lower - 3 * delta
    assert R_mu_lower == F(1427, 2000)
    gap = R_mu_lower - L_mu
    assert L_mu == F(55706889062400, 80664000728557) < F(691, 1000)
    assert gap == F(3693750914850839, 161328001457114000) > F(11, 500)
    nu = F(97, 100)
    # All-order definite circuits have target good weight>=r, and TP p=1.
    # Their recovery score exceeds2r-1=.62; half of that enters the
    # control-dephased minus instrument.
    bare_lower = 2 * r - 1
    visible_Haar_lower = nu * R_Haar_lower + (1 - nu) * bare_lower / 2
    visible_mu_lower = visible_Haar_lower - 3 * delta
    assert visible_mu_lower == F(14027, 20000)
    visible_gap = visible_mu_lower - L_mu
    assert visible_gap == F(17336156971469039, 1613280014571140000)
    assert visible_gap > F(107, 10000)
    result = {
        "status": "passed", "arithmetic": "exact rational",
        "scope": "frozen scalar stitching; separate local-physics and design proofs are inputs",
        "minimum_qubits": 8, "minimum_dimension": 256,
        "local_noise_rate": "eta_n=(4/3)(1-(9/10)^(1/n)); n independent sites after each module",
        "per_module_identity_Pauli_weight": "9/10",
        "joint_identity_pair_weight_r": rat(r),
        "joint_nonidentity_pair_maximum_upper": "3/(100n)",
        "lambda": rat(r), "uniform_affine_intercept_A": rat(A),
        "resource_intercept_b": rat(b), "resource_slope_k": rat(k),
        "prefix_error_at_design_tolerance_upper": rat(e_actual_max),
        "conservative_prefix_error_e": rat(e),
        "each_switch_q_p_error_upper_delta": rat(delta),
        "ordinary_mean_two_Haar_score_upper": rat(L_Haar),
        "switch_Haar_score_lower": rat(R_Haar_lower),
        "Haar_score_gap_lower": rat(R_Haar_lower - L_Haar),
        "ordinary_mean_two_approx_design_score_upper": rat(L_mu),
        "switch_approx_design_score_lower": rat(R_mu_lower),
        "approx_design_score_gap_lower": rat(gap),
        "control_visibility": rat(nu),
        "visible_switch_approx_design_score_lower": rat(visible_mu_lower),
        "visible_score_gap_lower": rat(visible_gap),
        "design_norm": "||Twirl_mu,6-Twirl_Haar,6||_diamond <=1/(2000D^10)",
        "guarantee": "expectation over fresh secret frame/state/noise; not a worst-frame guarantee",
    }
    (HERE / "application_final_local_recovery_audit.json").write_text(json.dumps(result, indent=2))
    return result


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Exact replay requires assertions; run without -O.")
    print(json.dumps(replay(), indent=2))
