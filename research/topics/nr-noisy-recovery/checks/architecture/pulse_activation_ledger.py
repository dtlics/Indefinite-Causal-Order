"""Scalar floating-point pulse/action diagnostic, not a noise certificate.

Primary pins: Howe et al., PRX Quantum 3, 010350 (2022), Sec. II
Eqs. (1)-(2), Fig. 3, Sec. VI Eq. (7), and Supplement XI:
https://arxiv.org/html/2111.12778v2
Liu et al., PRX Quantum 4, 030310 (2023), Sec. II/Fig. 2 supplies
the separate arbitrary-equatorial-phase interface discussion:
https://doi.org/10.1103/PRXQuantum.4.030310

All arithmetic/functions below preserve the audited source-parameter
ledger. Fractional-event rows are ideal interpolations. Rounded words,
midpoint process fidelity, microscopic noise, a coherent order helper,
hardware optimality and an irreducible activation cost are not certified.
Howe's event calibration and Liu's phase family are distinct experiments.
"""

import json
import math
from fractions import Fraction


def require(condition, message):
    if not condition:
        raise ValueError(message)


def verify():
    # Howe et al., Fig. 3, Sec. II and Eq. (7).  The energy is the paper's
    # approximate on-chip estimate, not quantized thermodynamic work.
    nu_pi = 352
    n_jj = 4650
    critical_current_a = Fraction(305, 100000)
    drive_hz = 2685000000
    planck_j_s = Fraction(662607015, 10**42)
    charge_c = Fraction(1602176634, 10**28)
    flux_quantum_wb = planck_j_s / (2 * charge_c)
    estimated_jpg_event_j = n_jj * critical_current_a * flux_quantum_wb

    # NR-R21 uses exp(-i theta A), while nu_pi is a Bloch-pi rotation.
    h = math.atan(1 / math.sqrt(2))
    b = math.pi / 6
    alpha = math.pi / 4
    q = Fraction(1, 9)
    events_per_oracle_radian = 2 * nu_pi / math.pi
    actions = {
        "direct_bisector_train": (alpha, 1),
        "ordinary_euler_three": (h + b, 3),
        "native_first_attempt_only": (2 * h, 2),
        "native_terminal_repair_mean": (2 * h + float(q) * (math.pi - b), Fraction(7, 3)),
        "native_rollback_retry_mean": ((2 * h + math.pi * float(q)) / (1 - float(q)), Fraction(5, 2)),
    }
    rows = {}
    for name, (action, calls) in actions.items():
        events = events_per_oracle_radian * action
        rows[name] = {
            "named_train_count_or_mean": float(calls),
            "total_oracle_angle_or_mean": action,
            "ideal_interpolated_jpg_events_or_mean": events,
            "ideal_active_time_ns_at_fig3_clock": 1e9 * events / drive_hz,
            "estimated_onchip_dissipation_pj": 1e12 * events * float(estimated_jpg_event_j),
            "idle_drive_periods_if_each_train_uses_howes_library_padding": float(2 * calls),
        }

    # Basic unit conversion and independent algebraic cross-checks prevent
    # the common factor-of-two and macro-call/event conflations.
    require(events_per_oracle_radian * (math.pi / 2) == nu_pi, "Bloch-pi normalization")
    require(rows["direct_bisector_train"]["ideal_interpolated_jpg_events_or_mean"] == 176, "Bloch-pi/2 train")
    require(b < h, "ordinary Euler action is below first native attempt")
    require(alpha < h + b < 2 * h, "action ordering")
    require(Fraction(2) + 3 * q == Fraction(7, 3), "terminal repair count")
    require(2 * (1 + q) / (1 - q) == Fraction(5, 2), "rollback count")
    require(28e-15 < float(estimated_jpg_event_j) < 30e-15, "source energy scale")

    # These integers are diagnostic nearest-pulse compilations only.  q=1/9
    # and exact output formulas must not be applied to the rounded words.
    euler_counts = [round(events_per_oracle_radian * t) for t in (h / 2, b, h / 2)]
    native_counts = [round(events_per_oracle_radian * h)] * 2
    require(euler_counts == [69, 117, 69], "nearest Euler events")
    require(native_counts == [138, 138], "nearest native first-attempt events")

    euler_active = rows["ordinary_euler_three"]["ideal_active_time_ns_at_fig3_clock"]
    hybrid_active = rows["native_terminal_repair_mean"]["ideal_active_time_ns_at_fig3_clock"]
    # This AP9 diagnostic even grants a cost-free native helper.  A measured
    # native-only helper latency H adds 3H/2 to the required setup latency.
    required_setup_ns = (hybrid_active - euler_active) / (3 - 7 / 3)
    library_padding_ns = 1e9 * 2 / drive_hz
    require(47 < required_setup_ns < 49, "native hybrid setup threshold")
    require(library_padding_ns < 1, "source library phase padding scale")

    return {
        "status": "passed",
        "scope": "Source-parameter cost diagnostic; no phase-resolved noisy map, native helper, hardware optimality or exact rounded gate is certified.",
        "source": "https://arxiv.org/html/2111.12778v2",
        "source_pins": ["Fig. 3", "Sec. II Eq. (2)", "Sec. VI Eq. (7)", "Supplement XI"],
        "source_constants": {
            "nu_pi_bloch": nu_pi,
            "n_jj_phase_slips_per_jpg_event": n_jj,
            "critical_current_a": float(critical_current_a),
            "fig3_drive_hz": drive_hz,
            "flux_quantum_wb": float(flux_quantum_wb),
            "estimated_onchip_dissipation_per_jpg_event_fj": 1e15 * float(estimated_jpg_event_j),
        },
        "interpolated_rows": rows,
        "nearest_integer_diagnostic_only": {
            "ordinary_euler_event_word": euler_counts,
            "native_first_attempt_event_word": native_counts,
            "exact_target_or_native_failure_probability_claimed": False,
        },
        "conditional_euler_vs_native_hybrid_clock": {
            "setup_needed_per_named_train_ns_even_with_free_native_helper": required_setup_ns,
            "native_helper_latency_multiplier_to_add": 1.5,
            "published_library_phase_padding_ns_per_train_at_fig3_clock": library_padding_ns,
            "padding_is_an_irreducible_activation_cost": False,
        },
        "uncounted_costs": [
            "ambient AWG, trigger drive, attenuation and wiring dissipation",
            "any quantum order helper, routing, coherent trigger or selector",
            "helper readout/reset, data waiting, and physical recovery noise",
            "actual phase changes, rounding, leakage and train transients",
            "calibration amortization and any paid quantum-drive reuse",
        ],
    }


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True, indent=2))
