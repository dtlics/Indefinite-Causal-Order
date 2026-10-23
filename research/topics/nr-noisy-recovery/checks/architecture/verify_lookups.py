"""Exact finite address-channel checks for NR-R13's lookup baselines.

Only standard-library Gaussian rationals are used. Full normalized address
Choi matrices retain all address coherences and hence arbitrary references.
The general restricted-erasure proof and native QRAM/interface assumptions
remain analytic in native-lookups.md. Reports go to stdout; no files are made.
"""
from __future__ import annotations

if not __debug__:
    raise RuntimeError("Exact lookup checks require assertions; do not use -O.")

from fractions import Fraction as F
from itertools import product
import json

from verify_fault_simulation import (
    ZERO, ONE, require, gaussian, add, times, zeros, identity, adjoint,
    matmul, tensor, vectorize, inner, add_outer,
)


def scaled(a, value):
    return [[times(x, value) for x in row] for row in a]


def summed(a, b):
    return [[add(x, y) for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]


def trace(a):
    out = ZERO
    for i in range(len(a)):
        out = add(out, a[i][i])
    return out


def normalized_choi(weighted_kraus):
    inputs = len(weighted_kraus[0][1][0])
    outputs = len(weighted_kraus[0][1])
    out = zeros(inputs * outputs, inputs * outputs)
    for weight, k in weighted_kraus:
        require(len(k) == outputs and len(k[0]) == inputs,
                "Kraus dimensions disagree.")
        if weight:
            add_outer(out, vectorize(k), weight / inputs)
    return out


def phase(bits):
    out = identity(len(bits))
    for x, bit in enumerate(bits):
        out[x][x] = gaussian((-1)**bit)
    return out


def xor_read(bits):
    out = zeros(2 * len(bits), 2 * len(bits))
    for x, bit in enumerate(bits):
        for answer in range(2):
            out[2 * x + (answer ^ bit)][2 * x + answer] = ONE
    return out


def z_read(bits):
    out = identity(2 * len(bits))
    for x, bit in enumerate(bits):
        for answer in range(2):
            out[2 * x + answer][2 * x + answer] = gaussian((-1)**(bit * answer))
    return out


def prepare_ancilla(n, raw_vector):
    """Raw embedding; all normalization is supplied as explicit CP weights."""
    width = len(raw_vector)
    out = zeros(n * width, n)
    for x in range(n):
        for a, value in enumerate(raw_vector):
            out[width * x + a][x] = value
    return out


def measure_x_raw(n, outcome):
    out = zeros(n, 2 * n)
    for x in range(n):
        for answer in range(2):
            out[x][2 * x + answer] = gaussian((-1)**(outcome * answer))
    return out


def flag_embed(k, flag):
    out = zeros(2 * len(k), len(k[0]))
    for x in range(len(k)):
        for y in range(len(k[0])):
            out[2 * x + flag][y] = k[x][y]
    return out


def ordinary_example(f, g):
    n = len(f)
    h = tuple(a * b for a, b in zip(f, g))
    vx, vz = xor_read(f), z_read(g)
    pf, ph = phase(f), phase(h)
    require(matmul(adjoint(vx), vx) == identity(2 * n), "X read is not unitary.")
    require(matmul(adjoint(vz), vz) == identity(2 * n), "Z read is not unitary.")
    h_raw = [[ONE, ONE], [ONE, gaussian(-1)]]
    wrapper = tensor(identity(n), h_raw)
    require(scaled(matmul(matmul(wrapper, xor_read(g)), wrapper), F(1, 2)) == vz,
            "Hadamard-wrapped XOR read differs from the Z read.")

    forward, reverse = matmul(vz, vx), matmul(vx, vz)
    require(forward == matmul(tensor(ph, identity(2)), reverse),
            "The two explicit oracle products have the wrong conjunction phase.")
    computed = matmul(forward, prepare_ancilla(n, [ONE, ZERO]))
    raw_kraus = [matmul(measure_x_raw(n, s), computed) for s in (0, 1)]
    require(raw_kraus[0] == ph and raw_kraus[1] == matmul(ph, pf),
            "The X measurement address Kraus operators are incorrect.")
    for k in raw_kraus:
        require(matmul(adjoint(k), k) == identity(n),
                "An X outcome does not have input-independent probability one half.")

    # A fresh normalized minus answer supplies phase kickback. The identical
    # raw embedding on both sides makes its 1/sqrt(2) factor cancel exactly.
    minus = prepare_ancilla(n, [ONE, gaussian(-1)])
    require(matmul(vx, minus) == matmul(minus, pf), "The correction query has wrong kickback.")
    corrected = [raw_kraus[0], matmul(pf, raw_kraus[1])]
    require(corrected == [ph, ph], "The conditional correction is not the clean target.")

    target = normalized_choi([(F(1), ph)])
    heralded = normalized_choi([(F(1, 2), raw_kraus[0])])
    deterministic = normalized_choi([(F(1, 2), k) for k in corrected])
    require(heralded == scaled(target, F(1, 2)), "Two-call success Choi identity failed.")
    require(deterministic == target, "Corrected deterministic address Choi identity failed.")
    actual_flagged = normalized_choi([(F(1, 2), flag_embed(k, s))
                                     for s, k in enumerate(corrected)])
    expected_flagged = normalized_choi([(F(1, 2), flag_embed(ph, s)) for s in (0, 1)])
    require(actual_flagged == expected_flagged,
            "The retained measurement flag carries a residual address record.")

    for r in (F(0), F(1, 3), F(1, 2), F(1)):
        p = (1 + r) / 2
        actual = normalized_choi([(F(1, 2), corrected[0]), (r / 2, corrected[1])])
        require(actual == scaled(target, p), "Selective correction Choi identity failed.")
        require(trace(actual) == gaussian(p), "Selective correction success is wrong.")
    mean_two = normalized_choi([(F(2, 5), k) for k in corrected])
    require(mean_two == scaled(target, F(4, 5)), "Mean-two upfront-rejection channel failed.")
    return forward, reverse, ph


def bare_switch_erasure_example():
    # One address for each truth pattern, including the two distinct g
    # values that share the same f=0 junk. This checks inter-class coherence.
    f, g = (0, 0, 1, 1), (0, 1, 0, 1)
    n = len(f)
    forward, reverse, ph = ordinary_example(f, g)
    p0 = [[ONE, ZERO], [ZERO, ZERO]]
    p1 = [[ZERO, ZERO], [ZERO, ONE]]
    switched = summed(tensor(forward, p0), tensor(reverse, p1))
    require(matmul(adjoint(switched), switched) == identity(4 * n),
            "The balanced-switch unitary is not unitary.")
    # Registers are address, answer, control. Initial answer0/control+
    # has raw vector (1,1,0,0) and a CP normalization weight of one half.
    switch_raw = matmul(switched, prepare_ancilla(n, [ONE, ONE, ZERO, ZERO]))
    junk = ([ONE, ONE, ZERO, ZERO], [ZERO, ZERO, ONE, ONE],
            [ZERO, ZERO, ONE, gaussian(-1)])
    labels = (0, 0, 1, 2)
    for x in range(n):
        for a in range(4):
            expected = times(junk[labels[x]][a], (-1)**(f[x] * g[x]))
            require(switch_raw[4 * x + a][x] == expected,
                    "Balanced-switch truth-pattern junk is wrong.")
    gram = [[times(inner(a, b), F(1, 2)) for b in junk] for a in junk]
    require(gram == identity(3), "The three normalized junk vectors are not orthonormal.")

    # (a+b+c)/sqrt(3) = (1,1,2,0)/sqrt(6). Its projector is rational.
    vector = [ONE, ONE, gaussian(2), ZERO]
    effect = zeros(4, 4)
    add_outer(effect, vector, F(1, 6))
    require(effect == adjoint(effect) and matmul(effect, effect) == effect,
            "The cleanup effect is not an orthogonal projector.")
    require(trace(effect) == ONE, "The cleanup projector is not rank one.")
    complement = summed(identity(4), scaled(effect, F(-1)))
    require(matmul(complement, complement) == complement,
            "The cleanup effect is not bounded above by identity.")

    compression = []
    for a in junk:
        row = []
        for b in junk:
            eb = [r[0] for r in matmul(effect, [[x] for x in b])]
            row.append(times(inner(a, eb), F(1, 2)))
        compression.append(row)
    expected_compression = [[gaussian(F(1, 3))] * 3 for _ in range(3)]
    require(compression == expected_compression, "Cleanup compression is not J3/3.")

    accepted_raw = matmul(tensor(identity(n), effect), switch_raw)
    factor = matmul(prepare_ancilla(n, [times(x, F(1, 3)) for x in vector]), ph)
    require(accepted_raw == factor, "Accepted junk does not factor independently of address.")
    address_kraus = [[[accepted_raw[4 * x + a][y] for y in range(n)]
                      for x in range(n)] for a in range(4)]
    accepted = normalized_choi([(F(1, 2), k) for k in address_kraus])
    target = normalized_choi([(F(1), ph)])
    require(accepted == scaled(target, F(1, 3)), "Clean bare-switch address Choi identity failed.")
    require(trace(accepted) == gaussian(F(1, 3)), "Bare-switch clean probability is not one third.")

    # The analytic upper bound uses a general effective compression p J3.
    # This exact witness checks its largest-eigenvalue coefficient 3 and
    # saturation at p=1/3, rather than claiming a finite search proves it.
    all_ones = [[ONE] * 3 for _ in range(3)]
    witness = [[ONE], [ONE], [ONE]]
    require(matmul(all_ones, witness) == [[gaussian(3)]] * 3,
            "The effect upper-bound witness has the wrong coefficient.")
    require(F(3) * F(1, 3) == 1, "The erasure-effect bound is not saturated.")
    return {"address_dimension": n, "truth_patterns": [[f[x], g[x]] for x in range(n)],
            "populated_orthogonal_junk_types": 3,
            "cleanup_effect": [[str(value[0]) for value in row] for row in effect],
            "clean_accepted_probability": "1/3", "full_address_Choi_residual": "0",
            "effective_compression": "J3/3", "upper_bound_witness_eigenvalue_coefficient": 3}


def main():
    counts = []
    for n in (1, 2, 3, 4):
        count = 0
        for f in product((0, 1), repeat=n):
            for g in product((0, 1), repeat=n):
                ordinary_example(f, g)
                count += 1
        require(count == 4**n, "Truth-table enumeration is incomplete.")
        counts.append({"address_dimension": n, "table_pairs_checked": count})

    correction_rows = []
    for r in (F(0), F(1, 3), F(1, 2), F(1)):
        p, c = (1 + r) / 2, 2 + r / 2
        correction_rows.append({"correction_probability": str(r),
                                "success_probability": str(p), "expected_calls": str(c)})
    require(correction_rows[0]["success_probability"] == "1/2", "Two-call success arithmetic failed.")
    require(correction_rows[-1]["success_probability"] == "1", "Deterministic success arithmetic failed.")
    require(F(2) + F(1, 2) == F(5, 2), "Deterministic expected cost is wrong.")
    require(F(4, 5) * F(5, 2) == 2, "Mean-two rejection cost is wrong.")

    print(json.dumps({
        "status": "passed", "arithmetic": "standard-library exact Gaussian rationals",
        "ordinary_full_address_Choi_table_enumeration": counts,
        "ordinary_table_pairs_checked": sum(row["table_pairs_checked"] for row in counts),
        "measurement_outcomes": ["+", "-"], "outcome_probabilities": ["1/2", "1/2"],
        "explicit_H_wrapped_g_read": "passed", "explicit_phase_kickback_correction": "passed",
        "selective_correction_examples": correction_rows,
        "mean_two_upfront_run_probability": "4/5", "mean_two_clean_success": "4/5",
        "bare_balanced_switch": bare_switch_erasure_example(),
        "scope": ("Finite complete-address Choi identities, explicit oracle/measurement/correction "
                  "products, the four-truth-pattern junk-erasure projector, and exact query accounting. "
                  "General junk-only upper bounds and native lookup assumptions remain analytic in native-lookups.md."),
        "limitations": ["No optimal all-ordinary frontier or converse for general switch protocols.",
                        "No native QRAM construction, maintained-table cost measurement, or hardware-runtime comparison."],
    }, indent=2))


if __name__ == "__main__":
    main()
