"""Exact finite and polynomial replay of NR-R14 bath backaction screens.

Gaussian-rational matrices and polynomial quotient arithmetic are used;
no floating point, third-party packages, or generated files. Full flagged
Choi equalities include every bath input and any passive reference. Finite
examples and algebraic counterexamples do not certify a general hardware
advantage, a complete noise model, or exclusion of every classical bath.
"""
from fractions import Fraction as F
from pathlib import Path
from itertools import product
import json
import sys

if not __debug__:
    raise RuntimeError("Run exact echo checks without -O.")
sys.dont_write_bytecode = True
helpers = Path(__file__).resolve().parent
sys.path.insert(0, str(helpers))
from verify_dispatch import (
    ZERO, ONE, require, gaussian, add, times, zeros, identity, adjoint,
    matmul, tensor, diagonal_blocks, scaled, plus, trace, pairs,
    normalized_choi, require_tp_choi, flag_embed,
)
from verify_fault_simulation import multiply, conjugate


def measure_block(unitary, d, phase, sign):
    # Plus input and <0| + sign*phase <1| output give a factor 1/2.
    result = zeros(d, d)
    for r, c, initial in product(range(d), range(d), range(2)):
        result[r][c] = add(result[r][c], times(unitary[r][initial*d+c], F(1, 2)))
        result[r][c] = add(result[r][c], times(
            multiply(phase, unitary[d+r][initial*d+c]), F(sign, 2)))
    return result


def require_unitary(a):
    require(matmul(adjoint(a), a) == identity(len(a)), "Not unitary.")


def echo_check(a, b):
    d = len(a)
    v = diagonal_blocks(a, b)
    x = zeros(2*d, 2*d)
    for j in range(d):
        x[j][d+j] = x[d+j][j] = ONE
    echo = matmul(x, matmul(v, matmul(x, v)))
    q, r = matmul(b, a), matmul(a, b)
    require(echo == diagonal_blocks(q, r), "Full echo controlled-order identity failed.")
    require(matmul(echo, echo) == diagonal_blocks(matmul(q, q), matmul(r, r)),
            "Repeated echo identity failed.")
    count = 0
    for phase in [ONE, gaussian(0, -1)]:
        native, ideal = [], []
        for flag, sign in [(0, 1), (1, -1)]:
            actual = measure_block(echo, d, phase, sign)
            weighted_r = [[multiply(phase, value) for value in row] for row in r]
            expected = scaled(plus(q, scaled(weighted_r, sign)), F(1, 2))
            require(actual == expected, "Bath Kraus instrument identity failed.")
            native.append((F(1), flag_embed(actual, flag)))
            ideal.append((F(1), flag_embed(expected, flag)))
        j_native, j_ideal = normalized_choi(native), normalized_choi(ideal)
        require(j_native == j_ideal, "Flagged full Choi instrument differs.")
        require_tp_choi(j_native, d, 2*d)
        count += 1
    return count


def axis_pair(ca, sa, cb, sb):
    a = [[gaussian(ca, -sa), ZERO], [ZERO, gaussian(ca, sa)]]
    b = [[gaussian(cb), gaussian(0, -sb)], [gaussian(0, -sb), gaussian(cb)]]
    require_unitary(a)
    require_unitary(b)
    return a, b


def coherence(a, b, repetitions):
    q, r = matmul(b, a), matmul(a, b)
    qn, rn = identity(2), identity(2)
    for _ in range(repetitions):
        qn, rn = matmul(q, qn), matmul(r, rn)
    return times(trace(matmul(adjoint(rn), qn)), F(1, 2))


def heldout_counterexample():
    # All four bath rotations have Gaussian-rational entries.
    first = axis_pair(F(15, 17), F(8, 17), F(56, 65), F(33, 65))
    second = axis_pair(F(0), F(1), F(1073, 1105), F(264, 1105))
    t, v = F(264, 1105)**2, F(840, 1105)**2
    require(coherence(*first, 1) == coherence(*second, 1) == gaussian(1-2*t),
            "First echo coherences do not match.")
    for sign in [1, -1]:
        outputs = []
        for a, b in [first, second]:
            k = scaled(plus(matmul(b, a), scaled(matmul(a, b), sign)), F(1, 2))
            outputs.append(scaled(matmul(k, adjoint(k)), F(1, 2)))
        probability = 1-t if sign == 1 else t
        require(outputs[0] == outputs[1] == scaled(identity(2), probability/2),
                "First echo flagged bath states do not match.")
    require(coherence(*first, 2) == gaussian(1-8*t*v), "First held-out coherence failed.")
    require(coherence(*second, 2) == ONE, "Second held-out coherence is not one.")
    return {"first_echo_minus_probability": str(t),
            "heldout_memory_fidelity_gap": str(4*t*v)}


def record_correlation_check():
    # Actual A=H and B=ZH; unnormalized raw matrices below have common
    # factor sqrt(2). The complete three-window path has weight 1/8.
    a = [[ONE, ONE], [ONE, gaussian(-1)]]
    z = [[ONE, ZERO], [ZERO, gaussian(-1)]]
    b = matmul(z, a)
    require(matmul(adjoint(a), a) == scaled(identity(2), 2), "Raw Hadamard norm failed.")
    require(matmul(adjoint(b), b) == scaled(identity(2), 2), "Raw ZH norm failed.")
    results = []
    for middle in [a, b]:
        normalization, correlation = ZERO, ZERO
        for m, n in product([1, -1], repeat=2):
            first = scaled(plus(a, scaled(b, m)), F(1, 2))
            last = scaled(plus(a, scaled(b, n)), F(1, 2))
            path = matmul(last, matmul(middle, first))
            # rho=I/2 and the omitted three sqrt(2) factors give 1/16.
            probability = times(trace(matmul(path, adjoint(path))), F(1, 16))
            normalization = add(normalization, probability)
            correlation = add(correlation, times(probability, m*n))
        require(normalization == ONE, "Three-window record experiment is not normalized.")
        results.append(correlation)
    require(results == [ONE, gaussian(-1)], "Maximal ordinary backaction contrast failed.")
    return 2


def p_reduce(terms):
    """Gaussian-rational R[c,s]/(c^2+s^2-1), canonical s degree <=1."""
    pending = list(terms.items())
    result = {}
    while pending:
        (i, j), coefficient = pending.pop()
        if coefficient == ZERO:
            continue
        if j >= 2:
            pending.append(((i, j-2), coefficient))
            pending.append(((i+2, j-2), times(coefficient, -1)))
        else:
            result[i, j] = add(result.get((i, j), ZERO), coefficient)
    return {power: coefficient for power, coefficient in result.items() if coefficient != ZERO}


def p_const(value):
    return p_reduce({(0, 0): value})


def p_add(a, b):
    out = dict(a)
    for power, coefficient in b.items():
        out[power] = add(out.get(power, ZERO), coefficient)
    return p_reduce(out)


def p_scale(a, value):
    return p_reduce({power: multiply(coefficient, value) for power, coefficient in a.items()})


def p_multiply(a, b):
    out = {}
    for (i, j), first in a.items():
        for (k, ell), second in b.items():
            power = i+k, j+ell
            out[power] = add(out.get(power, ZERO), multiply(first, second))
    return p_reduce(out)


def p_conjugate(a):
    return {power: conjugate(value) for power, value in a.items()}


def p_matrix_constant(a):
    return [[p_const(value) for value in row] for row in a]


def p_matrix_add(a, b):
    return [[p_add(x, y) for x, y in zip(first, second)] for first, second in zip(a, b)]


def p_matrix_scale(a, factor):
    return [[p_multiply(value, factor) for value in row] for row in a]


def p_matrix_multiply(a, b):
    out = [[{} for _ in b[0]] for _ in a]
    for r, k, c in product(range(len(a)), range(len(b)), range(len(b[0]))):
        out[r][c] = p_add(out[r][c], p_multiply(a[r][k], b[k][c]))
    return out


def p_matrix_adjoint(a):
    return [[p_conjugate(a[c][r]) for c in range(len(a))] for r in range(len(a[0]))]


def p_trace(a):
    result = {}
    for j in range(len(a)):
        result = p_add(result, a[j][j])
    return result


def p_at_cosine_squared(a, x):
    """Final coherence expressions have only even powers of real c."""
    result = F(0)
    for (i, j), (real, imag) in a.items():
        require(j == 0 and i % 2 == 0 and imag == 0,
                "Coherence is not a polynomial in cosine squared.")
        result += real*x**(i//2)
    return result


def symbolic_ramsey_checks():
    """All-time Ramsey equality and a phase-optimized reversed DD choice.

    c=cos(omega*t/2), s=sin(omega*t/2) are indeterminates subject only to
    c^2+s^2=1. No numerical angles, square roots, or trigonometry are used.
    """
    unit = p_const(ONE)
    c, s = {(1, 0): ONE}, {(0, 1): ONE}
    minus_i_s = p_scale(s, gaussian(0, -1))
    pi = p_matrix_constant(identity(2))
    px = p_matrix_constant([[ZERO, ONE], [ONE, ZERO]])
    pz = p_matrix_constant([[ONE, ZERO], [ZERO, gaussian(-1)]])
    a = p_matrix_add(p_matrix_scale(pi, c), p_matrix_scale(px, minus_i_s))
    b = p_matrix_add(p_matrix_scale(pi, c), p_matrix_scale(pz, minus_i_s))
    require(p_matrix_multiply(p_matrix_adjoint(a), a) == pi, "Symbolic A is not unitary.")
    require(p_matrix_multiply(p_matrix_adjoint(b), b) == pi, "Symbolic B is not unitary.")
    c_squared = p_multiply(c, c)
    s_squared = p_multiply(s, s)
    quantum_fid = p_scale(p_trace(p_matrix_multiply(p_matrix_adjoint(b), a)), gaussian(F(1, 2)))
    clock_phase = p_add(c, p_scale(s, gaussian(0, 1)))
    clock_phase_squared = p_multiply(clock_phase, clock_phase)
    # Classical field lambda=0,+/-omega, with probabilities1/2,1/4,1/4.
    classical_fid = p_add(p_const(gaussian(F(1, 2))), p_scale(
        p_add(clock_phase_squared, p_conjugate(clock_phase_squared)), gaussian(F(1, 4))))
    require(quantum_fid == classical_fid == c_squared,
            "All-time complete Ramsey-channel equality failed.")
    ba, ab = p_matrix_multiply(b, a), p_matrix_multiply(a, b)
    quantum_echo = p_scale(p_trace(p_matrix_multiply(p_matrix_adjoint(ab), ba)), gaussian(F(1, 2)))
    expected_echo = p_add(unit, p_scale(p_multiply(s_squared, s_squared), gaussian(-2)))
    require(quantum_echo == expected_echo, "Symbolic quantum echo coherence failed.")
    # No-pulse storage at total duration2t: A^2 versus B^2.
    a2, b2 = p_matrix_multiply(a, a), p_matrix_multiply(b, b)
    quantum_idle = p_scale(p_trace(p_matrix_multiply(p_matrix_adjoint(b2), a2)), gaussian(F(1, 2)))
    cosine_double = p_add(c_squared, p_scale(s_squared, gaussian(-1)))
    require(quantum_idle == p_multiply(cosine_double, cosine_double),
            "Symbolic two-window no-pulse coherence failed.")
    clock_phase_fourth = p_multiply(clock_phase_squared, clock_phase_squared)
    classical_idle = p_add(p_const(gaussian(F(1, 2))), p_scale(
        p_add(clock_phase_fourth, p_conjugate(clock_phase_fourth)), gaussian(F(1, 4))))
    require(quantum_idle == classical_idle, "No-pulse storage calibration does not agree.")
    # At c^2=1/4 (omega*t=2pi/3), compare BEST known Z-phase correction.
    echo = p_at_cosine_squared(quantum_echo, F(1, 4))
    idle = p_at_cosine_squared(quantum_idle, F(1, 4))
    require(echo == F(-1, 8) and idle == F(1, 4), "Reversed storage coherences failed.")
    echo_fidelity, idle_fidelity = (1+abs(echo))/2, (1+abs(idle))/2
    require(echo_fidelity == F(9, 16) < idle_fidelity == F(5, 8),
            "Phase-optimized quantum storage preference is not reversed.")
    # A static classical field refocuses exactly; its echo fidelity is1.
    require(F(1) > idle_fidelity, "Classical static model does not prefer echo.")
    require(p_at_cosine_squared(quantum_echo, F(0)) == -1,
            "Opposite deterministic echo diagnostic at omega*t=pi failed.")
    # Explicit passive alternating classical-bit embedding from the note.
    az = [[p_add(c, minus_i_s), {}], [{}, p_add(c, p_scale(minus_i_s, gaussian(-1)))]]
    bz = p_matrix_adjoint(az)
    flip_a, flip_b = p_matrix_multiply(px, az), p_matrix_multiply(px, bz)
    flip_ab = p_matrix_multiply(flip_a, flip_b)
    flip_ba = p_matrix_multiply(flip_b, flip_a)
    passive_echo = p_scale(p_trace(p_matrix_multiply(p_matrix_adjoint(flip_ab), flip_ba)),
                           gaussian(F(1, 2)))
    expected_passive = p_add(unit, p_scale(p_multiply(c_squared, s_squared), gaussian(-8)))
    require(passive_echo == expected_passive, "Classical alternating-field counterexample failed.")
    require(p_at_cosine_squared(passive_echo, F(9, 25)) == F(-527, 625),
            "A passive classical field did not exhibit echo loss.")
    return {"polynomial_families": 3, "quantum_echo_best_phase_fidelity": str(echo_fidelity),
            "no_pulse_best_phase_fidelity": str(idle_fidelity),
            "static_classical_echo_fidelity": "1"}


def main():
    cases = sum(echo_check(a, b) for d in [2, 3] for a, b in pairs(d))
    example = heldout_counterexample()
    contrast = record_correlation_check()
    symbolic = symbolic_ramsey_checks()
    print(json.dumps({"status": "passed", "flagged_full_choi_cases": cases,
                      "data_dimensions": [2, 3], "arithmetic": "exact Gaussian rational",
                      "ordinary_three_window_record_contrast": contrast,
                      "symbolic_ramsey_and_storage": symbolic,
                      "scope": "Exact finite full-instrument replay and scalar polynomial counterexamples; general access and physical-cost statements remain analytic.",
                      "counterexample": example}, sort_keys=True))


if __name__ == "__main__":
    main()
