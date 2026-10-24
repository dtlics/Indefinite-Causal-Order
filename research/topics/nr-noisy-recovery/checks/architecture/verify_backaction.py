"""Exact finite and polynomial replay of NR-R14 and NR-R19.

Gaussian-rational matrices and polynomial quotient arithmetic are used;
no floating point, third-party packages, or generated files. Full flagged
Choi equalities include every bath input and any passive reference. Finite
examples and algebraic counterexamples do not certify a general hardware
advantage, a complete noise model, or exclusion of every classical bath.
The exchange example additionally replays the full controlled sensor map,
diamond-norm factor identities and normalized Choi Gram data, with no access
to the defect output. NR-R19 adds full matrix-unit odd-coupler channel
identities and ordinary counterprotocols. Its universal hard-two converse,
like the generic norm bound, remains an analytic proof.
Andreev/Majorana guards check finite signature, particle-hole, bandwidth
and rank-one commutator identities; all-family wrapper/access proofs are analytic.
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
from native_converter_guards import run_checks as native_converter_checks


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


def exchange_backaction_checks():
    """Exact joint exchange model and full controlled-channel norm factors.

    The generic completely bounded cross-map norm inequality is proved in
    backaction.md. Here all finite matrix identities, input matrix units,
    Gram data and an attaining input are checked with Gaussian fractions.
    No inaccessible bath output is supplied to either discriminator.
    """
    q, mm, dag, kron = gaussian, matmul, adjoint, tensor
    i2 = identity(2)
    x = [[ZERO, ONE], [ONE, ZERO]]
    y = [[ZERO, q(0, -1)], [q(0, 1), ZERO]]
    z = [[ONE, ZERO], [ZERO, q(-1)]]
    p = [[ZERO, ZERO], [ZERO, ONE]]
    jump = [[ZERO, ONE], [ZERO, ZERO]]
    phase = [[ONE, ZERO], [ZERO, q(0, 1)]]

    def imaginary_scale(a, coefficient):
        return [[multiply(q(0, coefficient), v) for v in row] for row in a]

    def coupling(axis):
        block = plus(scaled(i2, F(2, 3)),
                     imaginary_scale(plus(axis, scaled(z, 2)), F(-1, 3)))
        out = identity(4)
        for r, rr in enumerate([2, 1]):
            for c, cc in enumerate([2, 1]):
                out[rr][cc] = block[r][c]
        return out

    def bath_kraus(unitary, d=2):
        # Matrix order is accessible input/output (C,S if present), then E.
        return [[[unitary[2*o+e][2*i] for i in range(d)]
                 for o in range(d)] for e in range(2)]

    def channel(kraus, rho):
        out = zeros(len(kraus[0]), len(kraus[0]))
        for k in kraus:
            out = plus(out, mm(mm(k, rho), dag(k)))
        return out

    def units(d):
        for r, c in product(range(d), repeat=2):
            out = zeros(d, d)
            out[r][c] = ONE
            yield out

    def vec(a):
        return [a[r][c] for c in range(len(a[0])) for r in range(len(a))]

    def dot(a, b):
        out = ZERO
        for left, right in zip(a, b):
            out = add(out, multiply(conjugate(left), right))
        return out

    a_joint = coupling(x)
    b_joint = [coupling(y), coupling(scaled(y, -1))]
    for u in [a_joint, *b_joint]:
        require_unitary(u)
    qp = kron(phase, i2)
    require(b_joint[0] == mm(dag(qp), mm(a_joint, qp)),
            "Positive joint phase-conjugation relation failed.")
    require(b_joint[1] == mm(qp, mm(a_joint, dag(qp))),
            "Negative joint phase-conjugation relation failed.")
    single = [bath_kraus(u) for u in [a_joint, *b_joint]]
    marginal0 = [[ONE, ZERO], [ZERO, q(F(2, 3), F(-2, 3))]]
    marginal1 = scaled(jump, F(1, 3))
    for rho in units(2):
        expected = channel([marginal0, marginal1], rho)
        require(all(channel(ks, rho) == expected for ks in single),
                "Isolated complete sensor channels are not identical.")

    amplitude = F(7, 9)
    t, b = 1-amplitude, (1+amplitude)/2
    gamma = 1-amplitude**2
    d = [[ONE, ZERO], [ZERO, q(b)]]
    d_bad = [[ONE, ZERO], [ZERO, q(amplitude)]]
    full, fixed_plus, ordinary, effects = [], [], [], []
    expected_ab = [imaginary_scale(z, -1),
                   imaginary_scale(plus(plus(scaled(x, 4), scaled(y, -4)),
                                        scaled(z, 7)), F(-1, 9))]
    expected_ba = [imaginary_scale(plus(plus(scaled(x, 4), scaled(y, 4)),
                                        scaled(z, 7)), F(-1, 9)),
                   imaginary_scale(z, -1)]
    for index, b_model in enumerate(b_joint):
        raw_ab, raw_ba = mm(a_joint, b_model), mm(b_model, a_joint)
        for raw, expected in [(raw_ab, expected_ab[index]), (raw_ba, expected_ba[index])]:
            require([[raw[rr][cc] for cc in [2, 1]] for rr in [2, 1]] == expected,
                    "One-excitation product formula failed.")
        ab, ba = mm(qp, raw_ab), mm(qp, raw_ba)
        good = ab if index == 0 else ba
        require(good == kron(i2, phase), "Full joint good memory word is not local on E.")
        bad = ba if index == 0 else ab
        bad_kraus = bath_kraus(bad)
        require(bad_kraus[0] == d_bad and
                mm(dag(bad_kraus[1]), bad_kraus[1]) == scaled(p, gamma),
                "Bad word is not the stated amplitude-damping channel.")
        ordinary.append(bath_kraus(ab))
        ks = bath_kraus(diagonal_blocks(ba, ab), 4)
        full.append(ks)
        # Plus-control embedding omits sqrt(2); Choi weights below restore it.
        fixed_plus.append([[[add(k[o][i], k[o][2+i]) for i in range(2)]
                            for o in range(4)] for k in ks])
        effect = mm(dag(ab), ba)
        effects.append([[effect[2*r][2*c] for c in range(2)] for r in range(2)])
        expected0 = diagonal_blocks(d_bad, i2) if index == 0 else diagonal_blocks(i2, d_bad)
        require(ks[0] == expected0, "Full input no-jump controlled Kraus formula failed.")
    require(effects[0] == effects[1] == d_bad,
            "Control-only cross effect differs between hidden signs.")
    require((1-(1+amplitude)/2)/2 == F(1, 18), "Control minus probability failed.")

    l1, r1 = kron(i2, scaled(jump, b)), kron(z, scaled(jump, t))
    l2, r2 = kron(i2, d), kron(z, scaled(p, -t))

    def elementary(rho):
        return plus(mm(mm(l1, rho), dag(r1)), mm(mm(l2, rho), dag(r2)))

    for rho in units(4):
        difference = plus(channel(full[0], rho), scaled(channel(full[1], rho), -1))
        require(difference == plus(elementary(rho), dag(elementary(dag(rho)))),
                "Full control/sensor channel factorization failed.")
    left = plus(mm(dag(l1), l1), mm(dag(l2), l2))
    right = plus(mm(dag(r1), r1), mm(dag(r2), r2))
    require(left == kron(i2, [[ONE, ZERO], [ZERO, q(2*b*b)]]),
            "Left cross-map norm factor failed.")
    require(right == kron(i2, scaled(p, 2*t*t)) and 2*b*b > 1 and 2*b*t == gamma,
            "Right cross-map norm factor failed.")
    # The same no-control factors bound ordinary id versus amplitude damping.
    for rho in units(2):
        elem = plus(scaled(mm(mm(jump, rho), dag(jump)), t*b),
                    scaled(mm(mm(d, rho), p), -t))
        sharp = plus(scaled(mm(mm(jump, dag(rho)), dag(jump)), t*b),
                     scaled(mm(mm(d, dag(rho)), p), -t))
        delta = plus(channel(ordinary[1], rho), scaled(channel(ordinary[0], rho), -1))
        require(delta == plus(elem, dag(sharp)), "Ordinary norm factorization failed.")

    # Exact Choi Gram data, with TP checks on the full matrices.
    v0, v1 = vec(full[0][0]), vec(full[1][0])
    n, m = dot(v0, v0), dot(v0, v1)
    require(n == dot(v1, v1) == q(F(292, 81)) and m == q(F(32, 9)),
            "Full Choi no-jump Gram matrix failed.")
    require(n[0]**2-m[0]**2 == F(16*145, 81**2), "Choi radical discriminant failed.")
    for index in [0, 1]:
        jump_vec = vec(full[index][1])
        require(dot(jump_vec, jump_vec) == q(gamma) and
                dot(jump_vec, v0) == dot(jump_vec, v1) == ZERO,
                "Choi jump Gram data failed.")
        require_tp_choi(normalized_choi([(F(1), k) for k in full[index]]), 4, 4)
        require_tp_choi(normalized_choi([(F(1, 2), k) for k in fixed_plus[index]]), 2, 4)
        require(dot(vec(fixed_plus[index][0]), vec(fixed_plus[index][0])) == n,
                "Fixed-plus Choi norm failed.")
    require(dot(vec(full[0][1]), vec(full[1][1])) == ZERO and
            dot(vec(fixed_plus[0][0]), vec(fixed_plus[1][0])) == m,
            "Cross-hypothesis Choi Gram data failed.")
    # Fixed-plus jump vectors also occupy distinct control sectors.
    for index in [0, 1]:
        fv = vec(fixed_plus[index][1])
        require(dot(fv, fv) == q(gamma) and all(
            dot(fv, vec(fixed_plus[other][0])) == ZERO for other in [0, 1]),
            "Fixed-plus Choi jump orthogonality failed.")
    require(dot(vec(fixed_plus[0][1]), vec(fixed_plus[1][1])) == ZERO,
            "Fixed-plus Choi jumps are not orthogonal.")
    ov0, ov1 = vec(ordinary[0][0]), vec(ordinary[1][0])
    n0, n1, overlap = dot(ov0, ov0)[0], dot(ov1, ov1)[0], dot(ov0, ov1)
    require((n0+n1)**2-4*(overlap[0]**2+overlap[1]**2) == F(16*145, 81**2),
            "Ordinary Choi discriminant differs.")
    for index, ks in enumerate(ordinary):
        fidelity = sum((trace(k)[0]**2+trace(k)[1]**2 for k in ks), F(0))/4
        require(fidelity == (F(1) if index == 0 else F(64, 81)),
                "Serial memory fidelity failed.")
    od = plus(channel(ordinary[0], p), scaled(channel(ordinary[1], p), -1))
    require(od == [[q(-gamma), ZERO], [ZERO, q(gamma)]], "Ordinary attaining input failed.")
    fd = scaled(plus(channel(fixed_plus[0], p), scaled(channel(fixed_plus[1], p), -1)), F(1, 2))
    require(all(fd[r][c] == ZERO for r, c in product(range(4), repeat=2) if r != c)
            and sum(abs(fd[r][r][0]) for r in range(4))/2 == gamma,
            "Full output attaining input failed.")

    # Different early/late joint blocks and nontrivial persistent-bath gap.
    a1, b1, a2, b2, gap = a_joint, b_joint[0], b_joint[1], a_joint, b_joint[0]
    selector1, selector2 = diagonal_blocks(a1, b1), diagonal_blocks(a2, b2)
    flip = kron(x, identity(4))
    chronological = mm(flip, mm(selector2, mm(flip, mm(kron(i2, gap), selector1))))
    require(chronological == diagonal_blocks(mm(b2, mm(gap, a1)), mm(a2, mm(gap, b1))),
            "Clock-dependent native selector compilation failed.")
    return {"isolated_channels": "identical complex amplitude damping",
            "good_memory_entanglement_fidelity": "1", "bad_memory_entanglement_fidelity": "64/81",
            "control_only_effect": ["1", "7/9"], "maximally_mixed_sensor_minus_probability": "1/18",
            "full_arbitrary_control_input_half_diamond": str(gamma),
            "ordinary_serial_half_diamond": str(gamma),
            "normalized_choi_half_trace_distance": "(8+sqrt(145))/81",
            "equal_prior_optimal_success": str((1+gamma)/2),
            "full_input_matrix_units": 16, "clock_dependent_selector_identity": True,
            "scope": "Finite joint model and norm-factor replay; analytic diamond inequality, no fitted hardware or all-adaptive ordinary converse."}


def odd_coupler_checks():
    """Finite NR-R19 identities; no numerical or general-comb converse."""
    mm, kron, dag, q = matmul, tensor, adjoint, gaussian

    def cscale(a, value):
        return [[multiply(value, x) for x in row] for row in a]

    def odd(u):
        d = len(u)
        out, ud = zeros(2*d, 2*d), dag(u)
        for r, c in product(range(d), repeat=2):
            out[r][d+c], out[d+r][c] = ud[r][c], u[r][c]
        return out

    def phase(value):
        return [[value, ZERO], [ZERO, conjugate(value)]]

    def ad_unit(k, r, c):
        # Ad_k(|r><c|), including off-diagonal inputs without density fitting.
        return [[multiply(row[r], conjugate(col[c])) for col in k] for row in k]

    i2 = identity(2)
    x = [[ZERO, ONE], [ONE, ZERO]]
    y = [[ZERO, q(0, -1)], [q(0, 1), ZERO]]
    z = [[ONE, ZERO], [ZERO, q(-1)]]
    u2 = plus(scaled(i2, F(5, 13)), cscale(y, q(0, F(-12, 13))))
    h2 = plus(scaled(x, F(3, 5)), scaled(z, F(4, 5)))
    r01, r12 = identity(3), identity(3)
    r01[0][0] = r01[1][1] = q(F(3, 5))
    r01[0][1] = r01[1][0] = q(0, F(-4, 5))
    r12[1][1] = r12[2][2] = q(F(5, 13))
    r12[1][2], r12[2][1] = q(F(-12, 13)), q(F(12, 13))
    u3 = mm(r01, r12)
    hvec = [F(1, 3), F(2, 3), F(2, 3)]
    h3 = [[q(F(r == c)-2*hvec[r]*hvec[c]) for c in range(3)] for r in range(3)]
    phases = [ONE, q(0, 1), q(F(3, 5), F(4, 5)), q(F(5, 13), F(-12, 13))]
    corrected_count = visibility_count = drift_count = wrapper_count = selector_count = gauge_count = 0

    for u, h in [(u2, h2), (u3, h3)]:
        d, idata = len(u), identity(len(u))
        n = 2*d
        require_unitary(u)
        require(dag(h) == h and mm(h, h) == idata, "Odd-coupler involution failed.")
        require(mm(u, h) != mm(h, u), "Odd-coupler example must be noncommuting.")
        a, b = odd(u), odd(mm(u, h))
        zc = kron(z, idata)
        w = diagonal_blocks(h, mm(mm(u, h), dag(u)))
        require(mm(a, b) == mm(b, a) == w and mm(w, w) == identity(n),
                "Commuting odd-coupler target failed.")
        for pa, pb in product(phases, repeat=2):
            ap, bp = mm(kron(phase(pa), idata), a), mm(kron(phase(pb), idata), b)
            require(dag(ap) == ap and mm(ap, ap) == identity(n) and
                    dag(bp) == bp and mm(bp, bp) == identity(n),
                    "Phase-dressed coupler is not a Hermitian involution.")
            delta = multiply(pb, conjugate(pa))
            p, reverse = mm(bp, ap), mm(ap, bp)
            require(p == mm(kron(phase(delta), idata), w) and
                    reverse == mm(kron(phase(conjugate(delta)), idata), w),
                    "Static phase signs differ from the controlled products.")
            kp = scaled(plus(p, reverse), F(1, 2))
            km = mm(zc, scaled(plus(p, scaled(reverse, -1)), F(1, 2)))
            require(kp == scaled(w, delta[0]) and km == cscale(w, q(0, delta[1])),
                    "All-outcome corrected Kraus operators failed.")
            require(mm(p, p) == kron(phase(multiply(delta, delta)), idata),
                    "Whole-pair phase calibration failed.")
            serial_overlap = times(trace(mm(dag(w), p)), F(1, n))
            require(multiply(serial_overlap, conjugate(serial_overlap)) == q(delta[0]**2),
                    "Raw serial entanglement fidelity differs from cos(delta)^2.")
            m = diagonal_blocks(h, idata)
            require(mm(m, mm(ap, mm(m, ap))) == w and mm(m, mm(bp, mm(m, bp))) == w,
                    "Known-H two-repeated-query wrapper failed.")
            wrapper_count += 2
            selector, flip = diagonal_blocks(ap, bp), kron(x, identity(n))
            require(mm(flip, mm(selector, mm(flip, selector))) == diagonal_blocks(p, reverse),
                    "Supplied-selector chronological compilation failed.")
            selector_count += 1

            pa_late, pb_late = q(0, 1), q(F(3, 5), F(4, 5))
            ap_late, bp_late = mm(kron(phase(pa_late), idata), a), mm(kron(phase(pb_late), idata), b)
            p0, p1 = mm(bp_late, ap), mm(ap_late, bp)
            drift_kp = scaled(plus(p0, p1), F(1, 2))
            drift_km = mm(zc, scaled(plus(p0, scaled(p1, -1)), F(1, 2)))
            relative = multiply(multiply(pb_late, conjugate(pa)), multiply(pa_late, conjugate(pb)))
            desired = mm(kron([[relative, ZERO], [ZERO, ONE]], idata), w)
            zp, zr, zw = mm(zc, p), mm(zc, reverse), mm(zc, w)
            for r, c in product(range(n), repeat=2):
                coherent = plus(ad_unit(kp, r, c), ad_unit(km, r, c))
                target = ad_unit(w, r, c)
                require(coherent == target, "Corrected full matrix-unit channel failed.")
                corrected_count += 1
                incoherent = scaled(plus(plus(ad_unit(p, r, c), ad_unit(reverse, r, c)),
                                         plus(ad_unit(zp, r, c), ad_unit(zr, r, c))), F(1, 4))
                for visibility in [F(0), F(3, 5), F(1)]:
                    actual = plus(scaled(coherent, visibility), scaled(incoherent, 1-visibility))
                    expected = plus(scaled(target, (1+visibility)/2),
                                    scaled(ad_unit(zw, r, c), (1-visibility)/2))
                    require(actual == expected, "Visibility-limited full output channel failed.")
                    visibility_count += 1
                require(plus(ad_unit(drift_kp, r, c), ad_unit(drift_km, r, c)) == ad_unit(desired, r, c),
                        "Time-dependent phase residual channel failed.")
                drift_count += 1
            if d == 2:
                require(mm(y, mm(h, y)) == scaled(h, -1), "Balanced-H gauge example failed.")
                up = mm(u, y)
                ap2 = mm(kron(phase(pa), idata), odd(up))
                bp2 = mm(kron(phase(multiply(q(0, 1), pb)), idata), odd(mm(up, h)))
                w2 = diagonal_blocks(h, mm(mm(up, h), dag(up)))
                require(w2 == mm(zc, w) and mm(bp2, ap2) == cscale(p, q(0, 1)) and
                        trace(mm(dag(w), w2)) == ZERO,
                        "Whole-pair identical-channel/orthogonal-target gauge failed.")
                gauge_count += 1

    abelian_count = 0
    cx = diagonal_blocks(i2, x)
    for value in phases:
        u = phase(value)
        for h in [x, y, plus(scaled(x, F(3, 5)), scaled(y, F(4, 5)))]:
            require(dag(h) == h and mm(h, h) == i2 and mm(h, z) == scaled(mm(z, h), -1),
                    "Unknown transverse H example failed.")
            p, qdata = dag(u), mm(u, h)
            actual = mm(cx, mm(kron(i2, p), mm(cx, kron(i2, qdata))))
            require(actual == diagonal_blocks(h, mm(mm(u, h), dag(u))),
                    "Unknown-H Abelian ordinary two-query counterprotocol failed.")
            abelian_count += 1
    return {"result": "NR-R19", "data_dimensions": [2, 3], "station_phase_pairs_per_dimension": 16,
            "corrected_channel_input_matrix_units": corrected_count,
            "visibility_channel_input_matrix_units": visibility_count,
            "temporal_drift_input_matrix_units": drift_count,
            "known_H_repeated_query_wrappers": wrapper_count,
            "supplied_selector_identities": selector_count,
            "whole_pair_gauge_ambiguities": gauge_count,
            "unknown_H_Abelian_two_query_identities": abelian_count,
            "scope": "Exact finite identities and ordinary closures; d>=3 full hard-two converse, no-SWITCH dependency and native cost remain analytic."}


def andreev_native_checks():
    """Finite guards for AM1 and AM3--AM5, not the universal AM2 proof."""
    def transpose(a):
        return [list(row) for row in zip(*a)]

    def conjugated(a):
        return [[conjugate(v) for v in row] for row in a]

    def difference(a, b):
        return plus(a, scaled(b, -1))

    def norm_square(a):
        return sum(v[0]**2+v[1]**2 for row in a for v in row)

    def reflector(vector):
        p = [[multiply(a, conjugate(b)) for b in vector] for a in vector]
        return difference(identity(len(vector)), scaled(p, 2))

    def odd(u):
        d = len(u)
        out, ud = zeros(2*d, 2*d), adjoint(u)
        for i, j in product(range(d), repeat=2):
            out[i][d+j], out[d+i][j] = ud[i][j], u[i][j]
        return out

    def particle_hole(a):
        flip = odd(identity(len(a)//2))
        return matmul(flip, matmul(conjugated(a), flip)) == a

    signature_cases = commutator_cases = 0
    for n in range(2, 6):
        m = 2*n
        p = [ONE]+[ZERO]*(m-1)
        a = reflector(p)
        require(matmul(a, a) == identity(m) and trace(a) == gaussian(m-2),
                "Single-Majorana involution signature guard failed.")
        signature_cases += 1
        for c, s in [(F(1), F(0)), (F(0), F(1)),
                     (F(3, 5), F(4, 5)), (F(5, 13), F(12, 13))]:
            b = reflector([gaussian(c), gaussian(s)]+[ZERO]*(m-2))
            comm = difference(matmul(b, a), matmul(a, b))
            overlap = c*c
            score = norm_square(comm)/F(4*m)
            require(score == 8*overlap*(1-overlap)/m and score <= F(2, m),
                    "Rank-one mixed-probe commutator normalization failed.")
            commutator_cases += 1

    h = [[ZERO, ONE, ZERO], [ONE, ZERO, ZERO], [ZERO, ZERO, ONE]]
    phases = [ONE, gaussian(0, 1), gaussian(F(3, 5), F(4, 5)),
              gaussian(F(5, 13), F(12, 13))]
    phs_pairs = dressed_phs_pairs = 0
    for q in phases:
        v = identity(3)
        v[1][1] = q
        u = matmul(v, transpose(v))
        hq = matmul(conjugated(v), matmul(h, transpose(v)))
        require(adjoint(hq) == hq and matmul(hq, hq) == identity(3),
                "Correlated particle-hole reflection guard failed.")
        uh = matmul(u, hq)
        require(transpose(u) == u and transpose(uh) == uh,
                "Takagi-correlated converter pair is not symmetric.")
        a, b = odd(u), odd(uh)
        require(particle_hole(a) and particle_hole(b) and
                matmul(a, b) == diagonal_blocks(hq, conjugated(hq)),
                "Particle-hole full target specialization failed.")
        phs_pairs += 1
        for pa, pb in product(phases, repeat=2):
            za, zb = zeros(6, 6), zeros(6, 6)
            # e^(i alpha Z) has Gaussian-rational phases pa and pa*.
            for i in range(3):
                za[i][i], za[3+i][3+i] = pa, conjugate(pa)
                zb[i][i], zb[3+i][3+i] = pb, conjugate(pb)
            require(particle_hole(matmul(za, a)) and particle_hole(matmul(zb, b)),
                    "Station phase was incorrectly excluded by particle-hole symmetry.")
            dressed_phs_pairs += 1

    u = identity(3)
    u[1][1] = gaussian(0, 1)
    require(particle_hole(odd(u)) and not particle_hole(odd(matmul(u, h))),
            "Independent-H particle-hole counterexample failed.")
    antisymmetric = [[ZERO, ONE], [gaussian(-1), ZERO]]
    a = odd(antisymmetric)
    ia = [[multiply(gaussian(0, 1), value) for value in row] for row in a]
    require(not particle_hole(a) and particle_hole(ia),
            "Even-dimensional antisymmetric global-phase branch was lost.")

    bandwidth_cases = 0
    for energy, width in product([F(0), F(1, 7), F(-2, 5), F(3)],
                                 [F(1), F(2, 3), F(5)]):
        denominator = energy*energy+width*width
        value = gaussian(2*energy*energy/denominator, -2*energy*width/denominator)
        require(value[0]**2+value[1]**2 == 4*energy*energy/denominator,
                "Finite-bandwidth resonance norm identity failed.")
        bandwidth_cases += 1
    return {"result": "NR-R19", "signature_cases": signature_cases,
            "rank_one_commutator_cases": commutator_cases,
            "joint_qutrit_particle_hole_pairs": phs_pairs,
            "station_phase_dressed_pairs": dressed_phs_pairs,
            "independent_H_violation": 1, "even_antisymmetric_phase_guard": 1,
            "bandwidth_identities": bandwidth_cases,
            "scope": "Exact finite operator/normalization guards; all-family AM2, physical source model and full-device access remain analytic."}


def main():
    from verify_high_order_bath import verify_high_order_bath
    from native_matter_guards import verify_native_matter_guards
    from private_program_guards import verify as private_program_checks
    from pair_memory_qualification_guards import verify as pair_memory_qualification_checks
    from loss_memory_qualification_guards import verify as loss_memory_qualification_checks
    cases = sum(echo_check(a, b) for d in [2, 3] for a, b in pairs(d))
    example = heldout_counterexample()
    contrast = record_correlation_check()
    symbolic = symbolic_ramsey_checks()
    exchange = exchange_backaction_checks()
    odd_couplers = odd_coupler_checks()
    andreev_native = andreev_native_checks()
    print(json.dumps({"status": "passed", "flagged_full_choi_cases": cases,
                      "data_dimensions": [2, 3], "arithmetic": "exact Gaussian rational",
                      "ordinary_three_window_record_contrast": contrast,
                      "symbolic_ramsey_and_storage": symbolic,
                      "exchange_backaction": exchange,
                      "odd_couplers": odd_couplers,
                      "andreev_native_interface": andreev_native,
                      "passive_native_converter_guards": native_converter_checks(),
                      "high_order_calibration_guard": verify_high_order_bath(),
                      "native_matter_controls": verify_native_matter_guards(),
                      "private_program_resources": private_program_checks(),
                      "pair_memory_qualification": pair_memory_qualification_checks(),
                      "loss_memory_qualification": loss_memory_qualification_checks(),
                      "scope": "NR-R14/NR-R19 exact finite full-instrument, exchange norm-factor, scalar polynomial, odd-coupler, Andreev-interface and private-program resource/factory replay; universal proofs, privacy/security, access and physical-cost statements remain analytic. Ordinary dedicated-pair and parallel classical-phase qualification adds finite channel/record/statistical-constant ingredients under explicit model, calibration and production premises. Loss-memory qualification adds finite collective/retained-output, decoded-channel, parity-recovery and actual-history guards; general bounds, concentration, physical bath/control and clock assumptions remain analytic or supplied. Separate dual-rail projector/independent-seed routes add finite full-reference success/loss guards under declared common-success four-mode ports, without a universal herald or hardware claim. Multiple-survivor collection adds finite common-pure-vacuum/final-sector and population-collection ingredients with additional CNOT, garbage-reset and active-recovery premises; its general bounds and calibration remain analytic. A separate unequal-vacuum boundary witness includes its paid one-word controlled-conjugation ordinary closure; no physical port or advantage follows. Collective fixed-deadline guards add exact ideal-code, projected-H, declared thermal/phase and heating-normalization ingredients; device-channel identification and control costs remain analytic or supplied. Protected-helper one-bit transfer adds literal reference and same-POVM/different-instrument guards with pre-wait alignment and spectator-safe readout premises; it does not infer a bypass from measurement statistics alone.",
                      "counterexample": example}, sort_keys=True))


if __name__ == "__main__":
    main()
