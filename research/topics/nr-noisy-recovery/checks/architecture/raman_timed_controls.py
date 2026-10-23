"""Exact timed-spin compiler and calibrated late-photon-flip Bell instrument.

Canonical proofs and access limits are in communication.md, NR-R11.
No solver or measured hardware model is used.
"""
from fractions import Fraction as F

from verify_fault_simulation import (
    ZERO, ONE, gaussian, add, multiply, times, zeros, identity,
    adjoint, matmul, tensor, conjugate,
)

if not __debug__:
    raise RuntimeError("Exact compiler checks require assertions; do not use -O.")


def scale(matrix, scalar):
    return [[multiply(scalar, value) for value in row] for row in matrix]


def matrix_add(left, right):
    return [[add(a, b) for a, b in zip(ra, rb)] for ra, rb in zip(left, right)]


def product(*matrices):
    result = matrices[0]
    for matrix in matrices[1:]:
        result = matmul(result, matrix)
    return result


def embedded_gate(gate, site, qubits):
    result = [[ONE]]
    for position in range(qubits):
        result = tensor(result, gate if position == site else identity(2))
    return result


def controlled_gate(gates, helper_site, target_site, qubits):
    size = 2 ** qubits
    result = zeros(size, size)
    for source in range(size):
        bits = [(source >> (qubits-1-k)) & 1 for k in range(qubits)]
        for target_bit in range(2):
            value = gates[bits[helper_site]][target_bit][bits[target_site]]
            output_bits = bits[:]
            output_bits[target_site] = target_bit
            target = sum(bit << (qubits-1-k) for k, bit in enumerate(output_bits))
            result[target][source] = value
    return result


def swap_sites(first, second, qubits):
    size = 2 ** qubits
    result = zeros(size, size)
    for source in range(size):
        bits = [(source >> (qubits-1-k)) & 1 for k in range(qubits)]
        bits[first], bits[second] = bits[second], bits[first]
        target = sum(bit << (qubits-1-k) for k, bit in enumerate(bits))
        result[target][source] = ONE
    return result


def _verify_timed_compiler():
    ident = identity(2)
    x = [[ZERO, ONE], [ONE, ZERO]]
    y = [[ZERO, gaussian(0, -1)], [gaussian(0, 1), ZERO]]
    z = [[ONE, ZERO], [ZERO, gaussian(-1)]]
    phase = [[ONE, ZERO], [ZERO, gaussian(0, 1)]]
    rotation = [[gaussian(F(3, 5)), gaussian(F(4, 5))],
                [gaussian(F(-4, 5)), gaussian(F(3, 5))]]
    unitaries = [ident, x, y, z, phase, rotation, matmul(phase, rotation)]
    swap = swap_sites(0, 1, 2)
    coefficients = [
        (ONE, ZERO), (ZERO, ONE),
        (gaussian(F(1, 3), F(1, 7)), gaussian(F(-2, 5), F(1, 11))),
        (gaussian(F(-1, 4), F(1, 8)), gaussian(F(2, 7), F(-1, 9))),
    ]
    one_node_cases = 0
    for unitary in unitaries:
        assert matmul(adjoint(unitary), unitary) == ident
        for a, b in coefficients:
            node = matrix_add(scale(identity(4), a), scale(swap, b))
            spin_version = product(tensor(ident, adjoint(unitary)), node,
                                   tensor(ident, unitary))
            photon_version = product(tensor(unitary, ident), node,
                                     tensor(adjoint(unitary), ident))
            assert spin_version == photon_version
            one_node_cases += 1

    # A known nontrivial Raman-leg frame changes the required photon gate.
    # Without that frame, substituting the lab spin gate is not valid.
    frame = phase
    twisted_swap = product(tensor(ident, frame), swap,
                           tensor(ident, adjoint(frame)))
    twisted_frame_cases = 0
    for unitary in unitaries:
        photon_gate = product(adjoint(frame), unitary, frame)
        for a, b in coefficients[:2]:
            node = matrix_add(scale(identity(4), a), scale(twisted_swap, b))
            actual = product(tensor(ident, adjoint(unitary)), node,
                             tensor(ident, unitary))
            compiled = product(tensor(photon_gate, ident), node,
                               tensor(adjoint(photon_gate), ident))
            assert actual == compiled
            twisted_frame_cases += 1
    assert product(tensor(ident, x), twisted_swap, tensor(ident, x)) != (
        product(tensor(x, ident), twisted_swap, tensor(x, ident)))

    # Equality of accepted no-loss operators alone does not determine
    # rejected spin/bath outputs. A valid all-loss/reset channel has
    # T=0; spin conjugation changes its reset state, photon conjugation
    # does not. This is a scope guard, not a SPRINT hardware model.
    loss_kraus = []
    loss_effect = zeros(4, 4)
    spin_loss_output = zeros(2, 2)
    photon_loss_output = zeros(2, 2)
    for column in range(4):
        loss = zeros(2, 4)
        loss[0][column] = ONE
        loss_kraus.append(loss)
        loss_effect = matrix_add(loss_effect, matmul(adjoint(loss), loss))
        spin_loss = product(x, loss, tensor(ident, x))
        photon_loss = product(loss, tensor(x, ident))
        for i in range(2):
            for j in range(2):
                spin_loss_output[i][j] = add(spin_loss_output[i][j],
                    multiply(spin_loss[i][0], conjugate(spin_loss[j][0])))
                photon_loss_output[i][j] = add(photon_loss_output[i][j],
                    multiply(photon_loss[i][0], conjugate(photon_loss[j][0])))
    assert loss_effect == identity(4)
    assert spin_loss_output == [[ZERO, ZERO], [ZERO, ONE]]
    assert photon_loss_output == [[ONE, ZERO], [ZERO, ZERO]]

    # Register order P,H,A,B. The middle photon gate mixes H and P,
    # so it does not commute with the helper-controlled compiler gates.
    helper_rotation = embedded_gate(rotation, 1, 4)
    photon_phase = embedded_gate(phase, 0, 4)
    cnot_photon_to_helper = controlled_gate([ident, x], 0, 1, 4)
    middle = product(helper_rotation, cnot_photon_to_helper, photon_phase)
    swap_a = swap_sites(0, 2, 4)
    swap_b = swap_sites(0, 3, 4)
    common_output = product(embedded_gate(phase, 2, 4),
                            embedded_gate(rotation, 3, 4))
    configurations = [([ident, x], [y, z]),
                      ([phase, rotation], [rotation, matmul(phase, rotation)]),
                      ([matmul(phase, rotation), y], [x, phase])]
    two_node_cases = 0
    for controls_a, controls_b in configurations:
        spin_a = controlled_gate(controls_a, 1, 2, 4)
        spin_b = controlled_gate(controls_b, 1, 3, 4)
        photon_a = controlled_gate(controls_a, 1, 0, 4)
        photon_b = controlled_gate(controls_b, 1, 0, 4)
        assert matmul(middle, photon_a) != matmul(photon_a, middle)
        compiled_middle = product(adjoint(photon_b), middle, photon_a)
        node_pairs = [(a, b) for a in (identity(16), swap_a)
                      for b in (identity(16), swap_b)]
        node_pairs.append((matrix_add(scale(identity(16), coefficients[2][0]),
                                       scale(swap_a, coefficients[2][1])),
                           matrix_add(scale(identity(16), coefficients[3][0]),
                                       scale(swap_b, coefficients[3][1]))))
        for node_a, node_b in node_pairs:
            original = product(common_output, adjoint(spin_b), node_b, spin_b,
                               middle, adjoint(spin_a), node_a, spin_a)
            compiled = product(common_output, photon_b, node_b,
                               compiled_middle, node_a, adjoint(photon_a))
            assert original == compiled
            two_node_cases += 1

    # Essential guard: helper-changing coefficient operators do not
    # commute through helper-controlled photon/spin conjugations.
    changed_helper = embedded_gate(x, 0, 3)  # order H,P,S
    spin_control = controlled_gate([ident, z], 0, 2, 3)
    photon_control = controlled_gate([ident, z], 0, 1, 3)
    wrong_spin = product(adjoint(spin_control), changed_helper, spin_control)
    wrong_photon = product(photon_control, changed_helper, adjoint(photon_control))
    assert wrong_spin != wrong_photon

    # Physical SU(2) pulse phases: four coherent Pauli bins, common
    # restored vacuum frame, and all independent paired-Pauli frames.
    rx = scale(x, gaussian(0, -1))
    ry = scale(y, gaussian(0, -1))
    ry_back = scale(y, gaussian(0, 1))
    frames = [ident, rx, scale(z, gaussian(0, 1)), ry]
    pulses = [rx, ry, rx, ry_back]
    current = ident
    chronology_cases = 0
    for index, pulse in enumerate(pulses):
        assert current == frames[index]
        pre = ident
        for before in pulses[:index]:
            pre = matmul(before, pre)
        post = ident
        for after in pulses[index:]:
            post = matmul(after, post)
        assert matmul(post, pre) == ident
        for node in (identity(4), swap):
            assert product(tensor(ident, post), node, tensor(ident, pre)) == (
                product(tensor(ident, adjoint(frames[index])), node,
                        tensor(ident, frames[index])))
            chronology_cases += 1
        current = matmul(pulse, current)
    assert current == ident
    pairs = []
    for b in range(4):
        order = range(4) if b % 2 == 0 else reversed(range(4))
        pairs.extend((a, b) for a in order)
    assert len(set(pairs)) == 16
    pulse_counts = [0, 0]
    for before, after in zip(pairs, pairs[1:] + [(0, 0)]):
        for site in range(2):
            if before[site] == after[site]:
                continue
            transition = matmul(frames[after[site]], adjoint(frames[before[site]]))
            assert transition in (rx, ry, adjoint(rx), adjoint(ry))
            pulse_counts[site] += 1
    assert pulse_counts == [12, 4]
    return {"one_node_full_operator_cases": one_node_cases,
            "known_twisted_frame_cases": twisted_frame_cases,
            "unknown_twisted_frame_counterexamples": 1,
            "accepted_only_loss_instrument_counterexamples": 1,
            "two_node_full_operator_cases": two_node_cases,
            "chronological_polynomial_cases": chronology_cases,
            "helper_preservation_counterexamples": 1,
            "four_pauli_frame_physical_pi_pulses": 4,
            "sixteen_paired_frames_physical_pi_pulses": pulse_counts,
            "scope": "Exact known-frame compiler and pulse schedule; no Bell-yield optimum or native cost equivalence."}


def _poly_clean(values):
    values = list(values)
    while len(values) > 1 and values[-1] == 0:
        values.pop()
    return tuple(values)


def _poly_add(left, right):
    result = [F(0)] * max(len(left), len(right))
    for index, value in enumerate(left):
        result[index] += value
    for index, value in enumerate(right):
        result[index] += value
    return _poly_clean(result)


def _poly_scale(scalar, polynomial):
    return _poly_clean([scalar * value for value in polynomial])


def _poly_subtract(left, right):
    return _poly_add(left, _poly_scale(-1, right))


def _poly_multiply(left, right):
    result = [F(0)] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i+j] += a * b
    return _poly_clean(result)


def _poly_evaluate(polynomial, value):
    result = F(0)
    for coefficient in reversed(polynomial):
        result = result * value + coefficient
    return result


def _verify_calibrated_late_flip():
    """Full polynomial state and all-launch success/rejection accounting."""
    zero, one = (F(0),), (F(1),)
    beta, t = (F(0), F(1)), (F(1), F(-1))
    beta2 = _poly_multiply(beta, beta)
    beta3 = _poly_multiply(beta2, beta)
    beta4 = _poly_multiply(beta2, beta2)
    t2 = _poly_multiply(t, t)

    def add_states(left, right):
        return [_poly_add(a, b) for a, b in zip(left, right)]

    def scale_state(polynomial, state):
        return [_poly_multiply(polynomial, value) for value in state]

    def swap_state(state, site):
        result = [zero for _ in range(16)]
        for source, value in enumerate(state):
            bits = [(source >> (3-k)) & 1 for k in range(4)]
            bits[0], bits[site] = bits[site], bits[0]
            target = sum(bit << (3-k) for k, bit in enumerate(bits))
            result[target] = _poly_add(result[target], value)
        return result

    def node(state, site):
        return add_states(scale_state(t, state),
                          scale_state(beta, swap_state(state, site)))

    # Unnormalized source |P0,Qearly,00>+|P1,Qlate,00>, norm squared 2.
    # Physical probabilities below include its factor 1/2.
    initial = [zero for _ in range(16)]
    initial[0] = initial[12] = one
    after_a = node(initial, 2)
    middle = [zero for _ in range(16)]
    for source, value in enumerate(after_a):
        helper_is_late = (source >> 2) & 1
        target = source ^ (8 if helper_is_late else 0)
        middle[target] = _poly_add(middle[target], value)
    actual = node(middle, 3)
    expected = [zero for _ in range(16)]
    expected[0] = one
    expected[4] = t
    expected[7] = beta2
    expected[14] = _poly_multiply(beta, t)
    assert actual == expected

    # A physical passive time-bin decoder's two central-clock bras are
    # (<early| +/- <late|)/2, with total effect I/2, not I.
    central_bras = [[[gaussian(F(1, 2)), gaussian(sign * F(1, 2))]]
                    for sign in (1, -1)]
    central_effect = zeros(2, 2)
    for bra in central_bras:
        central_effect = matrix_add(central_effect, matmul(adjoint(bra), bra))
    assert central_effect == scale(identity(2), gaussian(F(1, 2)))

    denominators = []
    for sign in (1, -1):
        raw = [_poly_add(actual[spin], _poly_scale(sign, actual[4+spin]))
               for spin in range(4)]
        denominator = _poly_add(one, _poly_scale(sign, t))
        denominators.append(denominator)
        assert raw == [denominator, zero, zero, _poly_scale(sign, beta2)]
        # Applying diag(beta^2/denominator,1) balances the two amplitudes.
        # The quotient need not be introduced into the polynomial ring.
        assert _poly_multiply(raw[0], beta2) == _poly_multiply(denominator, beta2)
        filtered = [beta2, zero, zero, _poly_scale(sign, beta2)]
        norm = zero
        for amplitude in filtered:
            norm = _poly_add(norm, _poly_multiply(amplitude, amplitude))
        assert _poly_scale(F(1, 8), norm) == _poly_scale(F(1, 4), beta4)

    # Denominators are 2-beta and beta. At beta=0 the minus herald is
    # zero and rejected; the limits give the same zero Bell probability.
    assert denominators == [(F(2), F(-1)), beta]
    plus_failure_numerator = _poly_subtract(
        _poly_multiply(denominators[0], denominators[0]), beta4)
    minus_failure_numerator = _poly_subtract(beta2, beta4)
    assert plus_failure_numerator == _poly_multiply(
        _poly_multiply(t, _poly_add(beta, (F(2),))),
        _poly_add(_poly_add(beta2, t), one))
    assert minus_failure_numerator == _poly_multiply(
        _poly_multiply(beta2, t), _poly_add(one, beta))

    norm = zero
    for amplitude in actual:
        norm = _poly_add(norm, _poly_multiply(amplitude, amplitude))
    accepted_node_weight = _poly_scale(F(1, 2), norm)
    node_reject = _poly_subtract(one, accepted_node_weight)
    assert node_reject == _poly_multiply(_poly_multiply(beta, t),
                                       _poly_add(one, beta2))
    photon_p1_reject = _poly_scale(F(1, 2), _poly_multiply(beta2, t2))
    offcentral_reject = _poly_scale(F(1, 4),
        _poly_add(_poly_add(one, t2), beta4))
    spin_filter_reject = _poly_scale(F(1, 8),
        _poly_add(plus_failure_numerator, minus_failure_numerator))
    assert spin_filter_reject == _poly_scale(F(1, 4),
        _poly_multiply(t, _poly_add(_poly_add(beta3, beta2), (F(2),))))
    bell_success = _poly_scale(F(1, 2), beta4)
    total = zero
    for probability in (node_reject, photon_p1_reject, offcentral_reject,
                        spin_filter_reject, bell_success):
        total = _poly_add(total, probability)
    assert total == one

    # Comparison with the specified 4/27 passive ring, preserving its
    # construction-specific scope and equal node-attenuation assumption.
    ring_bell_success = _poly_scale(F(4, 27),
        _poly_multiply(beta2, _poly_add(one, t2)))
    threshold_polynomial = (F(-16), F(16), F(19))
    assert _poly_subtract(bell_success, ring_bell_success) == _poly_scale(
        F(1, 54), _poly_multiply(beta2, threshold_polynomial))
    # (19 beta+8)^2-16*23 = 19(19 beta^2+16 beta-16).
    root_expression = (F(8), F(19))
    assert _poly_subtract(_poly_multiply(root_expression, root_expression),
                          (F(16*23),)) == _poly_scale(19, threshold_polynomial)
    assert threshold_polynomial[1] > 0 and threshold_polynomial[2] > 0
    assert _poly_evaluate(threshold_polynomial, F(0)) < 0
    assert _poly_evaluate(threshold_polynomial, F(1)) > 0
    assert _poly_evaluate(threshold_polynomial, F(588, 1000)) < 0
    assert _poly_evaluate(threshold_polynomial, F(589, 1000)) > 0

    # Guards for transcription/endpoints; the nonnegative factorizations
    # and polynomial identities above, not this grid, establish the range.
    for numerator in range(47):
        value = F(numerator, 46)
        probabilities = [_poly_evaluate(polynomial, value) for polynomial in
            (node_reject, photon_p1_reject, offcentral_reject,
             spin_filter_reject, bell_success)]
        assert all(probability >= 0 for probability in probabilities)
        assert sum(probabilities) == 1
    nominal_beta = F(45, 46)
    nominal_ratio = (_poly_evaluate(bell_success, nominal_beta)
                     / _poly_evaluate(ring_bell_success, nominal_beta))
    assert nominal_ratio == F(54675, 16936)
    return {
        "full_symbolic_no_loss_output": True,
        "retained_central_clock_flags": 2,
        "local_filter_success_probabilities": "beta^4/4 each",
        "all_launch_bell_probability": "beta^4/2",
        "nonnegative_failure_categories": 4,
        "endpoint_transcription_guards": 47,
        "specific_ring_threshold_polynomial": "19 beta^2+16 beta-16",
        "specific_ring_threshold": "(-8+4 sqrt(23))/19",
        "nominal_beta_45_over_46_ideal_route_ratio": str(nominal_ratio),
        "scope": "Calibrated real-beta family, timed photon rail flip and specified passive central decoder/ring; no universal routing comparison.",
    }


def verify_raman_timed_controls():
    return {"timed_spin_compiler": _verify_timed_compiler(),
            "calibrated_late_photon_flip": _verify_calibrated_late_flip()}


if __name__ == "__main__":
    import json
    print(json.dumps(verify_raman_timed_controls(), indent=2))
