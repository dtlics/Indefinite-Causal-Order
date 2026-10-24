"""Exact finite replay of ordinary binary/CSS fault-flag controllers.

The analytic closed-controller lower bound and physical resource assumptions
belong to the linked NR-R06 method. This checks finite matrix identities and
complete weighted instruments, not an all-strategy lower bound or native
hardware implementation. Separate replay groups cover the seven-level
CSS controller and a bank with intermediate recorded read/reset.
Standard library only; no files are written.
"""

from fractions import Fraction as F
import json
import sys


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def matrix(rows):
    return tuple(tuple(F(value) for value in row) for row in rows)


def zeros(rows, columns):
    return matrix([[0] * columns for _ in range(rows)])


def identity(size):
    return matrix([[int(i == j) for j in range(size)] for i in range(size)])


def add(left, right):
    require(len(left) == len(right) and len(left[0]) == len(right[0]),
            "Matrix addition dimensions")
    return tuple(tuple(x + y for x, y in zip(a, b))
                 for a, b in zip(left, right))


def scale(value, operand):
    return tuple(tuple(value * entry for entry in row) for row in operand)


def multiply(left, right):
    require(len(left[0]) == len(right), "Matrix multiplication dimensions")
    return tuple(tuple(sum((x * y for x, y in zip(row, column) if x and y), F(0))
                       for column in zip(*right)) for row in left)


def transpose(operand):
    """All replay fixtures are real rational, so this is also the adjoint."""
    return tuple(tuple(column) for column in zip(*operand))


def tensor(left, right):
    return tuple(tuple(x * y for x in row_left for y in row_right)
                 for row_left in left for row_right in right)


def conjugate(operator, operand):
    return multiply(multiply(operator, operand), transpose(operator))


def trace(operand):
    return sum(operand[i][i] for i in range(len(operand)))


def partial_trace_helper(operand, data_dimension):
    require(len(operand) == 3 * data_dimension
            and len(operand[0]) == 3 * data_dimension,
            "Qutrit partial trace dimensions")
    return tuple(tuple(sum(operand[h * data_dimension + i]
                                     [h * data_dimension + j]
                           for h in range(3))
                       for j in range(data_dimension))
                 for i in range(data_dimension))


def weighted_instrument(isometries, weights, effect, matrix_unit, dimension):
    output = zeros(dimension, dimension)
    projector = tensor(effect, identity(dimension))
    for word, isometry in isometries.items():
        selected = multiply(projector, isometry)
        branch = partial_trace_helper(conjugate(selected, matrix_unit),
                                      dimension)
        output = add(output, scale(weights[word], branch))
    return output


def hr_dot(a, b):
    return (a & b).bit_count() % 2


def hr_character(a, b):
    return F(-1 if hr_dot(a, b) else 1)


def hr_permutation(images):
    require(sorted(images) == list(range(len(images))), "Higher-rank permutation")
    return matrix([[int(i == images[j]) for j in range(len(images))]
                   for i in range(len(images))])


def hr_first_representation(a, size):
    return hr_permutation([j ^ a if j < size else j
                           for j in range(2 * size - 1)])


def hr_second_representation(b, size):
    images = list(range(2 * size - 1))
    for label in range(1, size):
        if hr_dot(label, b):
            minus = size + label - 1
            images[label], images[minus] = images[minus], images[label]
    return hr_permutation(images)


def hr_x_string(a, size):
    return hr_permutation([j ^ a for j in range(size)])


def hr_z_string(b, size):
    return matrix([[hr_character(b, i) if i == j else 0
                    for j in range(size)] for i in range(size)])


def hr_character_projectors(representation, size):
    dimension = len(representation[0])
    projectors = []
    for c in range(size):
        projector = zeros(dimension, dimension)
        for a in range(size):
            projector = add(projector, scale(hr_character(a, c) / size,
                                             representation[a]))
        projectors.append(projector)
    return tuple(projectors)


def hr_reduced_matrix_unit(isometry, i, j, size, helper_indices):
    """Trace selected helper rows of A |i><j| A^dagger; real fixtures."""
    return tuple(tuple(sum((isometry[h * size + row][i]
                            * isometry[h * size + column][j]
                            for h in helper_indices), F(0))
                       for column in range(size)) for row in range(size))


def hr_operator_matrix_unit(operator, i, j):
    return tuple(tuple(operator[row][i] * operator[column][j]
                       for column in range(len(operator)))
                 for row in range(len(operator)))


def hr_fault_laws(size):
    denominator = F(size * (size + 1), 2)
    return (
        {(a, b): F(1, size * size)
         for a in range(size) for b in range(size)},
        {(a, b): F(a + 1) * (size - b) / denominator ** 2
         for a in range(size) for b in range(size)},
    )


def hr_verify():
    counts = {"character_projectors": 0, "group_products": 0,
              "full_echo_identities": 0, "full_branch_isometries": 0,
              "flagged_branch_matrix_unit_maps": 0, "weighted_law_cases": 0,
              "weighted_flag_matrix_unit_maps": 0}
    cases = []
    for k in (1, 2):
        size = 1 << k
        helper_dimension = 2 * size - 1
        helper_identity = identity(helper_dimension)
        data_identity = identity(size)
        joint_identity = identity(helper_dimension * size)
        first = tuple(hr_first_representation(a, size) for a in range(size))
        second = tuple(hr_second_representation(b, size) for b in range(size))
        xs = tuple(hr_x_string(a, size) for a in range(size))
        zs = tuple(hr_z_string(b, size) for b in range(size))
        first_projectors = hr_character_projectors(first, size)
        second_projectors = hr_character_projectors(second, size)
        for representation, projectors in ((first, first_projectors),
                                            (second, second_projectors)):
            require(representation[0] == helper_identity,
                    "Higher-rank identity group element")
            for a in range(size):
                require(transpose(representation[a]) == representation[a],
                        "Higher-rank Hermitian involution")
                for b in range(size):
                    require(multiply(representation[a], representation[b])
                            == representation[a ^ b], "Higher-rank group law")
                    counts["group_products"] += 1
            total = zeros(helper_dimension, helper_dimension)
            for c, projector in enumerate(projectors):
                require(transpose(projector) == projector
                        and multiply(projector, projector) == projector,
                        "Higher-rank orthogonal character projector")
                require(trace(projector) == (size if c == 0 else 1),
                        "Higher-rank projector rank M,1,...,1")
                for other in range(c):
                    require(multiply(projector, projectors[other])
                            == zeros(helper_dimension, helper_dimension),
                            "Higher-rank mutually orthogonal projectors")
                total = add(total, projector)
                counts["character_projectors"] += 1
            require(total == helper_identity, "Higher-rank complete resolution")
            for a in range(size):
                reconstructed = zeros(helper_dimension, helper_dimension)
                for c in range(size):
                    reconstructed = add(reconstructed,
                                        scale(hr_character(a, c), projectors[c]))
                require(reconstructed == representation[a],
                        "Higher-rank exact character inversion")

        cz = zeros(helper_dimension * size, helper_dimension * size)
        cx = zeros(helper_dimension * size, helper_dimension * size)
        for c in range(size):
            cz = add(cz, tensor(first_projectors[c], zs[c]))
            cx = add(cx, tensor(second_projectors[c], xs[c]))
        require(transpose(cz) == cz and multiply(cz, cz) == joint_identity,
                "Higher-rank first Hermitian unitary check")
        require(transpose(cx) == cx and multiply(cx, cx) == joint_identity,
                "Higher-rank second Hermitian unitary check")
        wrapped_first, wrapped_second = [], []
        for a in range(size):
            wrapped = multiply(multiply(cz, tensor(helper_identity, xs[a])), cz)
            require(wrapped == tensor(first[a], xs[a]), "Higher-rank first echo")
            wrapped_first.append(wrapped)
            wrapped = multiply(multiply(cx, tensor(helper_identity, zs[a])), cx)
            require(wrapped == tensor(second[a], zs[a]), "Higher-rank second echo")
            wrapped_second.append(wrapped)
            counts["full_echo_identities"] += 2
        if k == 1:
            require(first[1] == matrix([[0, 1, 0], [1, 0, 0], [0, 0, 1]])
                    and second[1] == matrix([[1, 0, 0], [0, 0, 1], [0, 1, 0]]),
                    "Higher-rank k=1 reduces to the qutrit controller")

        embedding = matrix([[int(i == j) for j in range(size)]
                            for i in range(helper_dimension * size)])
        sectors = (tuple(range(size)), tuple(range(size, helper_dimension)))
        require(sorted(sectors[0] + sectors[1]) == list(range(helper_dimension)),
                "Higher-rank complete binary helper sectors")
        branches, targets = {}, {}
        native = {0: {}, 1: {}}
        for a in range(size):
            for b in range(size):
                target = multiply(zs[b], xs[a])
                reverse = multiply(xs[a], zs[b])
                require(reverse == scale(hr_character(a, b), target),
                        "Higher-rank data commutator character")
                actual = multiply(multiply(wrapped_second[b], wrapped_first[a]),
                                  embedding)
                helper_word = multiply(second[b], first[a])
                require(actual == multiply(tensor(helper_word, target), embedding),
                        "Higher-rank complete phase-free fault word")
                label = size + a - 1 if hr_dot(a, b) else a
                expected = matrix([[target[i % size][j]
                                    if i // size == label else 0
                                    for j in range(size)]
                                   for i in range(helper_dimension * size)])
                require(actual == expected, "Higher-rank helper label")
                require(multiply(transpose(actual), actual) == data_identity,
                        "Higher-rank branch normalization")
                branches[a, b], targets[a, b] = actual, target
                for flag in (0, 1):
                    native[flag][a, b] = scale(
                        F(1, 2), add(target, scale(1 if flag == 0 else -1, reverse)))
                    for i in range(size):
                        for j in range(size):
                            actual_map = hr_reduced_matrix_unit(actual, i, j, size,
                                                                sectors[flag])
                            require(actual_map == hr_operator_matrix_unit(
                                native[flag][a, b], i, j),
                                "Higher-rank full-word flagged matrix-unit map")
                            require(trace(actual_map)
                                    == int(flag == hr_dot(a, b)) * int(i == j),
                                    "Higher-rank deterministic full-input flag")
                            counts["flagged_branch_matrix_unit_maps"] += 1
                counts["full_branch_isometries"] += 1

        for law_index, weights in enumerate(hr_fault_laws(size)):
            require(sum(weights.values()) == 1 and min(weights.values()) > 0,
                    "Higher-rank positive normalized fault law")
            minus_probability = sum(weight for (a, b), weight in weights.items()
                                    if hr_dot(a, b))
            if law_index == 0:
                require(minus_probability == F(size - 1, 2 * size),
                        "Higher-rank uniform minus probability")
            normalization = zeros(size, size)
            for word, branch in branches.items():
                normalization = add(normalization, scale(
                    weights[word], multiply(transpose(branch), branch)))
            require(normalization == data_identity,
                    "Higher-rank complete weighted normalization")
            for i in range(size):
                for j in range(size):
                    combined = zeros(size, size)
                    for flag in (0, 1):
                        actual_map, expected_map = zeros(size, size), zeros(size, size)
                        for word, branch in branches.items():
                            actual_map = add(actual_map, scale(weights[word],
                                hr_reduced_matrix_unit(branch, i, j, size,
                                                       sectors[flag])))
                            expected_map = add(expected_map, scale(weights[word],
                                hr_operator_matrix_unit(native[flag][word], i, j)))
                        require(actual_map == expected_map,
                                "Higher-rank weighted flagged instrument")
                        probability = minus_probability if flag else 1 - minus_probability
                        require(trace(actual_map) == probability * int(i == j),
                                "Higher-rank weighted flag probability")
                        combined = add(combined, actual_map)
                        counts["weighted_flag_matrix_unit_maps"] += 1
                    composed = zeros(size, size)
                    for word, target in targets.items():
                        composed = add(composed, scale(weights[word],
                            hr_operator_matrix_unit(target, i, j)))
                    require(combined == composed and trace(combined) == int(i == j),
                            "Higher-rank summed flags preserve data and trace")
            counts["weighted_law_cases"] += 1
        cases.append({"k": k, "M": size, "data": size,
                      "helper_dimension": helper_dimension})
    return dict(counts, status="passed", cases=cases,
                scope="CSS X^a/Z^b finite family; no k=2 dimension-optimality or native hardware claim")


def reset_verify():
    """Replay both bank checks, intermediate X readout and recorded reset."""
    cases = []
    fine_operators = 0
    fine_matrix_unit_maps = 0
    coarse_matrix_unit_maps = 0
    intermediate_maps = 0
    for k in (1, 2):
        size = 1 << k
        data_identity = identity(size)
        meter_identity = identity(size)
        xs = tuple(hr_x_string(a, size) for a in range(size))
        zs = tuple(hr_z_string(b, size) for b in range(size))
        chi = tuple(tuple(hr_character(r, c) for c in range(size))
                    for r in range(size))
        projectors, resets = [], []
        reset_normalization = zeros(size, size)
        for r in range(size):
            projector = matrix([[chi[r][i] * chi[r][j] / size
                                 for j in range(size)] for i in range(size)])
            require(multiply(projector, projector) == projector
                    and transpose(projector) == projector and trace(projector) == 1,
                    "Recorded X-bank readout projector")
            reset = multiply(zs[r], projector)
            expected_reset = matrix([[chi[r][j] / size for j in range(size)]
                                     for _ in range(size)])
            require(reset == expected_reset,
                    "Record-conditioned Z reset returns the plus meter")
            reset_normalization = add(reset_normalization,
                                      multiply(transpose(reset), reset))
            projectors.append(projector)
            resets.append(reset)
        require(reset_normalization == meter_identity,
                "Complete read/reset bank without postselection")
        require(all(sum((projectors[r][i][j] for r in range(size)), F(0))
                    == meter_identity[i][j]
                    for i in range(size) for j in range(size)),
                "Complete X-bank projective measurement")

        bank_z, bank_x = zeros(size * size, size * size), zeros(size * size, size * size)
        for c in range(size):
            computational = matrix([[int(i == c and j == c)
                                     for j in range(size)] for i in range(size)])
            bank_z = add(bank_z, tensor(computational, zs[c]))
            bank_x = add(bank_x, tensor(computational, xs[c]))
        require(transpose(bank_z) == bank_z
                and multiply(bank_z, bank_z) == identity(size * size),
                "Actual computational-bank controlled Z gates")
        require(transpose(bank_x) == bank_x
                and multiply(bank_x, bank_x) == identity(size * size),
                "Actual computational-bank controlled X gates")
        # This source has norm squared M. All physical CP maps below divide
        # the helper trace by M, accounting for the initial |+>^k normalization.
        source = matrix([[int(i % size == j) for j in range(size)]
                         for i in range(size * size)])
        require(multiply(transpose(source), source) == scale(size, data_identity),
                "Unnormalized plus-meter source and its exact norm")
        for a in range(size):
            wrapped_a = multiply(multiply(bank_z, tensor(meter_identity, xs[a])), bank_z)
            require(wrapped_a == tensor(zs[a], xs[a]),
                    "Actual first bank echo with meter phase syndrome")
            after_a = multiply(wrapped_a, source)
            for b in range(size):
                wrapped_b = multiply(multiply(bank_x, tensor(meter_identity, zs[b])), bank_x)
                require(wrapped_b == tensor(zs[b], zs[b]),
                        "Actual second bank echo with meter phase syndrome")
                target = multiply(zs[b], xs[a])
                reverse = multiply(xs[a], zs[b])
                fine = {}
                normalization = zeros(size, size)
                for read_a in range(size):
                    after_read_a = multiply(tensor(resets[read_a], data_identity), after_a)
                    expected_mid = multiply(source, xs[a]) if read_a == a else zeros(size * size, size)
                    require(after_read_a == expected_mid,
                            "Intermediate X readout and conditional meter reset")
                    intermediate_maps += 1
                    for read_b in range(size):
                        actual = multiply(tensor(resets[read_b], data_identity),
                                          multiply(wrapped_b, after_read_a))
                        expected = (multiply(source, target)
                                    if read_a == a and read_b == b
                                    else zeros(size * size, size))
                        require(actual == expected,
                                "Complete two-read recorded fault-word operator")
                        normalization = add(normalization, scale(F(1, size),
                            multiply(transpose(actual), actual)))
                        fine[read_a, read_b] = actual
                        fine_operators += 1
                require(normalization == data_identity,
                        "Complete fine-record instrument including initial norm")
                for i in range(size):
                    for j in range(size):
                        coarse = [zeros(size, size), zeros(size, size)]
                        for (read_a, read_b), actual in fine.items():
                            actual_map = scale(F(1, size), hr_reduced_matrix_unit(
                                actual, i, j, size, range(size)))
                            expected_map = (hr_operator_matrix_unit(target, i, j)
                                            if read_a == a and read_b == b
                                            else zeros(size, size))
                            require(actual_map == expected_map,
                                    "Full-input fine-record matrix-unit map")
                            require(trace(actual_map)
                                    == int(read_a == a and read_b == b) * int(i == j),
                                    "Correct normalized probability for both readouts")
                            flag = hr_dot(read_a, read_b)
                            coarse[flag] = add(coarse[flag], actual_map)
                            fine_matrix_unit_maps += 1
                        for flag in (0, 1):
                            native_kraus = scale(F(1, 2), add(target,
                                scale(1 if flag == 0 else -1, reverse)))
                            require(coarse[flag] == hr_operator_matrix_unit(native_kraus, i, j),
                                    "Recorded/reset upper matches complete coarse SWITCH instrument")
                            coarse_matrix_unit_maps += 1
                        require(trace(add(coarse[0], coarse[1])) == int(i == j),
                                "Recorded/reset upper preserves full data trace")
        cases.append({"k": k, "M": size, "data": size,
                      "clean_meter_qubits": k, "binary_readout_bits": 2 * k,
                      "actual_queries_per_branch": 2})
    return {"status": "passed", "cases": cases,
            "fine_record_operators": fine_operators,
            "intermediate_read_reset_maps": intermediate_maps,
            "fine_record_matrix_unit_maps": fine_matrix_unit_maps,
            "coarse_flag_matrix_unit_maps": coarse_matrix_unit_maps,
            "scope": "CSS family with priced intermediate readout, retained classical records and conditional reset; outside the closed-controller lower bound"}


def verify():
    x = matrix([[0, 1], [1, 0]])
    z = matrix([[1, 0], [0, -1]])
    s = matrix([[0, 1, 0], [1, 0, 0], [0, 0, 1]])
    r = matrix([[1, 0, 0], [0, 0, 1], [0, 1, 0]])
    i3 = identity(3)
    plus = matrix([[1, 0, 0], [0, 1, 0], [0, 0, 0]])
    minus = matrix([[0, 0, 0], [0, 0, 0], [0, 0, 1]])
    require(multiply(s, s) == i3 and transpose(s) == s,
            "First qutrit swap is a Hermitian involution")
    require(multiply(r, r) == i3 and transpose(r) == r,
            "Second qutrit swap is a Hermitian involution")
    require(add(plus, minus) == i3
            and multiply(plus, plus) == plus
            and multiply(minus, minus) == minus
            and multiply(plus, minus) == zeros(3, 3),
            "Complete orthogonal binary qutrit PVM")

    rates = ((F(0), F(0)), (F(1), F(0)), (F(0), F(1)),
             (F(1), F(1)), (F(3, 7), F(2, 5)),
             (F(4, 9), F(5, 8)))
    fixtures = ((x, z), (tensor(x, x), tensor(z, identity(2))))
    branch_count = 0
    weighted_cases = 0
    matrix_unit_maps = 0

    for p_operator, q_operator in fixtures:
        dimension = len(p_operator)
        data_identity = identity(dimension)
        require(transpose(p_operator) == p_operator
                and transpose(q_operator) == q_operator,
                "Hermitian real Pauli fixtures")
        require(multiply(p_operator, p_operator) == data_identity
                and multiply(q_operator, q_operator) == data_identity,
                "Pauli involution fixtures")
        require(multiply(p_operator, q_operator)
                == scale(-1, multiply(q_operator, p_operator)),
                "Anticommuting Pauli fixtures")

        cq = add(tensor(scale(F(1, 2), add(i3, s)), data_identity),
                 tensor(scale(F(1, 2), add(i3, scale(-1, s))), q_operator))
        cp = add(tensor(scale(F(1, 2), add(i3, r)), data_identity),
                 tensor(scale(F(1, 2), add(i3, scale(-1, r))), p_operator))
        require(multiply(cq, cq) == identity(3 * dimension)
                and transpose(cq) == cq,
                "Known first controlled Pauli is Hermitian unitary")
        require(multiply(cp, cp) == identity(3 * dimension)
                and transpose(cp) == cp,
                "Known second controlled Pauli is Hermitian unitary")

        embedding = matrix([[int(i == j) for j in range(dimension)]
                            for i in range(3 * dimension)])
        isometries = {}
        native = {0: {}, 1: {}}
        targets = {}
        for a in (0, 1):
            for b in (0, 1):
                pa = p_operator if a else data_identity
                qb = q_operator if b else data_identity
                wrapped_a = multiply(multiply(cq, tensor(i3, pa)), cq)
                wrapped_b = multiply(multiply(cp, tensor(i3, qb)), cp)
                require(wrapped_a == tensor(s if a else i3, pa),
                        "First complete wrapped fault identity")
                require(wrapped_b == tensor(r if b else i3, qb),
                        "Second complete wrapped fault identity")
                actual = multiply(multiply(wrapped_b, wrapped_a), embedding)
                target = multiply(qb, pa)
                label = 2 if a * b else a
                expected = matrix([[target[i % dimension][j]
                                    if i // dimension == label else 0
                                    for j in range(dimension)]
                                   for i in range(3 * dimension)])
                require(actual == expected, "Full fault-word isometry")
                require(multiply(transpose(actual), actual) == data_identity,
                        "Fault-word isometry normalization")
                for flag, effect in ((0, plus), (1, minus)):
                    selected = multiply(tensor(effect, data_identity), actual)
                    require(selected == (actual if flag == a * b
                                         else zeros(3 * dimension, dimension)),
                            "Correct deterministic coarse fault flag")
                    native[flag][a, b] = scale(
                        F(1, 2), add(target, scale(1 if flag == 0 else -1,
                                                   multiply(pa, qb))))
                isometries[a, b] = actual
                targets[a, b] = target
                branch_count += 1

        for p_rate, q_rate in rates:
            weights = {(a, b): (p_rate if a else 1 - p_rate)
                       * (q_rate if b else 1 - q_rate)
                       for a in (0, 1) for b in (0, 1)}
            require(sum(weights.values()) == 1 and min(weights.values()) >= 0,
                    "Complete nonnegative classical fault law")
            normalization = zeros(dimension, dimension)
            for word, actual in isometries.items():
                normalization = add(normalization, scale(
                    weights[word], multiply(transpose(actual), actual)))
            require(normalization == data_identity,
                    "Complete weighted ordinary Kraus normalization")
            for i in range(dimension):
                for j in range(dimension):
                    unit = matrix([[int(k == i and ell == j)
                                    for ell in range(dimension)]
                                   for k in range(dimension)])
                    combined = zeros(dimension, dimension)
                    for flag, effect in ((0, plus), (1, minus)):
                        actual = weighted_instrument(isometries, weights,
                                                     effect, unit, dimension)
                        expected = zeros(dimension, dimension)
                        for word in isometries:
                            expected = add(expected, scale(
                                weights[word], conjugate(native[flag][word], unit)))
                        require(actual == expected,
                                "Weighted full matrix-unit native instrument")
                        probability = p_rate * q_rate if flag else 1 - p_rate * q_rate
                        require(trace(actual) == probability * int(i == j),
                                "Input-independent complete flag probability")
                        combined = add(combined, actual)
                        matrix_unit_maps += 1
                    ordinary_composition = zeros(dimension, dimension)
                    for word, target in targets.items():
                        ordinary_composition = add(ordinary_composition, scale(
                            weights[word], conjugate(target, unit)))
                    require(combined == ordinary_composition,
                            "Summing flags gives the ordinary composed data channel")
                    require(trace(combined) == int(i == j),
                            "Trace preservation on every matrix unit")
            weighted_cases += 1

    return {
        "status": "passed",
        "arithmetic": "exact rational; standard library",
        "data_dimensions": [2, 4],
        "helper_dimension": 3,
        "actual_queries_per_branch": 2,
        "full_fault_isometries": branch_count,
        "weighted_rate_cases": weighted_cases,
        "weighted_flag_matrix_unit_maps": matrix_unit_maps,
        "higher_rank": hr_verify(),
        "reset_upper": reset_verify(),
        "scope": ("finite exact replay of the coarse measured flag and full target "
                  "instrument for fixed pure qutrit control; analytic lower bound, "
                  "arbitrary order-control input and native hardware not certified"),
    }


if __name__ == "__main__":
    if sys.flags.optimize:
        raise SystemExit("Run exact replays without Python optimization (-O).")
    print(json.dumps(verify(), sort_keys=True))
