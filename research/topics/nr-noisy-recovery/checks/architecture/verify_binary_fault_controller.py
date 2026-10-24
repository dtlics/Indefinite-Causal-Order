"""Exact finite replay of ordinary binary/CSS fault-flag controllers.

The analytic closed-controller lower bound and physical resource assumptions
belong to the linked NR-R06 method. This checks finite matrix identities and
complete weighted instruments, not an all-strategy lower bound or native
hardware implementation. Separate replay groups cover the seven-level
CSS controller and a bank with intermediate recorded read/reset.
An additional Gaussian-rational replay covers cross-dual full-Pauli
families with internal anticommutation and inverse ordered check banks.
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


def replay_cross_dual():
    """Full n=1,2 Pauli instruments, including physical complex phases.

    The established Gaussian scalar engine supplies exact arithmetic. Sparse
    rows keep the 31-level helper fixture finite without a dense large-matrix
    multiplication. Physical Paulis come from its tensor-product basis; the
    older real helper representations supply a separate character resolution.
    No scratch source or report is imported.
    """
    import verify_fault_simulation as g

    class Sparse:
        def __init__(self, rows, columns, entries):
            self.shape = rows, columns
            self.rows = [{} for _ in range(rows)]
            for (i, j), value in entries.items():
                require(0 <= i < rows and 0 <= j < columns,
                        "Cross-dual sparse dimensions")
                if value != g.ZERO:
                    self.rows[i][j] = value

        def __eq__(self, other):
            return (isinstance(other, Sparse) and self.shape == other.shape
                    and self.rows == other.rows)

        def entries(self):
            return ((i, j, value) for i, row in enumerate(self.rows)
                    for j, value in row.items())

    def empty(rows, columns):
        return Sparse(rows, columns, {})

    def unit(size):
        return Sparse(size, size, {(i, i): g.ONE for i in range(size)})

    def from_dense(operand, real=False):
        return Sparse(len(operand), len(operand[0]),
                      {(i, j): g.gaussian(value) if real else value
                       for i, row in enumerate(operand)
                       for j, value in enumerate(row)})

    def plus(left, right):
        require(left.shape == right.shape, "Cross-dual sum dimensions")
        out = {(i, j): value for i, j, value in left.entries()}
        for i, j, value in right.entries():
            out[i, j] = g.add(out.get((i, j), g.ZERO), value)
        return Sparse(*left.shape, out)

    def times(scalar, operand):
        return Sparse(*operand.shape,
                      {(i, j): g.times(value, scalar)
                       for i, j, value in operand.entries()})

    def product(left, right):
        require(left.shape[1] == right.shape[0],
                "Cross-dual product dimensions")
        out = {}
        for i, row in enumerate(left.rows):
            for middle, x in row.items():
                for j, y in right.rows[middle].items():
                    value = y if x == g.ONE else x if y == g.ONE else g.multiply(x, y)
                    out[i, j] = g.add(out.get((i, j), g.ZERO), value)
        return Sparse(left.shape[0], right.shape[1], out)

    def adjoint(operand):
        return Sparse(operand.shape[1], operand.shape[0],
                      {(j, i): g.conjugate(value)
                       for i, j, value in operand.entries()})

    def kron(left, right):
        rows, columns = right.shape
        return Sparse(left.shape[0] * rows, left.shape[1] * columns,
                      {(i * rows + k, j * columns + ell): g.multiply(x, y)
                       for i, j, x in left.entries()
                       for k, ell, y in right.entries()})

    def tr(operand):
        out = g.ZERO
        for i, row in enumerate(operand.rows):
            out = g.add(out, row.get(i, g.ZERO))
        return out

    def matrix_unit_image(operator, i, j):
        return Sparse(operator.shape[0], operator.shape[0],
                      {(row, column): g.multiply(values[i], g.conjugate(other[j]))
                       for row, values in enumerate(operator.rows) if i in values
                       for column, other in enumerate(operator.rows) if j in other})

    def reduced_image(operator, i, j, dimension, size, flag):
        out = {}
        for row, values in enumerate(operator.rows):
            helper, data_row = divmod(row, dimension)
            if i not in values or int(helper >= size) != flag:
                continue
            for data_column in range(dimension):
                other = operator.rows[helper * dimension + data_column]
                if j in other:
                    out[data_row, data_column] = g.add(
                        out.get((data_row, data_column), g.ZERO),
                        g.multiply(values[i], g.conjugate(other[j])))
        return Sparse(dimension, dimension, out)

    def ordered_bank(generators, size, dimension):
        bank = unit(size * dimension)
        for bit, generator in enumerate(generators):
            controlled = empty(size * dimension, size * dimension)
            for label in range(size):
                control = Sparse(size, size, {(label, label): g.ONE})
                controlled = plus(controlled, kron(
                    control, generator if label & (1 << bit) else unit(dimension)))
            # Chronological order is bit 0, then bit 1, and so on.
            bank = product(controlled, bank)
        return bank

    cases = []
    counts = {name: 0 for name in (
        "cross_dual_pairs", "internal_anticommuting_ordered_pairs",
        "character_projectors", "complete_echo_identities",
        "full_fault_isometries", "closed_flag_matrix_unit_maps",
        "open_single_read_kraus", "open_fine_record_operators",
        "open_flag_matrix_unit_maps", "inverse_order_guards")}
    for n in (1, 2):
        dimension, bits = 1 << n, 2 * n
        size, helper_dimension = 1 << bits, 2 * (1 << bits) - 1
        basis = g.pauli_basis(n)
        physical = []
        # Engine basis digits are I,X,Y,Z; label bits are x below z.
        digits = {(0, 0): 0, (1, 0): 1, (1, 1): 2, (0, 1): 3}
        for label in range(size):
            index = 0
            for bit in reversed(range(n)):
                index = 4 * index + digits[((label >> bit) & 1,
                                           (label >> (n + bit)) & 1)]
            physical.append(from_dense(basis[index]))
        ps = tuple(physical)
        qs = tuple(ps[((label & (dimension - 1)) << n) | (label >> n)]
                   for label in range(size))
        data_identity = unit(dimension)
        for family in (ps, qs):
            require(any(value[1] for operator in family
                        for _, _, value in operator.entries()),
                    "Cross-dual fixtures include imaginary physical amplitudes")
            anti_count = 0
            for a, left in enumerate(family):
                require(adjoint(left) == left and product(left, left) == data_identity,
                        "Physical Pauli is a Hermitian involution")
                for right in family:
                    if product(left, right) == times(-1, product(right, left)):
                        anti_count += 1
            require(anti_count == size * size // 2 - size // 2,
                    "Full Pauli fixture has internal anticommutation")
            counts["internal_anticommuting_ordered_pairs"] += anti_count
        for a in range(size):
            for b in range(size):
                require(product(ps[a], qs[b]) == times(
                    hr_character(a, b), product(qs[b], ps[a])),
                        "All cross-dual commutation characters")
                counts["cross_dual_pairs"] += 1

        representations = (
            tuple(hr_first_representation(a, size) for a in range(size)),
            tuple(hr_second_representation(b, size) for b in range(size)))
        resolutions = []
        for representation in representations:
            dense_projectors = hr_character_projectors(representation, size)
            projectors = tuple(from_dense(p, real=True) for p in dense_projectors)
            total = empty(helper_dimension, helper_dimension)
            for c, projector in enumerate(projectors):
                require(adjoint(projector) == projector
                        and product(projector, projector) == projector,
                        "Cross-dual helper character projector")
                require(tr(projector) == g.gaussian(size if c == 0 else 1),
                        "Helper character ranks M,1,...,1")
                for other in projectors[:c]:
                    require(product(projector, other)
                            == empty(helper_dimension, helper_dimension),
                            "Cross-dual helper projector orthogonality")
                total = plus(total, projector)
                counts["character_projectors"] += 1
            require(total == unit(helper_dimension), "Complete helper resolution")
            resolutions.append(projectors)

        closed = []
        for projectors, family in zip(resolutions, (qs, ps)):
            controller = empty(helper_dimension * dimension,
                               helper_dimension * dimension)
            for projector, operator in zip(projectors, family):
                controller = plus(controller, kron(projector, operator))
            require(adjoint(controller) == controller
                    and product(controller, controller)
                    == unit(helper_dimension * dimension),
                    "Actual projector controller is a Hermitian involution")
            closed.append(controller)
        source = Sparse(helper_dimension * dimension, dimension,
                        {(j, j): g.ONE for j in range(dimension)})
        closed_words = [[], []]
        for which, (controller, family, representation) in enumerate(zip(
                closed, (ps, qs), representations)):
            for label, operator in enumerate(family):
                actual = product(product(controller, kron(unit(helper_dimension),
                                                           operator)), controller)
                expected = kron(from_dense(representation[label], real=True), operator)
                require(actual == expected, "Literal full cross-dual controller echo")
                closed_words[which].append(actual)
                counts["complete_echo_identities"] += 1
        for a in range(size):
            for b in range(size):
                target, reverse = product(qs[b], ps[a]), product(ps[a], qs[b])
                flag = hr_dot(a, b)
                label = size + a - 1 if flag else a
                actual = product(closed_words[1][b], product(closed_words[0][a], source))
                expected = Sparse(helper_dimension * dimension, dimension,
                                  {(label * dimension + row, column): value
                                   for row, column, value in target.entries()})
                require(actual == expected, "Phase-sensitive full closed fault isometry")
                require(product(adjoint(actual), actual) == data_identity,
                        "Closed fault-word isometry normalization")
                for read in (0, 1):
                    native = times(F(1, 2), plus(target, times(1 if read == 0 else -1,
                                                             reverse)))
                    for i in range(dimension):
                        for j in range(dimension):
                            image = reduced_image(actual, i, j, dimension, size, read)
                            require(image == matrix_unit_image(native, i, j),
                                    "Full complex-linear closed flag instrument")
                            require(tr(image) == g.gaussian(int(read == flag and i == j)),
                                    "Closed normalized flag probability")
                            counts["closed_flag_matrix_unit_maps"] += 1
                counts["full_fault_isometries"] += 1

        # Normalize the source/read pair jointly: J has M identical helper rows,
        # and the bra coefficient 1/M includes both physical 1/sqrt(M) factors.
        open_source = Sparse(size * dimension, dimension,
                             {(h * dimension + j, j): g.ONE
                              for h in range(size) for j in range(dimension)})
        require(product(adjoint(open_source), open_source)
                == times(size, data_identity), "Open-bank source normalization")
        read_bras, resets = [], []
        reset_complete = empty(size, size)
        for read in range(size):
            bra = Sparse(1, size, {(0, h): g.gaussian(hr_character(read, h) / size)
                                   for h in range(size)})
            projector = Sparse(size, size,
                               {(i, j): g.gaussian(hr_character(read, i ^ j) / size)
                                for i in range(size) for j in range(size)})
            z_read = Sparse(size, size,
                            {(h, h): g.gaussian(hr_character(read, h))
                             for h in range(size)})
            reset = product(z_read, projector)
            require(adjoint(projector) == projector
                    and product(projector, projector) == projector,
                    "Physical X-readout projector")
            reset_complete = plus(reset_complete, product(adjoint(reset), reset))
            read_bras.append(kron(bra, data_identity))
            resets.append(kron(reset, data_identity))
        require(reset_complete == unit(size), "Complete measured reset instrument")

        reads = [[], []]
        for which, (check_family, fault_family) in enumerate(((qs, ps), (ps, qs))):
            bank = ordered_bank(tuple(check_family[1 << bit] for bit in range(bits)),
                                size, dimension)
            joint_identity = unit(size * dimension)
            require(product(adjoint(bank), bank) == joint_identity,
                    "Ordered controlled-Pauli bank is unitary")
            require(bank != adjoint(bank) and product(bank, bank) != joint_identity,
                    "Wrong W-query-W echo fails already on the identity query")
            require(product(bank, product(bank, open_source)) != open_source,
                    "Wrong W-squared echo also fails on the initialized meter code")
            counts["inverse_order_guards"] += 1
            for label, operator in enumerate(fault_family):
                actual = product(product(adjoint(bank), kron(unit(size), operator)), bank)
                z_label = Sparse(size, size,
                                 {(h, h): g.gaussian(hr_character(label, h))
                                  for h in range(size)})
                require(actual == kron(z_label, operator),
                        "Actual inverse-order bank phase-syndrome echo")
                after = product(actual, open_source)
                normalization = empty(dimension, dimension)
                operators = []
                for read in range(size):
                    selected = product(read_bras[read], after)
                    require(selected == (operator if read == label
                                          else empty(dimension, dimension)),
                            "Normalized fine-read target Kraus operator")
                    require(product(resets[read], after) == product(open_source, selected),
                            "Middle X-read and conditional Z reset actually reuses meters")
                    normalization = plus(normalization, product(adjoint(selected), selected))
                    operators.append(selected)
                    counts["open_single_read_kraus"] += 1
                require(normalization == data_identity, "Complete single-read instrument")
                reads[which].append(operators)

        for a in range(size):
            for b in range(size):
                target, reverse = product(qs[b], ps[a]), product(ps[a], qs[b])
                coarse = [[], []]
                normalization = empty(dimension, dimension)
                for read_a in range(size):
                    for read_b in range(size):
                        selected = product(reads[1][b][read_b], reads[0][a][read_a])
                        require(selected == (target if read_a == a and read_b == b
                                              else empty(dimension, dimension)),
                                "Both retained fine records preserve complete target phase")
                        normalization = plus(normalization,
                                             product(adjoint(selected), selected))
                        if any(selected.rows):
                            coarse[hr_dot(read_a, read_b)].append(selected)
                        counts["open_fine_record_operators"] += 1
                require(normalization == data_identity, "Complete two-read instrument")
                for i in range(dimension):
                    for j in range(dimension):
                        total = empty(dimension, dimension)
                        for flag in (0, 1):
                            image = empty(dimension, dimension)
                            for selected in coarse[flag]:
                                image = plus(image, matrix_unit_image(selected, i, j))
                            native = times(F(1, 2), plus(target, times(
                                1 if flag == 0 else -1, reverse)))
                            require(image == matrix_unit_image(native, i, j),
                                    "Full complex-linear open-bank flag instrument")
                            require(tr(image) == g.gaussian(
                                int(flag == hr_dot(a, b) and i == j)),
                                    "Open-bank normalized flag probability")
                            total = plus(total, image)
                            counts["open_flag_matrix_unit_maps"] += 1
                        require(tr(total) == g.gaussian(int(i == j)),
                                "Open-bank complete trace preservation")
        cases.append({"n": n, "r": bits, "M": size, "data_dimension": dimension,
                      "closed_helper_dimension": helper_dimension,
                      "open_clean_meter_qubits": bits,
                      "open_binary_readout_bits": 2 * bits,
                      "fault_words": size * size})
    return {"status": "passed", "arithmetic": "exact Gaussian rational; standard library",
            "cases": cases, **counts, "actual_queries_per_branch": 2,
            "scope": ("full cross-dual Pauli families n=1,2, all fault words and input "
                      "matrix units; ordered inverse banks and intermediate read/reset "
                      "priced; no helper minimum or native hardware certification")}


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
        "cross_dual": replay_cross_dual(),
        "scope": ("finite exact replay of the coarse measured flag and full target "
                  "instrument for fixed pure qutrit control; analytic lower bound, "
                  "arbitrary order-control input and native hardware not certified"),
    }


if __name__ == "__main__":
    if sys.flags.optimize:
        raise SystemExit("Run exact replays without Python optimization (-O).")
    print(json.dumps(verify(), sort_keys=True))
