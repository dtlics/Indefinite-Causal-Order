"""Exact finite replay of the ordinary qutrit double-fault controller.

The analytic closed-controller lower bound and physical resource assumptions
belong to the linked NR-R06 method. This checks finite matrix identities and
complete weighted instruments, not an all-strategy lower bound or native
hardware implementation. Standard library only; no files are written.
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
    return tuple(tuple(sum(x * y for x, y in zip(row, column))
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
        "scope": ("finite exact replay of the coarse measured flag and full target "
                  "instrument for fixed pure qutrit control; analytic lower bound, "
                  "arbitrary order-control input and native hardware not certified"),
    }


if __name__ == "__main__":
    if sys.flags.optimize:
        raise SystemExit("Run exact replays without Python optimization (-O).")
    print(json.dumps(verify(), sort_keys=True))
