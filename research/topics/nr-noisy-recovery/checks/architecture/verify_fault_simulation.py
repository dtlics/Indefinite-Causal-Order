"""Finite exact replay for NR-R06's orthogonal-unitary fault simulation.

Only the Python standard library is used. Gaussian-rational matrices verify
complete process bases, Bell decoding of correlated labels, and equality of
the full normalized control-target Choi matrices. No report files are written.
The general trajectory and physical-access arguments remain analytic inputs.
"""

from fractions import Fraction as F
from itertools import product
import json


if not __debug__:
    raise RuntimeError("Exact fault-simulation checks require Python without -O.")


ZERO = (F(0), F(0))
ONE = (F(1), F(0))


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def gaussian(real=0, imag=0):
    return (F(real), F(imag))


def add(a, b):
    if a == ZERO:
        return b
    if b == ZERO:
        return a
    return (a[0] + b[0], a[1] + b[1])


def multiply(a, b):
    if a == ZERO or b == ZERO:
        return ZERO
    return (a[0] * b[0] - a[1] * b[1],
            a[0] * b[1] + a[1] * b[0])


def conjugate(a):
    return (a[0], -a[1])


def times(a, scalar):
    return (a[0] * scalar, a[1] * scalar)


def zeros(rows, cols):
    return [[ZERO for _ in range(cols)] for _ in range(rows)]


def identity(d):
    out = zeros(d, d)
    for i in range(d):
        out[i][i] = ONE
    return out


def adjoint(a):
    return [[conjugate(a[j][i]) for j in range(len(a))]
            for i in range(len(a[0]))]


def matmul(a, b):
    require(len(a[0]) == len(b), "Matrix dimensions disagree.")
    out = zeros(len(a), len(b[0]))
    for i, row in enumerate(a):
        for k, x in enumerate(row):
            if x == ZERO:
                continue
            for j, y in enumerate(b[k]):
                if y != ZERO:
                    out[i][j] = add(out[i][j], multiply(x, y))
    return out


def tensor(a, b):
    return [[multiply(a[i][j], b[k][ell])
             for j in range(len(a[0])) for ell in range(len(b[0]))]
            for i in range(len(a)) for k in range(len(b))]


def diagonal_blocks(a, b):
    d = len(a)
    require(len(b) == d, "Control branches have different dimensions.")
    out = zeros(2 * d, 2 * d)
    for i, j in product(range(d), repeat=2):
        out[i][j] = a[i][j]
        out[d + i][d + j] = b[i][j]
    return out


def vectorize(a):
    # Column-major vec: row index is output + input * output_dimension.
    return [a[i][j] for j in range(len(a[0])) for i in range(len(a))]


def inner(a, b):
    out = ZERO
    for x, y in zip(a, b):
        out = add(out, multiply(conjugate(x), y))
    return out


def add_outer(out, vector, weight):
    occupied = [(i, x) for i, x in enumerate(vector) if x != ZERO]
    for i, x in occupied:
        for j, y in occupied:
            out[i][j] = add(out[i][j], times(multiply(x, conjugate(y)), weight))


def pauli_basis(n):
    i = identity(2)
    x = [[ZERO, ONE], [ONE, ZERO]]
    y = [[ZERO, gaussian(0, -1)], [gaussian(0, 1), ZERO]]
    z = [[ONE, ZERO], [ZERO, gaussian(-1)]]
    out = []
    for word in product((i, x, y, z), repeat=n):
        matrix = [[ONE]]
        for factor in word:
            matrix = tensor(matrix, factor)
        out.append(matrix)
    return out


def rational_rotation(pauli, numerator, imaginary_numerator, denominator):
    # (a I - i b P)/c with a^2+b^2=c^2; no square roots are introduced.
    d = len(pauli)
    out = zeros(d, d)
    for i, j in product(range(d), repeat=2):
        out[i][j] = multiply(gaussian(0, F(-imaginary_numerator, denominator)),
                             pauli[i][j])
        if i == j:
            out[i][j] = add(out[i][j], gaussian(F(numerator, denominator)))
    require(matmul(adjoint(out), out) == identity(d), "Calibration is not unitary.")
    return out


def non_clifford_check(unitary, probe, paulis):
    image = vectorize(matmul(matmul(unitary, probe), adjoint(unitary)))
    d = len(unitary)
    coefficients = [times(inner(vectorize(p), image), F(1, d)) for p in paulis]
    require(all(c[1] == 0 for c in coefficients), "Hermitian Pauli coefficient is nonreal.")
    nonzero = [c[0] for c in coefficients if c != ZERO]
    require(len(nonzero) == 2 and sum(c * c for c in nonzero) == 1,
            "Chosen calibration did not give the intended non-Clifford witness.")
    return [str(c) for c in nonzero]


def process_basis(gates):
    d = len(gates[0])
    require(len(gates) == d * d, "Example is not a complete process basis.")
    require(all(matmul(adjoint(gate), gate) == identity(d) for gate in gates),
            "An orthogonal fault operation is not unitary.")
    vectors = [vectorize(gate) for gate in gates]
    gram = [[times(inner(a, b), F(1, d)) for b in vectors] for a in vectors]
    require(gram == identity(d * d), "Normalized process states are not orthogonal.")
    resolution = zeros(d * d, d * d)
    for vector in vectors:
        add_outer(resolution, vector, F(1, d))
    require(resolution == identity(d * d), "Process projectors do not resolve identity.")
    # Squared overlaps are the actual Bell/process-state measurement kernel.
    return [[z[0] * z[0] + z[1] * z[1] for z in row] for row in gram]


def correlated_law(labels, support, diagonal_only=False):
    p = [[F(0) for _ in range(labels)] for _ in range(labels)]
    if diagonal_only:
        for a, index in enumerate(support):
            p[index][index] = F(a + 1, 10)
    else:
        for a, index_a in enumerate(support):
            for b, index_b in enumerate(support):
                p[index_a][index_b] = F((a + 1) * (4 - b) + (a + 1) * (a == b), 110)
    require(sum(map(sum, p)) == 1, "Fault law is not normalized.")
    a, b = support[:2]
    minor = p[a][a] * p[b][b] - p[a][b] * p[b][a]
    require(minor != 0, "Fault law accidentally factorizes.")
    return p, minor


def decode_joint_labels(p, kernel_e, kernel_f):
    labels = len(p)
    occupied = [(a, b, p[a][b]) for a, b in product(range(labels), repeat=2) if p[a][b]]
    out = [[F(0) for _ in range(labels)] for _ in range(labels)]
    for a, b in product(range(labels), repeat=2):
        out[a][b] = sum(weight * kernel_e[a][i] * kernel_f[b][j]
                        for i, j, weight in occupied)
    require(out == p, "Bell measurement did not reproduce the correlated joint law.")
    return out


def direct_switch_choi(es, fs, p):
    d = len(es[0])
    out = zeros((2 * d) ** 2, (2 * d) ** 2)
    for a, b in product(range(len(es)), range(len(fs))):
        if p[a][b]:
            # Direct definition: the two coherent order blocks are FE and EF.
            w = diagonal_blocks(matmul(fs[b], es[a]), matmul(es[a], fs[b]))
            add_outer(out, vectorize(w), p[a][b] / (2 * d))
    return out


def ordinary_simulator_choi(es, fs, decoded):
    d = len(es[0])
    n = 2 * d
    out = zeros(n * n, n * n)
    for a, b in product(range(len(es)), range(len(fs))):
        if not decoded[a][b]:
            continue
        # Known feedforward is two controlled gates after decoding. Construct
        # it independently of the direct FE/EF block formula above.
        first = diagonal_blocks(es[a], fs[b])
        second = diagonal_blocks(fs[b], es[a])
        w = matmul(second, first)
        weight = decoded[a][b] / n
        # Evaluate every input matrix unit |i><j|; this includes arbitrary
        # control coherence and arbitrary reference-entangled input states.
        for i, j in product(range(n), repeat=2):
            for row in range(n):
                if w[row][i] == ZERO:
                    continue
                for col in range(n):
                    if w[col][j] != ZERO:
                        r, s = row + n * i, col + n * j
                        value = multiply(w[row][i], conjugate(w[col][j]))
                        out[r][s] = add(out[r][s], times(value, weight))
    return out


def check_choi(choi, d):
    n = 2 * d
    require(choi == adjoint(choi), "Full Choi matrix is not Hermitian.")
    marginal = [[ZERO for _ in range(n)] for _ in range(n)]
    for i, j in product(range(n), repeat=2):
        for output in range(n):
            marginal[i][j] = add(marginal[i][j], choi[output + n * i][output + n * j])
    expected = [[times(x, F(1, n)) for x in row] for row in identity(n)]
    require(marginal == expected, "Output partial trace is not I/(2d).")
    # Explicitly retain coherence between the two order blocks. A fixed |+>
    # slice, a scalar acceptance check, or a classical order mixture is not
    # the object checked here.
    order_zero = [row + n * col for row, col in product(range(d), repeat=2)]
    order_one = [d + row + n * (d + col) for row, col in product(range(d), repeat=2)]
    coherent_entries = sum(choi[i][j] != ZERO for i in order_zero for j in order_one)
    require(coherent_entries > 0, "Example failed to test cross-order Choi coherence.")
    return coherent_entries


def example(n, diagonal_only=False):
    d = 2 ** n
    paulis = pauli_basis(n)
    if n == 1:
        generator_u, generator_v, probe_u, probe_v = 1, 3, 3, 1
        support = [0, 1, 2, 3]
    else:
        # Genuine two-qubit calibrated entanglers and spatial Pauli faults.
        generator_u, generator_v, probe_u, probe_v = 5, 13, 12, 4  # XX, ZX, ZI, XI
        support = [0, 5, 11, 12]  # II, XX, YZ, ZI
    u = rational_rotation(paulis[generator_u], 3, 4, 5)
    v = rational_rotation(paulis[generator_v], 5, 12, 13)
    witnesses = [non_clifford_check(u, paulis[probe_u], paulis),
                 non_clifford_check(v, paulis[probe_v], paulis)]
    es = [matmul(p, u) for p in paulis]
    fs = [matmul(p, v) for p in paulis]
    kernel_e, kernel_f = process_basis(es), process_basis(fs)
    p, minor = correlated_law(len(paulis), support, diagonal_only)
    decoded = decode_joint_labels(p, kernel_e, kernel_f)
    direct = direct_switch_choi(es, fs, p)
    ordinary = ordinary_simulator_choi(es, fs, decoded)
    require(direct == ordinary, "Full switched-output and ordinary Choi matrices differ.")
    coherence = check_choi(direct, d)
    return {
        "data_dimension": d,
        "control_target_input_dimension": 2 * d,
        "complete_process_basis_size_per_module": d * d,
        "process_gram_entries_checked": 2 * d ** 4,
        "correlated_label_law": "weighted equal labels" if diagonal_only else "asymmetric nonproduct rational law",
        "nonproduct_minor": str(minor),
        "nonzero_joint_label_pairs": sum(weight != 0 for row in p for weight in row),
        "calibration_non_clifford_pauli_coefficients": witnesses,
        "full_choi_shape": [(2 * d) ** 2, (2 * d) ** 2],
        "full_choi_entries_compared": (2 * d) ** 4,
        "input_matrix_units_checked": (2 * d) ** 2,
        "nonzero_cross_order_choi_entries": coherence,
        "normalized_choi_output_partial_trace": "I/(2d)",
        "exact_full_choi_residual": "0",
    }


def main():
    examples = [example(1), example(1, diagonal_only=True), example(2)]
    print(json.dumps({
        "status": "passed",
        "result": "NR-R06",
        "arithmetic": "Python standard-library Gaussian rationals; no floating point",
        "examples": examples,
        "scope": ("Finite exact d=2,4 algebra replay of known orthogonal-unitary process bases, "
                  "correlated Bell-label decoding, and the full coherent switched-output ordinary simulation. "
                  "Persistent-trajectory induction, matched physical fault laws, noiseless memory, allowed "
                  "known-control synthesis and hardware costs remain assumptions/analytic proof inputs. "
                  "No general quantum-memory or input-dependent-noise simulation is asserted."),
    }, indent=2))


if __name__ == "__main__":
    main()
