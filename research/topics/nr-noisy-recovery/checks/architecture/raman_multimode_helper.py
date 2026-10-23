"""Exact four-level flying-helper Raman instrument at p=1/3, s=1/4.

The parameter-family proof and physical access limits are in NR-R11,
communication.md. This replay uses Q(sqrt(2), sqrt(3)) and no solver.
It checks an achievable instrument, not an ordinary optimum.
"""
from fractions import Fraction

if not __debug__:
    raise RuntimeError("Exact Raman helper checks require assertions; do not use -O.")


class _Radical:
    """Real field elements in the basis 1, sqrt(2), sqrt(3), sqrt(6)."""

    def __init__(self, *coefficients):
        assert len(coefficients) <= 4
        padded = coefficients + (0,) * (4 - len(coefficients))
        self.coefficients = tuple(Fraction(value) for value in padded)

    def __add__(self, other):
        if not isinstance(other, _Radical):
            other = _Radical(other)
        return _Radical(*(a + b for a, b in
                          zip(self.coefficients, other.coefficients)))

    __radd__ = __add__

    def __neg__(self):
        return _Radical(*(-value for value in self.coefficients))

    def __sub__(self, other):
        if not isinstance(other, _Radical):
            other = _Radical(other)
        return self + (-other)

    def __mul__(self, other):
        if not isinstance(other, _Radical):
            other = _Radical(other)
        result = [Fraction(0)] * 4
        # Basis indices are bit masks for the two independent radicals.
        # A repeated sqrt(2) or sqrt(3) contributes its rational square.
        for i, left in enumerate(self.coefficients):
            for j, right in enumerate(other.coefficients):
                factor = (2 if (i & j) & 1 else 1)
                factor *= (3 if (i & j) & 2 else 1)
                result[i ^ j] += left * right * factor
        return _Radical(*result)

    __rmul__ = __mul__

    def __eq__(self, other):
        if not isinstance(other, _Radical):
            other = _Radical(other)
        return self.coefficients == other.coefficients

    def __repr__(self):
        return repr(self.coefficients)


_ZERO = _Radical()
_ONE = _Radical(1)
_SQRT2 = _Radical(0, 1)
_SQRT3 = _Radical(0, 0, 1)
_SQRT6 = _Radical(0, 0, 0, 1)


def _zeros(size):
    return [_ZERO for _ in range(size)]


def _add_vectors(left, right):
    return [a + b for a, b in zip(left, right)]


def _scale_vector(scalar, vector):
    return [scalar * value for value in vector]


def _inner(left, right):
    # Every source, processor and readout in this witness is real.
    return sum((a * b for a, b in zip(left, right)), _ZERO)


def _basis(index):
    vector = _zeros(8)
    vector[index] = _ONE
    return vector


def _outer(left, right):
    return [[a * b for b in right] for a in left]


def _add_matrices(left, right):
    return [_add_vectors(a, b) for a, b in zip(left, right)]


def _matvec(matrix, vector):
    return [_inner(row, vector) for row in matrix]


def _gram_columns(matrix):
    return [[sum((matrix[row][i] * matrix[row][j]
                  for row in range(8)), _ZERO)
             for j in range(8)] for i in range(8)]


def _matrix_product(left, right):
    return [[sum((left[i][k] * right[k][j] for k in range(8)), _ZERO)
             for j in range(8)] for i in range(8)]


def _identity():
    return [[_ONE if i == j else _ZERO for j in range(8)]
            for i in range(8)]


def _subtract_matrices(left, right):
    return [[a - b for a, b in zip(row_left, row_right)]
            for row_left, row_right in zip(left, right)]


def _rational(value):
    assert value.coefficients[1:] == (0, 0, 0)
    return value.coefficients[0]


def verify_raman_multimode_helper():
    """Replay all retained and rejected effects of the four-readout witness."""
    half_sqrt2 = _SQRT2 * Fraction(1, 2)
    output_a = _scale_vector(half_sqrt2,
                             _add_vectors(_basis(0), _basis(5)))
    output_b = _add_vectors(
        _scale_vector(Fraction(1, 2), _basis(2)),
        _scale_vector(_SQRT3 * Fraction(1, 2), _basis(7)))
    source = _add_vectors(
        _scale_vector(_SQRT3 * Fraction(1, 3), _basis(0)),
        _scale_vector(_SQRT6 * Fraction(1, 3), _basis(5)))
    input_kept = _add_vectors(
        _scale_vector(_SQRT6 * Fraction(1, 3), _basis(0)),
        _scale_vector(-_SQRT3 * Fraction(1, 3), _basis(5)))

    processor = [[_ZERO for _ in range(8)] for _ in range(8)]
    columns = (
        (0, _scale_vector(_SQRT6 * Fraction(1, 3), output_b)),
        (5, _scale_vector(-_SQRT3 * Fraction(1, 3), output_b)),
        (1, output_a),
    )
    for column, vector in columns:
        for row, value in enumerate(vector):
            processor[row][column] = value

    assert _inner(source, source) == 1
    assert _inner(input_kept, input_kept) == 1
    assert _inner(source, input_kept) == 0
    kept_effect = _add_matrices(
        _outer(input_kept, input_kept), _outer(_basis(1), _basis(1)))
    assert _gram_columns(processor) == kept_effect
    assert _matrix_product(kept_effect, kept_effect) == kept_effect
    processor_reject = _subtract_matrices(_identity(), kept_effect)
    assert _gram_columns(processor_reject) == processor_reject
    assert _add_matrices(kept_effect, processor_reject) == _identity()
    assert _matvec(processor, source) == _zeros(8)
    assert _inner(_matvec(processor_reject, source),
                  _matvec(processor_reject, source)) == 1

    readout_00 = _add_vectors(
        _scale_vector(_SQRT3 * Fraction(1, 2), _basis(2)),
        _scale_vector(Fraction(-1, 2), _basis(7)))
    readout_01 = _basis(3)
    readout_10 = _scale_vector(
        half_sqrt2, _add_vectors(_basis(0), _scale_vector(-1, _basis(5))))
    readout_11 = _basis(1)
    readouts = []
    for left, right in ((readout_00, readout_11),
                        (readout_01, readout_10)):
        for sign in (1, -1):
            readouts.append(_scale_vector(
                half_sqrt2, _add_vectors(left, _scale_vector(sign, right))))
    for i, readout in enumerate(readouts):
        assert _inner(readout, output_a) == 0
        assert _inner(readout, output_b) == 0
        for j, other in enumerate(readouts):
            assert _inner(readout, other) == (i == j)
    readout_effect = [[_ZERO for _ in range(8)] for _ in range(8)]
    for readout in readouts:
        readout_effect = _add_matrices(readout_effect,
                                       _outer(readout, readout))
    readout_reject = _subtract_matrices(_identity(), readout_effect)
    assert _matrix_product(readout_effect, readout_effect) == readout_effect
    assert _gram_columns(readout_reject) == readout_reject

    # State order is (P,H) followed by A,B, with photon index 4*P+H.
    def apply_processor(state):
        result = _zeros(32)
        for spin in range(4):
            vector = _matvec(processor,
                             [state[photon * 4 + spin] for photon in range(8)])
            for photon, value in enumerate(vector):
                result[photon * 4 + spin] = value
        return result

    def swap_memory(state, site):
        result = _zeros(32)
        for photon in range(8):
            p, helper = divmod(photon, 4)
            for spin in range(4):
                a, b = divmod(spin, 2)
                bits = [p, a, b]
                bits[0], bits[site] = bits[site], bits[0]
                target = (4 * bits[0] + helper) * 4 + 2 * bits[1] + bits[2]
                result[target] = result[target] + state[photon * 4 + spin]
        return result

    def herald(readout, state):
        return [sum((readout[photon] * state[photon * 4 + spin]
                     for photon in range(8)), _ZERO) for spin in range(4)]

    initial = _zeros(32)
    for photon, value in enumerate(source):
        initial[photon * 4] = value
    after_first_swap = swap_memory(initial, 1)
    double_swap = swap_memory(apply_processor(after_first_swap), 2)
    polynomial_terms = (
        apply_processor(initial),
        apply_processor(after_first_swap),
        swap_memory(apply_processor(initial), 2),
        double_swap,
    )

    bell_probability = _ZERO
    spin_filter_reject_probability = _ZERO
    photon_kept_probability = _ZERO
    for index, readout in enumerate(readouts):
        for term in polynomial_terms[:3]:
            assert herald(readout, term) == _zeros(4)
        unfiltered = herald(readout, double_swap)
        photon_kept_probability += _inner(unfiltered, unfiltered)
        sign = 1 if index % 2 == 0 else -1
        if index < 2:
            # The even-spin filter has effect diag(1,1/8), and its
            # complementary effect diag(0,7/8) is positive.
            filter_amplitude = _SQRT2 * Fraction(1, 4)
            assert filter_amplitude * filter_amplitude == Fraction(1, 8)
            filtered = unfiltered[:2] + [value * filter_amplitude
                                         for value in unfiltered[2:]]
            failed_probability = Fraction(7, 8) * _inner(unfiltered[2:],
                                                         unfiltered[2:])
            expected = [_SQRT3 * Fraction(1, 12), _ZERO, _ZERO,
                        sign * _SQRT3 * Fraction(1, 12)]
        else:
            filtered = unfiltered
            failed_probability = _ZERO
            expected = [_ZERO, _SQRT3 * Fraction(1, 6),
                        sign * _SQRT3 * Fraction(1, 6), _ZERO]
        assert filtered == expected
        assert _inner(unfiltered, unfiltered) == (
            _inner(filtered, filtered) + failed_probability)
        bell_probability += _inner(filtered, filtered)
        spin_filter_reject_probability += failed_probability

    double_swap_probability = _inner(double_swap, double_swap)
    photon_reject_probability = _ZERO
    for spin in range(4):
        vector = _matvec(readout_reject,
                         [double_swap[photon * 4 + spin] for photon in range(8)])
        photon_reject_probability += _inner(vector, vector)
    assert photon_kept_probability + photon_reject_probability == double_swap_probability
    assert bell_probability == Fraction(5, 12)
    assert spin_filter_reject_probability == Fraction(7, 24)
    assert photon_reject_probability == Fraction(13, 72)
    assert double_swap_probability == Fraction(8, 9)
    processor_reject_probability = _ONE - double_swap_probability
    assert (processor_reject_probability + photon_reject_probability
            + spin_filter_reject_probability + bell_probability) == 1

    return {
        "photonic_modes": 8,
        "helper_levels": 4,
        "processor_kept_projector_rank": 2,
        "orthonormal_readouts": 4,
        "cancelled_polynomial_branches": 12,
        "filtered_bell_outputs": 4,
        "exact_bell_coefficient": str(_rational(bell_probability)),
        "processor_rejected_double_swap": str(_rational(processor_reject_probability)),
        "photon_readout_rejected_double_swap": str(_rational(photon_reject_probability)),
        "spin_filter_rejected_double_swap": str(_rational(spin_filter_reject_probability)),
        "scope": "Achievable p=1/3,s=1/4 instrument; optimized family and physical access remain analytic.",
    }


if __name__ == "__main__":
    import json
    print(json.dumps(verify_raman_multimode_helper(), indent=2))
