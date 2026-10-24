"""Exact finite ingredients for the hard-one-encounter four-mode chain bound.

Reuse the standard-library Gaussian-rational matrix engine. This checks
Fourier ranks/minors, finite words/slices, nucleus identities and a physical
weighted-metric fixture. General all-n slicing, interpolation, prefix-frame,
instrument/continuous-record and determinant-potential arguments remain
analytic in the method. No optimizer, tolerance or hardware claim.
Import is quiet; no files are written; all guards remain active under -O.
"""
from fractions import Fraction as F
from itertools import combinations, permutations, product
import json

from retained_photon_serial import (
    G, add, adj, blockdiag, blockrows, cp_equal, eye, kron, mm,
    rank, require, scale, zeros,
)


def determinant(a):
    require(len(a) == len(a[0]), "square determinant")
    work = [list(row) for row in a]
    value = G(1)
    for col in range(len(work)):
        pivot = next((row for row in range(col, len(work)) if work[row][col] != 0), None)
        if pivot is None:
            return G()
        if pivot != col:
            work[col], work[pivot] = work[pivot], work[col]
            value = -value
        entry = work[col][col]
        value = value*entry
        work[col] = [x/entry for x in work[col]]
        for row in range(col+1, len(work)):
            factor = work[row][col]
            if factor != 0:
                work[row] = [x-factor*y for x, y in zip(work[row], work[col])]
    return value


def trace(a):
    return sum((a[i][i] for i in range(len(a))), G())


def hs2(a):
    value = trace(mm(adj(a), a))
    require(value.i == 0, "real squared Hilbert-Schmidt norm")
    return value.r


def positive_definite(a):
    if a != adj(a):
        return False
    for n in range(1, len(a)+1):
        value = determinant([row[:n] for row in a[:n]])
        if value.i != 0 or value.r <= 0:
            return False
    return True


def partial_tau(a):
    return [[a[i][j]+a[i+2][j+2] for j in range(2)] for i in range(2)]


def paulis():
    return (eye(2), [[G(), G(1)], [G(1), G()]],
            [[G(), G(0, -1)], [G(0, 1), G()]],
            [[G(1), G()], [G(), G(-1)]])


def pair_coefficients():
    ident, x, _, z = paulis()
    return [ident, scale(z, G(0, -1)), scale(x, G(0, -1)), zeros(2)]


def coefficient(n, bits):
    require(0 <= bits < 1 << (2*n), "Fourier coefficient index")
    terms = pair_coefficients()
    result = eye(2)
    for pair in range(n):
        a, b = (bits >> (2*pair)) & 1, (bits >> (2*pair+1)) & 1
        result = mm(terms[a+2*b], result)
    return result


def packed(bits, positions):
    return sum(((bits >> bit) & 1) << i for i, bit in enumerate(positions))


def flatten(n, past):
    past = tuple(sorted(past))
    future = tuple(bit for bit in range(2*n) if bit not in past)
    out = zeros(1 << (len(future)+1), 1 << (len(past)+1))
    for bits in range(1 << (2*n)):
        entry = coefficient(n, bits)
        for fout, fin in product(range(2), repeat=2):
            out[2*packed(bits, future)+fout][2*packed(bits, past)+fin] = entry[fout][fin]
    return out


def chronological_word(word, n):
    return all(set(word[2*i:2*i+2]) == {2*i, 2*i+1} for i in range(n))


def boundary_rank_guards():
    expected = {(0, 1): 2, (0, 2): 8, (0, 3): 8,
                (1, 2): 8, (1, 3): 8, (2, 3): 6}
    ranks, mixed = {}, 0
    for past, expected_rank in expected.items():
        matrix = flatten(2, past)
        require(rank(matrix) == expected_rank, "two-pair Fourier cut rank")
        ranks["".join(str(i) for i in past)] = expected_rank
        if expected_rank == 8:
            require(determinant(matrix) == 1, "mixed full determinant +1")
            mixed += 1
        if expected_rank == 6:
            require(all(value == 0 for row in matrix[6:] for value in row), "reversed zero terminal rows")
            require(all(row[j] == 0 for row in matrix for j in (6, 7)), "reversed zero terminal columns")
            require(determinant([row[:6] for row in matrix[:6]]) == 16, "reversed leading minor determinant 16")
    for size in (1, 3):
        for past in combinations(range(4), size):
            require(rank(flatten(2, past)) == 4, "one/three-leaf Fourier cut rank4")

    slices = 0
    for n in range(2, 6):
        for first, second in combinations(range(n), 2):
            for small in range(16):
                large = ((small & 3) << (2*first)) | (((small >> 2) & 3) << (2*second))
                require(coefficient(n, large) == coefficient(2, small), "Fourier-00 two-pair slice")
                slices += 1

    subset_ranks = {}
    for size in range(1, 6):
        for past in combinations(range(6), size):
            subset_ranks[frozenset(past)] = rank(flatten(3, past))
    survivors = []
    words = 0
    for word in permutations(range(6)):
        passes = all(subset_ranks[frozenset(word[:k])] <= 4 for k in range(1, 6))
        require(passes == chronological_word(word, 3), "all six-leaf query words")
        if passes:
            survivors.append(word)
        words += 1
    require(len(survivors) == 8, "exactly eight chronological three-pair words")

    boundaries = 0
    for n in range(2, 5):
        for k in range(1, 2*n):
            require(rank(flatten(n, range(k))) == (4 if k % 2 else 2), "chronological rank profile")
            boundaries += 1
    return {"two_pair_cut_ranks": ranks, "mixed_full_determinants": mixed,
            "reversed_leading_minor_determinant": 16, "one_three_leaf_cuts": 8,
            "fourier_zero_slice_coefficients_n2_through_n5": slices,
            "three_pair_words": words, "three_pair_surviving_words": len(survivors),
            "chronological_boundary_cases_n2_through_n4": boundaries,
            "scope": "exact finite tensors/minors; general-n word and combined-boundary-rank theorems are analytic"}


def nucleus_and_phase_guards():
    ident, x, y, z = paulis()
    nucleus = blockrows(ident, scale(z, G(0, -1)))+blockrows(scale(x, G(0, -1)), zeros(2))
    inverse = blockrows(zeros(2), scale(x, G(0, 1)))+blockrows(scale(z, G(0, 1)), scale(y, G(0, 1)))
    require(mm(nucleus, inverse) == eye(4) and mm(inverse, nucleus) == eye(4), "nucleus inverse")
    for moment in (mm(nucleus, adj(nucleus)), mm(adj(nucleus), nucleus)):
        require(add(add(mm(moment, moment), scale(moment, -3)), eye(4)) == zeros(4), "nucleus quadratic")
        root_numerator = add(moment, eye(4))
        require(mm(root_numerator, root_numerator) == scale(moment, 5), "positive square-root numerator identity")
        require(positive_definite(root_numerator), "positive square-root numerator")
        require(partial_tau(root_numerator) == scale(ident, 5), "balanced square-root partial trace numerator")
    require(hs2(nucleus) == 6, "nucleus squared HS norm")

    jmatrix = [[G(), G(-2)], [G(1), G()]]
    # The first two cases certify the coefficient identity for all complex
    # a,b by linearity; the latter cases separately exercise complex signs.
    cases = [(G(1), G()), (G(), G(1)),
             (G(F(2, 5)), G(0, F(3, 7))),
             (G(F(1, 3), F(1, 4)), G(F(-2, 7), F(3, 8)))]
    for a, b in cases:
        lhs = mm(mm(nucleus, kron(add(scale(ident, a), scale(x, b)), ident)), inverse)
        rhs = add(scale(eye(4), a), add(scale(kron(ident, z), G(0, 1)*b),
                                      scale(kron(jmatrix, y), -G(0, 1)*b)))
        require(lhs == rhs, "all-coefficient phase-ratio identity")
    require(trace(mm(x, jmatrix)) == -1, "phase-obstruction trace")
    return nucleus, {"nucleus_quadratics": 2, "positive_sqrt_numerator_identities": 2,
                     "balanced_partial_trace_numerators": 2,
                     "phase_coefficient_basis_cases": 2, "additional_complex_phase_cases": 2,
                     "scope": "exact nucleus and phase ingredients; three-lines, differentiation and global determinant-normalized norm inequality remain analytic"}


def big_diagonal(blocks):
    out = zeros(2*len(blocks))
    for k, block in enumerate(blocks):
        for i, j in product(range(2), repeat=2):
            out[2*k+i][2*k+j] = block[i][j]
    return out


def matrix_unit(n, i, j):
    out = zeros(n)
    out[i][j] = G(1)
    return out


def weighted_pair_guard(nucleus):
    ident, x, _, z = paulis()
    hin = [[G(1), G(0, F(1, 3))], [G(), G(1)]]
    hini = [[G(1), G(0, F(-1, 3))], [G(), G(1)]]
    require(mm(hin, hini) == ident and determinant(hin) == 1, "anisotropic complex input metric")
    h1 = [[G(F(3, 5)), G()], [G(), G(F(4, 5))]]
    calibrated = add(scale(ident, F(3, 5)), scale(x, G(0, F(4, 5))))
    require(mm(adj(calibrated), calibrated) == ident and determinant(calibrated) == 1, "complex output unitary")
    h2 = mm(calibrated, [[G(F(4, 5)), G()], [G(), G(F(3, 5))]])
    outputs = (h1, h2)
    metric_sum = add(mm(adj(h1), h1), mm(adj(h2), h2))
    require(metric_sum == ident, "output metric sum S=I")
    determinants = [determinant(h) for h in outputs]
    require(all(value == F(12, 25) for value in determinants), "positive child determinants")
    determinant_sum = sum((value.r for value in determinants), F(0))
    require(determinant_sum == F(24, 25) and determinant_sum < 1, "strict Minkowski determinant sum")

    # S=I permits determinant domination, but does not make the flagged
    # filter instrument equal to the identity channel of its replacement.
    channel_difference = False
    for i, j in product(range(2), repeat=2):
        unit = matrix_unit(2, i, j)
        actual = add(mm(mm(h1, unit), adj(h1)), mm(mm(h2, unit), adj(h2)))
        channel_difference = channel_difference or actual != unit
    require(channel_difference, "single-row replacement is not the original CP instrument")

    e0, e1 = scale(ident, F(3, 5)), scale(ident, F(4, 5))
    source = e0+e1
    left = blockdiag(e0, e1)
    left_inverse = blockdiag(scale(ident, F(5, 3)), scale(ident, F(5, 4)))
    base_row = blockrows(e0, e1)
    require(mm(adj(source), source) == ident and mm(base_row, adj(base_row)) == ident,
            "source isometry and output coisometry")
    preparation = [mm(source, h) for h in outputs]
    require(add(mm(adj(preparation[0]), preparation[0]), mm(adj(preparation[1]), preparation[1])) == ident,
            "complete subnormalized source-preparation budget")
    require(sum((hs2(blockdiag([row[:] for row in s[:2]], [row[:] for row in s[2:]])) for s in preparation), F(0)) == 2,
            "summed source sector HS budget two")
    k = F(1, 100)
    total_fourier = scale(mm(nucleus, kron(ident, hini)), k)
    middle = mm(mm(left_inverse, total_fourier), left_inverse)
    require(hs2(middle) < 1 and positive_definite(add(eye(4), scale(mm(adj(middle), middle), -1))),
            "physical middle contraction and positive completion")
    scaled_hin, scaled_hini = scale(hin, 2), scale(hini, F(1, 2))
    require(mm(scaled_hin, scaled_hini) == ident and determinant(scaled_hin) == 4,
            "non-unit-determinant input metric")
    scaled_fourier = scale(mm(nucleus, kron(ident, scaled_hini)), k)
    scaled_middle = mm(mm(left_inverse, scaled_fourier), left_inverse)
    require(scaled_fourier == scale(total_fourier, F(1, 2)) and
            hs2(scaled_middle) == hs2(middle)/4, "input determinant and physical norm scaling")
    rows = [mm(h, base_row) for h in outputs]
    row_effect = add(mm(adj(rows[0]), rows[0]), mm(adj(rows[1]), rows[1]))
    require(row_effect == mm(adj(base_row), base_row) and mm(row_effect, row_effect) == row_effect,
            "complete terminal row budget with projector residual")
    require(mm(mm(left, middle), left) == total_fourier, "single-row physical factorization")

    sectors, units, normalized_grams = 0, 0, []
    for h, row in zip(outputs, rows):
        row_sectors = blockdiag([r[:2] for r in row], [r[2:] for r in row])
        require(mm(mm(row_sectors, middle), left) == mm(kron(ident, h), total_fourier),
                "weighted Fourier physical factorization")
        actual, expected = [], []
        gram_reference = None
        for a, b in product((1, -1), repeat=2):
            da, db = blockdiag(ident, scale(ident, a)), blockdiag(ident, scale(ident, b))
            physical = mm(mm(mm(mm(row, db), middle), da), source)
            numerator = add(ident, add(scale(z, G(0, -a)), scale(x, G(0, -b))))
            require(mm(adj(numerator), numerator) == scale(ident, 3), "normalized G numerator effect three")
            target = scale(mm(mm(h, numerator), hini), k)
            require(physical == target, "weighted full-input spin-sector map")
            logical_output = mm(physical, hin)
            scaled_physical = mm(mm(mm(mm(row, db), scaled_middle), da), source)
            require(mm(scaled_physical, scaled_hin) == logical_output,
                    "weighted map with non-unit input determinant")
            actual.append(logical_output)
            expected.append(scale(mm(h, numerator), k))
            # G=N/sqrt(3). Thus K Hin N^dagger /sqrt(3) is H_out,
            # allowing its Gram to be computed without adjoining sqrt(3).
            numerator_output_metric = mm(logical_output, adj(numerator))
            output_gram = scale(mm(adj(numerator_output_metric), numerator_output_metric), F(1, 3))
            require(output_gram == scale(mm(adj(h), h), 3*k*k), "normalized output metric Gram includes factor three")
            require(positive_definite(output_gram), "normalized output metric invertible")
            if gram_reference is None:
                gram_reference = output_gram
            require(output_gram == gram_reference, "output metric is independent of new spin labels")
            sectors += 1
        normalized_grams.append(gram_reference)
        units += cp_equal(big_diagonal(actual), big_diagonal(expected))
    normalized_weights = [3*k*k*F(12, 25) for _ in outputs]
    for gram, weight in zip(normalized_grams, normalized_weights):
        require(determinant(gram) == weight*weight and weight > 0, "positive normalized metric determinant weight")
    potential = sum(normalized_weights, F(0))
    require(potential == F(9, 31250), "exact normalized determinant potential")
    require(potential < 3*k*k and 3*k*k-potential == F(3, 250000), "normalized strict Minkowski gap")
    require(potential <= F(3, 5), "finite weighted-stage contraction check")
    require(20*k*k <= 2*hs2(mm(middle, left)), "finite 20/3 determinant/norm normalization check")
    require(potential/determinant(scaled_hin).r == F(9, 125000) and
            20*k*k/determinant(scaled_hin).r <= 2*hs2(mm(scaled_middle, left)),
            "input determinant denominator normalization")
    return {"weighted_sector_maps": sectors, "full_ABF_matrix_units": units,
            "minkowski_sum": "24/25", "compression_determinant": 1,
            "replacement_preserves_original_CP_instrument": False,
            "subnormalized_source_histories": len(preparation),
            "rescaled_input_metric_determinant": 4,
            "rescaled_input_metric_sector_maps": sectors,
            "middle_squared_HS_norm": str(hs2(middle)),
            "normalized_output_potential": str(potential),
            "normalized_minkowski_gap": str(3*k*k-potential),
            "scope": "one physical rational anisotropic metric fixture and exact normalization/budgets; no general instrument or probability theorem is established by this finite replay"}


def mean_budget_guards():
    for n in range(1, 17):
        native, hard = F(3, 4)**n, F(3, 5)**n
        require(native > hard, "finite native/hard-class probability comparison")
        require(F(1, 2)*(4*n) == 2*n, "four-contact coin mean budget")
        require((F(1, 2) > native) == (n >= 3), "four-contact coin native threshold")
        require(F(2, 3)*(3*n) == 2*n, "conditional coherent-return coin mean budget")
        require((F(2, 3) > native) == (n >= 2), "conditional coherent-return native threshold")
    require(F(3, 4)**2 > F(1, 2) > F(3, 4)**3 and 0 < F(3, 4) < 1,
            "exact four-contact threshold and monotonicity ingredients")
    require(F(3, 4) > F(2, 3) > F(3, 4)**2, "conditional return threshold ingredients")
    return {"finite_n_cases": 16, "four_contact_coin_probability": "1/2",
            "four_contact_coin_native_threshold_n": 3,
            "conditional_eight_mode_return_coin_probability": "2/3",
            "conditional_eight_mode_return_native_threshold_n": 2,
            "scope": "exact mean-2n ledger guards; hard one-encounter bounds do not imply expected-query or hardware-rate advantages; the eight-mode point additionally assumes its priced lossless controlled-vacuum return interface"}


def verify():
    nucleus, local = nucleus_and_phase_guards()
    return {"status": "passed", "arithmetic": "Q(i), Fraction, standard library",
            "boundary_rank": boundary_rank_guards(), "nucleus_and_phase": local,
            "weighted_pair": weighted_pair_guard(nucleus), "mean_budget": mean_budget_guards(),
            "scope": "finite exact rank/minor/Fourier-slice/word and weighted-metric ingredients for the exact hard-one-CZ-per-spin four-mode chain. General all-n slicing, three-lines, determinant-normalized norm, actual-prefix/frame, complete-instrument and continuous-record arguments remain analytic. No approximate-gate robustness, terminal spin-filter theorem, enlarged controlled-vacuum call simulation, expected-query separation or hardware advantage."}


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True))
