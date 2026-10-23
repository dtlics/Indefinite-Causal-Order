"""Exact finite full-Choi replay for NR-R12's binary dispatcher.

Only standard-library Gaussian-rational arithmetic is used. Noncommuting
rational unitary examples have target dimensions 2 and 3. The replay includes
the classical flag and every counter/data input matrix unit, rather than only
success probabilities or basis-state inputs. The universal query lower bound
and the physical coherent-use model remain analytic dependencies. No output
files are written.
"""

from fractions import Fraction as F
from itertools import product
import json

from verify_fault_simulation import (
    ZERO, ONE, require, gaussian, add, multiply, conjugate, times,
    zeros, identity, adjoint, matmul, tensor, diagonal_blocks,
    vectorize, inner, add_outer,
)


if not __debug__:
    raise RuntimeError("Exact dispatch checks require Python without -O.")


def scaled(a, value):
    return [[times(x, value) for x in row] for row in a]


def plus(a, b):
    return [[add(x, y) for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]


def trace(a):
    out = ZERO
    for i in range(len(a)):
        out = add(out, a[i][i])
    return out


def require_unitary(a):
    require(matmul(adjoint(a), a) == identity(len(a)), "Example is not exactly unitary.")


def phase_diagonal(d, position, real, imag):
    out = identity(d)
    out[position][position] = gaussian(real, imag)
    require_unitary(out)
    return out


def givens(d, left, right, cosine, sine, imaginary=False):
    """A rational real or complex two-plane rotation; no square roots."""
    out = identity(d)
    out[left][left] = out[right][right] = gaussian(cosine)
    if imaginary:
        out[left][right] = out[right][left] = gaussian(0, -sine)
    else:
        out[left][right] = gaussian(-sine)
        out[right][left] = gaussian(sine)
    require_unitary(out)
    return out


def pairs(d):
    first = givens(d, 0, 1, F(3, 5), F(4, 5))
    if d == 2:
        second = phase_diagonal(d, 0, F(5, 13), F(12, 13))
        yield first, second
        yield (givens(d, 0, 1, F(5, 13), F(12, 13), True),
               givens(d, 0, 1, F(8, 17), F(15, 17)))
    else:
        first = matmul(first, phase_diagonal(d, 2, F(5, 13), F(12, 13)))
        second = matmul(givens(d, 1, 2, F(5, 13), F(12, 13), True),
                        phase_diagonal(d, 0, F(3, 5), F(-4, 5)))
        yield first, second
        yield (matmul(givens(d, 0, 2, F(8, 17), F(15, 17), True), first),
               matmul(givens(d, 0, 1, F(7, 25), F(24, 25)), second))


def multiplexor(v0, v1):
    d = len(v0)
    out = zeros(2*d, 2*d)
    for r, c in product(range(d), repeat=2):
        out[d+r][c] = v0[r][c]
        out[r][d+c] = v1[r][c]
    return out


def normalized_choi(kraus, input_dimension=None):
    """(probability, rectangular Kraus matrix); normalization is by input d."""
    if input_dimension is None:
        input_dimension = len(kraus[0][1][0])
    output_dimension = len(kraus[0][1])
    out = zeros(input_dimension*output_dimension, input_dimension*output_dimension)
    for weight, k in kraus:
        require(len(k) == output_dimension and len(k[0]) == input_dimension,
                "Kraus dimensions disagree.")
        if weight:
            add_outer(out, vectorize(k), weight/input_dimension)
    return out


def require_tp_choi(j, input_dimension, output_dimension):
    require(j == adjoint(j), "Normalized Choi matrix is not Hermitian.")
    marginal = zeros(input_dimension, input_dimension)
    for r, c in product(range(input_dimension), repeat=2):
        for output in range(output_dimension):
            marginal[r][c] = add(marginal[r][c],
                j[output+output_dimension*r][output+output_dimension*c])
    require(marginal == scaled(identity(input_dimension), F(1, input_dimension)),
            "Choi output marginal is not normalized identity.")


def flag_embed(k, flag):
    d = len(k)
    out = zeros(2*d, len(k[0]))
    for r in range(d):
        out[flag*d+r] = list(k[r])
    return out


def corrected_switch_kraus(u, z, p, kappa):
    """Direct two-slot switch, external +/- mixture, X readout, Z feedback."""
    choices = [u, matmul(z, u)]
    error_weights = [1-p, p]
    control_weights = [(1+kappa)/2, (1-kappa)/2]
    flagged, discarded_flag, groups = [], [], [[], []]
    for initial_sign, error_a, error_b, flag in product(range(2), repeat=4):
        weight = control_weights[initial_sign]*error_weights[error_a]*error_weights[error_b]
        if not weight:
            continue
        # The two products belong to distinct named slots, even though their
        # reduced channels coincide. This is the supplied switch interface.
        forward = matmul(choices[error_b], choices[error_a])
        reverse = matmul(choices[error_a], choices[error_b])
        sign = -1 if (initial_sign+flag) % 2 else 1
        k = scaled(plus(forward, scaled(reverse, sign)), F(1, 2))
        if flag:
            k = matmul(z, k)
        groups[flag].append((weight, k))
        discarded_flag.append((weight, k))
        flagged.append((weight, flag_embed(k, flag)))
    return flagged, discarded_flag, groups


def classical_index_check(u, z, v0, v1):
    d = len(v0)
    direct = normalized_choi([(F(1, 2), u), (F(1, 2), matmul(z, u))])
    l0, l1 = zeros(2*d, 2*d), zeros(2*d, 2*d)
    for r, c in product(range(d), repeat=2):
        l0[d+r][c] = v0[r][c]
        l1[r][d+c] = v1[r][c]
    measured = normalized_choi([(F(1), l0), (F(1), l1)])
    require(direct == measured, "Complete-dephasing classical-index instrument failed.")
    require_tp_choi(direct, 2*d, 2*d)


def ordinary_routing_checks(v0, v1, w):
    d = len(v0)
    i = identity(d)
    # Three sequential calls, one dummy. Ordering: counter, data, dummy.
    first = diagonal_blocks(tensor(v0, i), tensor(i, v0))
    second = diagonal_blocks(tensor(v1, i), tensor(v1, i))
    third = diagonal_blocks(tensor(i, v0), tensor(v0, i))
    actual = matmul(matmul(third, second), first)
    require(actual == tensor(w, v0), "Three-call common-dummy factorization failed.")
    # Four calls in two rounds, two DISTINCT dummies. Each branch has two
    # disjoint parallel subroutine actions per round.
    stage_one = diagonal_blocks(
        tensor(tensor(v0, i), v1), tensor(tensor(v1, v0), i))
    stage_two = diagonal_blocks(
        tensor(tensor(v1, v0), i), tensor(tensor(v0, i), v1))
    actual = matmul(stage_two, stage_one)
    require(actual == tensor(tensor(w, v0), v1),
            "Four-call two-round/two-dummy factorization failed.")


def temporal_phase_checks(u, z, w):
    """Two-window classical fields, with an occupied/vacuum path interface.

    Each phase is the square of a rational point on the unit circle so the
    half-sum residual also has Gaussian-rational entries. The check compares
    the retained quantum channel after prescribed feedback and flag disposal,
    rather than claiming equality of the two flagged instruments.
    """
    d = len(u)//2
    a = gaussian(F(3, 5), F(4, 5))
    b = gaussian(F(5, 13), F(12, 13))
    c = gaussian(F(8, 17), F(-15, 17))
    phases = [
        (ONE, ONE, a, a), (a, a, b, b),
        (ONE, a, ONE, b), (a, b, c, ONE),
        (a, c, b, a), (b, a, c, b),
        (c, b, a, ONE), (b, c, a, b),
    ]

    def phase_gate(value):
        return diagonal_blocks(
            [[multiply(x, value) for x in row] for row in identity(d)],
            [[multiply(x, conjugate(value)) for x in row] for row in identity(d)])

    def readout(first, second, kappa):
        unflagged, flagged = [], []
        for initial_sign, flag in product(range(2), repeat=2):
            weight = (1+kappa)/2 if initial_sign == 0 else (1-kappa)/2
            sign = -1 if (initial_sign+flag) % 2 else 1
            k = scaled(plus(first, scaled(second, sign)), F(1, 2))
            if flag:
                k = matmul(z, k)
            unflagged.append((weight, k))
            flagged.append((weight, flag_embed(k, flag)))
        return normalized_choi(unflagged), normalized_choi(flagged)

    cases = distinct_instruments = 0
    for qa1, qa2, qb1, qb2 in phases:
        modules = [matmul(phase_gate(multiply(q, q)), u)
                   for q in (qa1, qa2, qb1, qb2)]
        a1, a2, b1, b2 = modules
        switched = (matmul(b2, a1), matmul(a2, b1))
        same_order = (matmul(a2, a1), matmul(b2, b1))
        residual = multiply(multiply(qa2, conjugate(qa1)),
                            multiply(qb2, conjugate(qb1)))
        target = matmul(phase_gate(residual), w)
        for kappa in (F(0), F(97, 100), F(1)):
            actual, switch_flag = readout(*switched, kappa)
            ordinary, ordinary_flag = readout(*same_order, kappa)
            expected = normalized_choi([
                ((1+kappa)/2, target),
                ((1-kappa)/2, matmul(z, target)),
            ])
            require(actual == expected == ordinary,
                    "Temporal phase switch and ordinary path filter differ.")
            require_tp_choi(actual, 2*d, 2*d)
            distinct_instruments += switch_flag != ordinary_flag
            cases += 1
    require(distinct_instruments > 0,
            "Examples must distinguish discarded-flag from full-instrument equality.")
    return cases


def event_head_checks(u, z, w):
    """Explicit occupied-window visit addressing; private coins are retained.

    A head's intermediate 0/1 coherence is dephased by a random Z. The
    final common head state is checked before reducing to payload Kraus
    matrices. Rewinding a head and allocating coins by clock time are
    separately tested alternatives, not alternative descriptions of one port.
    """
    cases = clock_cases = reuse_cases = 0
    for p in (F(1, 10), F(1, 2), F(9, 10)):
        probabilities = (1-p, p)
        choices = (u, matmul(z, u))
        for la, lb in ((F(1), F(1)), (F(49, 50), F(97, 100)), (F(0), F(1))):
            actual = []
            for sa, sb, ea, eb in product(range(2), repeat=4):
                weight = probabilities[sa]*probabilities[sb]
                weight *= ((1+la)/2 if ea == 0 else (1-la)/2)
                weight *= ((1+lb)/2 if eb == 0 else (1-lb)/2)
                products = []
                for branch in (0, 1):
                    heads = [0, 0]
                    coins = [sa, sb]
                    output = identity(len(u))
                    for window, station in enumerate((branch, 1-branch)):
                        require(heads[station] == 0, "Switch revisited a station.")
                        output = matmul(choices[coins[station]], output)
                        heads[station] += 1
                        if window == 0:
                            output = scaled(output, (-1)**(ea*heads[0]+eb*heads[1]))
                    require(heads == [1, 1], "Final event heads retain arrival order.")
                    products.append(output)
                for flag in (0, 1):
                    k = scaled(plus(products[0], scaled(products[1], (-1)**flag)), F(1, 2))
                    if flag:
                        k = matmul(z, k)
                    actual.append((weight, flag_embed(k, flag)))
            expected, _, _ = corrected_switch_kraus(u, z, p, la*lb)
            require(normalized_choi(actual) == normalized_choi(expected),
                    "Visit-head dilation differs from the effective-visibility instrument.")
            cases += 1

        # A different port assigns independent fault coins to all four CLOCK
        # windows. Its prescribed decoder leaves the ordinary two-call noise.
        clock = []
        for a1, a2, b1, b2 in product(range(2), repeat=4):
            weight = probabilities[a1]*probabilities[a2]*probabilities[b1]*probabilities[b2]
            forward = matmul(choices[b2], choices[a1])
            reverse = matmul(choices[a2], choices[b1])
            for flag in (0, 1):
                k = scaled(plus(forward, scaled(reverse, (-1)**flag)), F(1, 2))
                if flag:
                    k = matmul(z, k)
                clock.append((weight, k))
        alpha, beta = (1-p)**2+p*p, 2*p*(1-p)
        require(normalized_choi(clock) == normalized_choi([(alpha, w), (beta, matmul(z, w))]),
                "Fresh clock-time coins spuriously realize perfect self-switch correction.")
        clock_cases += 1

        for rewind in (False, True):
            repeated = []
            for first, second in product(range(2), repeat=2):
                coins, head = (first, second), 0
                output = identity(len(u))
                for visit in (0, 1):
                    if visit and rewind:
                        head = 0
                    output = matmul(choices[coins[head]], output)
                    head += 1
                repeated.append((probabilities[first]*probabilities[second], output))
            expected = [(F(1), w)] if rewind else [(alpha, w), (beta, matmul(z, w))]
            require(normalized_choi(repeated) == normalized_choi(expected),
                    "Fresh-repeat/retained-tape-rewind distinction failed.")
            reuse_cases += 1
    return cases, clock_cases, reuse_cases


def replay_pair(v0, v1):
    d = len(v0)
    require(len(v1) == d, "Subroutine dimensions disagree.")
    require_unitary(v0)
    require_unitary(v1)
    require(matmul(v0, v1) != matmul(v1, v0), "Example subroutines commute.")
    u = multiplexor(v0, v1)
    z = diagonal_blocks(identity(d), scaled(identity(d), -1))
    w = diagonal_blocks(matmul(v1, v0), matmul(v0, v1))
    require_unitary(u)
    require_unitary(w)
    require(matmul(z, u) == scaled(matmul(u, z), -1), "Z and U fail to anticommute.")
    require(matmul(u, u) == w, "Multiplexor square does not contain the two orders.")
    classical_index_check(u, z, v0, v1)
    ordinary_routing_checks(v0, v1, w)
    temporal_cases = temporal_phase_checks(u, z, w)
    jw = normalized_choi([(F(1), w)])
    zw = matmul(z, w)
    count = 0
    for p, kappa in product([F(0), F(1, 2), F(9, 10)],
                            [F(0), F(97, 100), F(1)]):
        a, b = (1+kappa)/2, (1-kappa)/2
        alpha, beta = (1-p)**2+p*p, 2*p*(1-p)
        flagged, unflagged, groups = corrected_switch_kraus(u, z, p, kappa)
        actual_flagged = normalized_choi(flagged)
        expected_flagged = normalized_choi([
            (a*alpha, flag_embed(w, 0)), (b*beta, flag_embed(zw, 0)),
            (a*beta, flag_embed(w, 1)), (b*alpha, flag_embed(zw, 1)),
        ])
        require(actual_flagged == expected_flagged,
                "Complete flag/counter/data corrected Choi equality failed.")
        require_tp_choi(actual_flagged, 2*d, 4*d)
        actual = normalized_choi(unflagged)
        expected = normalized_choi([(a, w), (b, zw)])
        require(actual == expected, "Residual phase channel differs from the full Choi output.")
        require_tp_choi(actual, 2*d, 2*d)
        fe = inner(vectorize(jw), vectorize(actual))
        require(fe == gaussian(a), "Entanglement fidelity is not (1+kappa)/2.")
        for flag, probability in [(0, a*alpha+b*beta), (1, a*beta+b*alpha)]:
            require(trace(normalized_choi(groups[flag])) == gaussian(probability),
                    "Reported flag probability is wrong.")
        if kappa == 1:
            require(actual == jw, "Ideal-control correction is not a full unitary channel.")
        # The uncorrected ordinary two-call channel is independently expanded.
        choices, weights = [u, matmul(z, u)], [1-p, p]
        sequence = [(weights[i]*weights[j], matmul(choices[j], choices[i]))
                    for i, j in product(range(2), repeat=2)]
        require(normalized_choi(sequence) == normalized_choi([(alpha, w), (beta, zw)]),
                "Ordinary sequential dephasing law failed.")
        # A fixed program basis value extracts V_j perfectly for every p.
        for program, v in enumerate([v0, v1]):
            extracted = []
            for weight, g in zip(weights, choices):
                block = [[g[(1-program)*d+r][program*d+c] for c in range(d)]
                         for r in range(d)]
                extracted.append((weight, block))
            require(normalized_choi(extracted) == normalized_choi([(F(1), v)]),
                    "Classical program value did not extract a noiseless subroutine.")
        count += 1
    return count, temporal_cases


def main():
    cases = temporal_cases = pairs_checked = 0
    for d in [2, 3]:
        for v0, v1 in pairs(d):
            flagged, temporal = replay_pair(v0, v1)
            cases += flagged
            temporal_cases += temporal
            pairs_checked += 1
    v0, v1 = next(pairs(2))
    u = multiplexor(v0, v1)
    z = diagonal_blocks(identity(2), scaled(identity(2), -1))
    head_cases, clock_cases, reuse_cases = event_head_checks(u, z, matmul(u, u))
    print(json.dumps({
        "status": "passed", "arithmetic": "exact Gaussian rational, standard library",
        "target_dimensions": [2, 3], "noncommuting_unitary_pairs": pairs_checked,
        "full_flagged_choi_cases": cases,
        "classical_phase_trajectory_choi_cases": temporal_cases,
        "event_head_flagged_choi_cases": head_cases,
        "clock_time_choi_cases": clock_cases,
        "fresh_repeat_and_rewind_choi_cases": reuse_cases,
        "p": ["0", "1/2", "9/10"], "kappa": ["0", "97/100", "1"],
        "scope": "Finite full-channel replay; universal no-go and physical slots are analytic inputs.",
    }, sort_keys=True))


if __name__ == '__main__':
    main()
