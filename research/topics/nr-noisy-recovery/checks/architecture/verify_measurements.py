"""Exact finite measurement examples supporting architecture-baselines.md.

Uses only standard-library rational arithmetic.  The analytic all-dimensional
arguments and physical access assumptions remain in the canonical note.
This verifier prints JSON and creates no files; the runner owns build logs.
"""
from __future__ import annotations

if not __debug__:
    raise RuntimeError("Exact measurement checks require assertions; do not use -O.")

from fractions import Fraction as F
import json


def zero(d: int) -> list[list[F]]:
    return [[F(0) for _ in range(d)] for _ in range(d)]


def eye(d: int) -> list[list[F]]:
    a = zero(d)
    for i in range(d):
        a[i][i] = F(1)
    return a


def add(a, b):
    return [[x + y for x, y in zip(r, s)] for r, s in zip(a, b)]


def scale(a, x):
    return [[x * y for y in r] for r in a]


def transpose(a):
    return list(map(list, zip(*a)))


def mul(a, b):
    out = [[F(0) for _ in range(len(b[0]))] for _ in range(len(a))]
    for i, row in enumerate(a):
        for k, x in enumerate(row):
            if not x:
                continue
            for j, y in enumerate(b[k]):
                if y:
                    out[i][j] += x * y
    return out


def tr(a):
    return sum((a[i][i] for i in range(len(a))), F(0))


def kron(a, b):
    return [[a[i // len(b)][j // len(b[0])] * b[i % len(b)][j % len(b[0])]
             for j in range(len(a[0]) * len(b[0]))]
            for i in range(len(a) * len(b))]


def binary_pvm(h):
    return [scale(add(eye(len(h)), scale(h, F(s))), F(1, 2))
            for s in (1, -1)]


def check_pvm(projectors):
    d = len(projectors[0])
    total = zero(d)
    for i, p in enumerate(projectors):
        assert p == transpose(p) and mul(p, p) == p
        total = add(total, p)
        for j, q in enumerate(projectors):
            if i != j:
                assert mul(p, q) == zero(d)
    assert total == eye(d)


def choi(kraus):
    """Normalized input-first Choi matrix; all tested matrices are real."""
    d = len(kraus[0])
    result = zero(d * d)
    for k in kraus:
        vector = [k[out][inp] for inp in range(d) for out in range(d)]
        result = add(result, [[x * y / d for y in vector] for x in vector])
    return result


def bell_return(choi_matrix, d):
    return sum((choi_matrix[i * (d + 1)][j * (d + 1)]
                for i in range(d) for j in range(d)), F(0)) / d


def metrics(p, q):
    check_pvm(p)
    check_pvm(q)
    d = len(p[0])
    cross_formula = sum((tr(mul(a, b)) ** 2 for a in p for b in q), F(0)) / d**2
    rho_e, rho_f = choi(p), choi(q)
    cross_direct = tr(mul(rho_e, rho_f))
    sequential_return = bell_return(choi([mul(b, a) for a in p for b in q]), d)
    assert cross_formula == cross_direct == sequential_return

    v = sum((tr(mul(mul(mul(a, b), a), b)) for a in p for b in q), F(0)) / d
    record_equal = sum((tr(mul(mul(mul(mul(a, b), a), b), a))
                        for a in p for b in q), F(0)) / d
    commutator_minus = F(0)
    for a in p:
        for b in q:
            commutator = add(mul(a, b), scale(mul(b, a), F(-1)))
            commutator_minus += tr(mul(transpose(commutator), commutator)) / (4 * d)
    assert v == record_equal
    assert commutator_minus == (1 - v) / 2
    assert 0 <= v <= 1
    return cross_direct, v, commutator_minus


def trace_filter_check(h):
    """Check the entire small CP map on a matrix-unit basis, not just states."""
    d = len(h)
    assert h == transpose(h) and mul(h, h) == eye(d) and tr(h) == 0
    filtered = [scale(add(k, scale(eye(d), -tr(k) / d)), F(1, 2))
                for k in binary_pvm(h)]
    assert filtered == [scale(h, F(1, 4)), scale(h, F(-1, 4))]
    effect = zero(d)
    for k in filtered:
        effect = add(effect, mul(transpose(k), k))
    assert effect == scale(eye(d), F(1, 8))
    for i in range(d):
        for j in range(d):
            unit = zero(d)
            unit[i][j] = F(1)
            actual = zero(d)
            for k in filtered:
                actual = add(actual, mul(mul(k, unit), transpose(k)))
            assert actual == scale(mul(mul(h, unit), h), F(1, 8))
    return d * d


def main():
    z = [[F(1), F(0)], [F(0), F(-1)]]
    x = [[F(0), F(1)], [F(1), F(0)]]
    p4 = kron(z, eye(2))
    q_angle = kron(add(scale(z, F(3, 5)), scale(x, F(4, 5))), eye(2))
    binary_cases = (
        ("same", p4, p4, (F(1, 2), F(1), F(0))),
        ("strong-MUB-syndrome", p4, kron(x, eye(2)), (F(1, 4), F(1, 2), F(1, 4))),
        ("commuting-independent-syndrome", p4, kron(eye(2), z), (F(1, 4), F(1), F(0))),
        ("rational-angle", p4, q_angle, (F(17, 50), F(17, 25), F(4, 25))),
        ("protected-rank-three", kron(z, eye(3)), kron(x, eye(3)),
         (F(1, 4), F(1, 2), F(1, 4))),
    )
    rows = []
    involutions = {}
    for name, p, q, expected in binary_cases:
        actual = metrics(binary_pvm(p), binary_pvm(q))
        assert actual == expected, (name, actual, expected)
        d = len(p)
        tau = tr(mul(mul(mul(p, q), p), q)) / d
        assert actual[1] == (3 + tau) / 4 and actual[2] == (1 - tau) / 8
        assert tr(mul(mul(mul(q, p), q), p)) / d == tau
        for h in (p, q):
            involutions[tuple(map(tuple, h))] = h
        rows.append({"case": name, "dimension": d,
                     "Choi_cross_overlap_and_sequential_Bell_return": str(actual[0]),
                     "switch_visibility_and_record_return": str(actual[1]),
                     "switch_minus": str(actual[2]), "tau": str(tau)})

    # Exact rational 4x4 Walsh basis supplies a non-binary rank-one example.
    h2 = [[F(1), F(1)], [F(1), F(-1)]]
    h4 = scale(kron(h2, h2), F(1, 2))
    assert mul(transpose(h4), h4) == eye(4)
    computational = []
    for i in range(4):
        projector = zero(4)
        projector[i][i] = F(1)
        computational.append(projector)
    walsh = [mul(mul(h4, p), transpose(h4)) for p in computational]
    actual = metrics(computational, walsh)
    assert actual == (F(1, 16), F(1, 4), F(3, 8))
    rows.append({"case": "rank-one-Walsh-four-outcome", "dimension": 4,
                 "Choi_cross_overlap_and_sequential_Bell_return": str(actual[0]),
                 "switch_visibility_and_record_return": str(actual[1]),
                 "switch_minus": str(actual[2])})

    rank_checks = 0
    for s in (2, 4, 8, 16):
        for m in (1, 2, 7, 32):
            d = s * m
            assert F(s * m * m, d * d) == F(1, s)
            assert F(s * s, d * d) * F(m, s)**2 == F(1, s * s)
            assert F(s * s * m, d * s * s) == F(1, s)
            assert F(1, s) - F(1, s * s) >= F(1, 2 * s)
            rank_checks += 1

    matrix_units = sum(trace_filter_check(h) for h in involutions.values())
    success = F(1, 8)
    four_successes = success**4
    full_attempt_cost = 4 / four_successes
    early_abort_cost = sum((success**j for j in range(4)), F(0)) / four_successes
    assert four_successes == F(1, 4096)
    assert full_attempt_cost == 16384 and early_abort_cost == 4680

    report = {
        "status": "passed", "arithmetic": "standard-library Fraction matrices",
        "scope": ("Finite exact PVM/Choi/record/commutator examples and balanced-binary "
                  "filter CP identities; scalar rank and retry arithmetic. Analytic "
                  "generalization and physical access assumptions remain in architecture-baselines.md."),
        "examples": rows, "finite_rank_scaling_checks": rank_checks,
        "balanced_binary_filter_examples": len(involutions),
        "filter_matrix_unit_checks": matrix_units,
        "four_filter_success_probability": str(four_successes),
        "expected_calls_per_retained_scalar_sample_full_attempts": str(full_attempt_cost),
        "expected_calls_per_retained_scalar_sample_early_abort": str(early_abort_cost),
        "limitations": ["No hardware runtime, detector-noise, generic bath, or optimal-strategy proof.",
                        "No all-dimensional representation theorem or Lean formalization is replayed."],
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
