"""Exact inverse permutation Gram convolution, without character tables.

Permutations are tuples of images and compose(p, q)[i] = p[q[i]].  For the
complete S_n list, G[p,q] = D ** cycles(compose(inverse(p), q)).  Its inverse
is the central convolution kernel h(p^-1 q) returned by
weingarten_by_cycle_type.  The kernel is obtained by solving the small
cycle-class system directly over fractions, not by using S_n characters.

Public APIs:
    weingarten_by_cycle_type(n, D) -> dict[tuple[int,...], Fraction]
    gram_inverse_vector(permutations, D, values) -> list[Fraction]

Cycle-type keys list cycle lengths in descending order.  n <= 6 and D >= n
are required.  The permutation input must contain each element of S_n
exactly once; its ordering may be arbitrary (lexicographic ordering works).
Vector multiplication uses common-denominator integers and creates only
the final output Fractions, avoiding quadratic Fraction arithmetic.

Run this file to write exact self-check results beside it.  Only Python's
standard library is required.
"""

from __future__ import annotations
if not __debug__:
    raise RuntimeError('Exact Gram replay requires Python without -O.')

from fractions import Fraction
from functools import lru_cache
from itertools import permutations as enumerate_permutations
from math import factorial, lcm
from pathlib import Path
import json
import time


def compose(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(p[q[i]] for i in range(len(p)))


def inverse(p: tuple[int, ...]) -> tuple[int, ...]:
    result = [0] * len(p)
    for i, image in enumerate(p):
        result[image] = i
    return tuple(result)


def cycle_type(p: tuple[int, ...]) -> tuple[int, ...]:
    visited = [False] * len(p)
    lengths = []
    for first in range(len(p)):
        if visited[first]:
            continue
        j, length = first, 0
        while not visited[j]:
            visited[j] = True
            length += 1
            j = p[j]
        lengths.append(length)
    return tuple(sorted(lengths, reverse=True))


def _relative_type(pinverse: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    """Cycle type of p^-1 q, without allocating its image tuple."""
    visited = [False] * len(q)
    lengths = []
    for first in range(len(q)):
        if visited[first]:
            continue
        j, length = first, 0
        while not visited[j]:
            visited[j] = True
            length += 1
            j = pinverse[q[j]]
        lengths.append(length)
    return tuple(sorted(lengths, reverse=True))


def _validate_dimensions(n: int, D: int) -> None:
    if not isinstance(n, int) or isinstance(n, bool) or not 0 <= n <= 6:
        raise ValueError("n must be an integer between zero and six")
    if not isinstance(D, int) or isinstance(D, bool) or D < max(1, n):
        raise ValueError("D must be a positive integer satisfying D >= n")


def _fraction_solve(matrix: list[list[int]], rhs: list[int]) -> list[Fraction]:
    size = len(rhs)
    aug = [[Fraction(x) for x in row] + [Fraction(b)]
           for row, b in zip(matrix, rhs)]
    for col in range(size):
        pivot = next((r for r in range(col, size) if aug[r][col]), None)
        if pivot is None:
            raise ArithmeticError("singular central Gram system")
        aug[col], aug[pivot] = aug[pivot], aug[col]
        scale = aug[col][col]
        aug[col] = [x / scale for x in aug[col]]
        for row in range(size):
            if row == col or not aug[row][col]:
                continue
            scale = aug[row][col]
            aug[row] = [x - scale * y for x, y in zip(aug[row], aug[col])]
    return [row[-1] for row in aug]


@lru_cache(maxsize=None)
def _kernel_items(n: int, D: int) -> tuple[tuple[tuple[int, ...], Fraction], ...]:
    _validate_dimensions(n, D)
    perms = list(enumerate_permutations(range(n)))
    types = [cycle_type(p) for p in perms]
    representatives = {}
    for p, kind in zip(perms, types):
        representatives.setdefault(kind, p)
    kinds = sorted(representatives, reverse=True)
    index = {kind: i for i, kind in enumerate(kinds)}
    matrix = []
    rhs = []
    identity = tuple(range(n))
    for kind in kinds:
        p = representatives[kind]
        pinv = inverse(p)
        row = [0] * len(kinds)
        for q, qkind in zip(perms, types):
            relative = _relative_type(pinv, q)
            row[index[qkind]] += D ** len(relative)
        matrix.append(row)
        rhs.append(int(p == identity))
    solution = _fraction_solve(matrix, rhs)
    # An exact residual checks the small linear solve itself.
    for row, expected in zip(matrix, rhs):
        if sum((Fraction(a) * b for a, b in zip(row, solution)), Fraction()) != expected:
            raise ArithmeticError("nonzero exact central-system residual")
    return tuple(zip(kinds, solution))


def weingarten_by_cycle_type(n: int, D: int) -> dict[tuple[int, ...], Fraction]:
    """Return the exact central kernel of the inverse permutation Gram.

    For one representative p of each cycle class, solve
        sum_q D^cycles(p^-1 q) h(type(q)) = 1[p = identity].
    Conjugation invariance extends these equations to every p in S_n.
    Thus the resulting convolution is the inverse Gram kernel.
    """
    return dict(_kernel_items(n, D))


def _common_denominator(values: list[Fraction]) -> tuple[list[int], int]:
    denominator = 1
    for value in values:
        denominator = lcm(denominator, value.denominator)
    numerators = [value.numerator * (denominator // value.denominator)
                  for value in values]
    return numerators, denominator


def gram_inverse_vector(permutations, D: int, values) -> list[Fraction]:
    """Compute G^-1 values exactly for a complete, arbitrarily ordered S_n.

    Values may be ints or Fraction-compatible exact rationals.  Float inputs
    are rejected to avoid silently turning rounded numerical data into an
    apparent exact certificate.
    """
    perms = [tuple(p) for p in permutations]
    if not perms:
        raise ValueError("permutations must contain the complete S_n list")
    n = len(perms[0])
    _validate_dimensions(n, D)
    if len(perms) != factorial(n) or len(set(perms)) != len(perms):
        raise ValueError("permutations must contain every S_n element once")
    expected = set(range(n))
    if any(len(p) != n or set(p) != expected for p in perms):
        raise ValueError("invalid permutation images")
    data = list(values)
    if len(data) != len(perms):
        raise ValueError("values length does not match permutation count")
    if any(isinstance(value, (float, complex)) for value in data):
        raise TypeError("use exact integers or Fractions, not floats/complex")
    fractions = [Fraction(value) for value in data]
    h = weingarten_by_cycle_type(n, D)
    kinds = list(h)
    h_nums, h_den = _common_denominator([h[kind] for kind in kinds])
    numerators = dict(zip(kinds, h_nums))
    f_nums, f_den = _common_denominator(fractions)
    nonzero = [(p, value) for p, value in zip(perms, f_nums) if value]
    denominator = h_den * f_den
    answer = []
    for p in perms:
        pinv = inverse(p)
        total = sum(numerators[_relative_type(pinv, q)] * value
                    for q, value in nonzero)
        answer.append(Fraction(total, denominator))
    return answer


def _gram_vector(perms, D, values):
    """Independent exact forward multiplication used only for self-tests."""
    nums, denominator = _common_denominator([Fraction(x) for x in values])
    result = []
    for p in perms:
        pinv = inverse(p)
        total = 0
        for q, value in zip(perms, nums):
            if value:
                rel = compose(pinv, q)
                total += D ** len(cycle_type(rel)) * value
        result.append(Fraction(total, denominator))
    return result


def self_test() -> list[dict]:
    records = []
    for n in (2, 4, 6):
        perms = list(enumerate_permutations(range(n)))
        for D in (6, 8):
            started = time.perf_counter()
            h = weingarten_by_cycle_type(n, D)
            # Test every convolution coordinate, not just representatives.
            kernel = [h[cycle_type(p)] for p in perms]
            image = _gram_vector(perms, D, kernel)
            expected = [Fraction(int(p == tuple(range(n)))) for p in perms]
            assert image == expected
            # Dense signed rational vector tests orientation and scaling.
            vector = [Fraction((17 * i + 3) % 29 - 14, 1 + (i % 7))
                      for i in range(len(perms))]
            result = gram_inverse_vector(perms, D, vector)
            assert _gram_vector(perms, D, result) == vector
            # Reversing the enumeration must only reverse the answer.
            reversed_result = gram_inverse_vector(perms[::-1], D, vector[::-1])
            assert reversed_result == result[::-1]
            records.append({
                "n": n, "D": D, "permutations": len(perms),
                "cycle_classes": len(h),
                "all_kernel_coordinates_exact": True,
                "dense_vector_inverse_exact": True,
                "arbitrary_enumeration_order_exact": True,
                "kernel": {",".join(map(str, kind)): str(value)
                           for kind, value in h.items()},
                "elapsed_seconds": time.perf_counter() - started,
            })
    return records


if __name__ == "__main__":
    records = self_test()
    output = Path(__file__).with_name("brauer_weingarten_tests.json")
    output.write_text(json.dumps({
        "convention": "compose(p,q)[i]=p[q[i]]; G[p,q]=D^cycles(p^-1 q)",
        "method": "exact central class system and integer convolution",
        "tests": records,
    }, indent=2), encoding="utf-8")
    print(json.dumps({"output": str(output), "tests_passed": len(records),
                      "elapsed_seconds": sum(r["elapsed_seconds"] for r in records)}, indent=2))
