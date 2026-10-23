"""Exact finite guards for the partial-Bell burst relation test."""

from fractions import Fraction as F
from itertools import product
import json
import sys

if sys.flags.optimize:
    raise RuntimeError('Run without -O')


def bracket(a, b, n):
    mask = (1 << n) - 1
    return (((a & mask) & (b >> n)).bit_count()
            + ((b & mask) & (a >> n)).bit_count()) & 1


def lagrangians(n):
    spaces = {(0,)}
    for _ in range(n):
        extended = set()
        for ell in spaces:
            for a in range(1, 1 << (2 * n)):
                if a not in ell and not any(bracket(a, b, n) for b in ell):
                    extended.add(tuple(sorted(ell + tuple(a ^ b for b in ell))))
        spaces = extended
    return sorted(spaces)


def project(label, n, k):
    mask = (1 << k) - 1
    r = (label & mask) | (((label >> n) & mask) << k)
    x = (label >> k) & ((1 << (n - k)) - 1)
    return x, r


def stream_reject(records, k):
    pivots, relations = {}, {}
    for x, r in records:
        while x:
            j = x.bit_length() - 1
            if j not in pivots:
                pivots[j] = x, r
                break
            a, b = pivots[j]
            x, r = x ^ a, r ^ b
        if x:
            continue
        if any(bracket(r, old, k) for old in relations.values()):
            return True
        while r:
            j = r.bit_length() - 1
            if j not in relations:
                relations[j] = r
                break
            r ^= relations[j]
    return False


def exhaustive_reject(records, k):
    relations = set()
    for bits in product((0, 1), repeat=len(records)):
        x, r = 0, 0
        for bit, (a, b) in zip(bits, records):
            if bit:
                x, r = x ^ a, r ^ b
        if not x:
            relations.add(r)
    return any(bracket(a, b, k) for a in relations for b in relations)


def verify():
    sound_cases = streaming_cases = conditional_x_cases = known_cases = 0
    rejection_rows = []
    for n, k, length in ((1, 1, 3), (2, 1, 4), (2, 2, 3)):
        for ell in lagrangians(n):
            for errors in product(ell, repeat=length):
                assert all(bracket(a, b, n) == 0 for a in errors for b in errors)
                records = [project(a, n, k) for a in errors]
                assert not exhaustive_reject(records, k)
                assert not stream_reject(records, k)
                sound_cases += 1
            # Any known nonzero direction gives the simpler product-probe test.
            for known in ell[1:]:
                assert all(bracket(known, a, n) == 0 for a in ell)
                uniform_bad = sum(bracket(known, a, n) for a in range(4 ** n))
                assert F(uniform_bad, 4 ** n) == F(1, 2)
                known_cases += 1
    for m, k in ((0, 1), (1, 1), (2, 1), (1, 2)):
        length = m + 2
        for xs in product(range(1 << m), repeat=length):
            rejected, total = 0, 0
            for rs in product(range(1 << (2 * k)), repeat=length):
                records = list(zip(xs, rs))
                result = stream_reject(records, k)
                # Independent brute-kernel construction on a varied subfamily.
                if (sum(xs) + sum(rs)) % 17 == 0:
                    assert result == exhaustive_reject(records, k)
                    streaming_cases += 1
                rejected += result
                total += 1
            probability = F(rejected, total)
            lower = (1 - F(1, 4 ** k)) / 2
            assert probability >= lower
            rejection_rows.append(probability)
            conditional_x_cases += 1
    x = F(49, 8)
    assert 1 + x + x * x / 2 > 9
    assert F(3, 8) * (1 - F(1, 9)) == F(1, 3)
    return {'status': 'passed', 'arithmetic': 'exact binary and Fraction',
            'commuting_error_streams': sound_cases,
            'streaming_vs_complete_kernel_cases': streaming_cases,
            'conditional_uniform_burst_x_matrices': conditional_x_cases,
            'minimum_rejection_probability': str(min(rejection_rows)),
            'known_direction_checks': known_cases,
            'scope': 'Finite algebraic guards; all-n query/concentration and physical assumptions are analytic.'}


if __name__ == '__main__':
    print(json.dumps(verify(), indent=2))
