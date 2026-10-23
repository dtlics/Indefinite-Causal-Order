"""Exact finite likelihood/counting checks for the scoped fixed-probe bound."""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import product
import json

if not __debug__:
    raise RuntimeError("Run fixed-probe guards without -O.")


def bracket(a, b, n):
    mask = (1 << n) - 1
    return (((a & mask) & (b >> n)).bit_count()
            + ((b & mask) & (a >> n)).bit_count()) & 1


def lagrangians(n):
    spaces = {(0,)}
    for _ in range(n):
        extended = set()
        for ell in spaces:
            for v in range(1, 1 << (2*n)):
                if v not in ell and not any(bracket(v, u, n) for u in ell):
                    extended.add(tuple(sorted(ell + tuple(v ^ u for u in ell))))
        spaces = extended
    return sorted(spaces)


def rank(values):
    pivots = {}
    for value in values:
        while value:
            pivot = value.bit_length() - 1
            if pivot in pivots:
                value ^= pivots[pivot]
            else:
                pivots[pivot] = value
                break
    return len(pivots)


def record(a, n, k):
    # Low n bits are x; high n bits are z. Record x_M in low m bits.
    m, rm = n-k, (1 << k)-1
    y = (a >> k) & ((1 << m)-1)
    referenced = (a & rm) | (((a >> n) & rm) << k)
    return y | (referenced << m)


def check_case(n, k, t_calls):
    m, d = n-k, 1 << n
    ls = lagrangians(n)
    size = 1 << (n+k)
    counts = defaultdict(int)
    for ell in ls:
        projected = Counter(record(a, n, k) for a in ell)
        for stream in product(projected, repeat=t_calls):
            weight = 1
            for c in stream:
                weight *= projected[c]
            counts[stream] += weight
    denominator = len(ls) * d ** t_calls
    p0 = F(1, size ** t_calls)
    good_p0 = good_p1 = tv = F(0)
    likelihood = F(1)
    good0_formula = good1_formula = F(1)
    for j in range(t_calls):
        likelihood /= 1 + F(2**j, 2**n)
        good0_formula *= 1-F(2**j, 2**m)
        good1_formula *= (1-F(2**j, 2**m))/(1+F(2**j, 2**n))
    good_records = 0
    for stream in product(range(size), repeat=t_calls):
        p1 = F(counts.get(stream, 0), denominator)
        tv += abs(p1-p0)/2
        if rank([c & ((1 << m)-1) for c in stream]) == t_calls:
            assert p1/p0 == likelihood
            good_p0 += p0
            good_p1 += p1
            good_records += 1
    assert good_p0 == good0_formula and good_p1 == good1_formula
    assert tv <= 1-good_p1
    bound = (2**t_calls-1)*(F(1, 2**m)+F(1, 2**n))
    assert 1-good_p1 <= bound
    return {"n": n, "references": k, "burst_calls": t_calls,
            "lagrangians": len(ls), "good_records": good_records,
            "good_likelihood": str(likelihood), "TV": str(tv),
            "good_p1": str(good_p1), "union_bound": str(bound)}


def verify():
    rows = [check_case(n, k, t) for n in (1, 2, 3)
            for k in range(n) for t in range(1, n-k+1)]
    # Explicit expected-budget constants, worst t<=1 and m>=16.
    assert F(1, 24)+F(1, 16)+F(2, 16)+F(1, 128) < F(1, 3)
    assert F(1, 24)+F(1, 16)+F(2, 16)+F(1, 128)+F(1, 24) < F(1, 3)
    return {"status": "passed", "cases": rows,
            "scope": "Finite exact fixed-layout likelihoods, not a general ordinary-query bound."}


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
