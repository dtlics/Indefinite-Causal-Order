"""Exact finite-code recovery certificate for ordinary rank-one Gaussian noise.

Reconstructs the finite Choi/overflow channel from Gaussian moments using only
integer dyadic intervals. No floating arithmetic, NumPy, noise quadrature,
optimizer, Mehler/source-tail approximation or hardware claim is used.
The analytic kernel, controller circuit and recovery proof are in
methods/heat-gkp-certification.md. The rational source is itself the actual code.
"""
if not __debug__:
    raise RuntimeError("The certificate requires assertions; omit -O")

from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import factorial, isqrt
from pathlib import Path
import json

BITS = 160
DEN = 1 << BITS
ZERO = (0, 0)


def rational(q):
    q = F(q)
    numerator = q.numerator * DEN
    return numerator // q.denominator, -((-numerator) // q.denominator)


@lru_cache(None)
def coefficient(q, numerator, denominator):
    """Exact outward bracket of q*sqrt(numerator/denominator)."""
    q = F(q)
    if not q or not numerator:
        return ZERO
    square = q*q*F(numerator, denominator)
    top, bottom = square.numerator * DEN * DEN, square.denominator
    low = isqrt(top // bottom)
    high = low if low*low*bottom == top else low+1
    assert low*low*bottom <= top <= high*high*bottom
    return (low, high) if q > 0 else (-high, -low)


def add(x, y):
    return x[0]+y[0], x[1]+y[1]


def scale(x, c):
    """Integer floor/ceiling products; multiplier has a known sign."""
    low, high = c
    if low == high == 0 or x == ZERO:
        return ZERO
    if high <= 0:
        x, low, high = (-x[1], -x[0]), -high, -low
    assert low >= 0
    lo = (low if x[0] >= 0 else high)*x[0]
    hi = (low if x[1] <= 0 else high)*x[1]
    return lo >> BITS, -((-hi) >> BITS)


def planes(target, source):
    """Normalized f[m,n,p,q] for a=1/4,b=0, in rolling q planes."""
    # Q=Q0+h h^T/10, h=(1,-1,1,-1); Z=2/sqrt(5).
    h = (1, -1, 1, -1)
    q = tuple(tuple(F(h[i]*h[j], 10)
                    + F(i != j and {i, j} in ({0, 1}, {2, 3}))
                    for j in range(4)) for i in range(4))
    size = target*source*target
    index = lambda m, n, p: (m*source+n)*target+p
    previous = [ZERO]*size
    previous[0] = coefficient(1, 4, 5)
    for m in range(2, target, 2):
        previous[index(m, 0, 0)] = scale(
            previous[index(m-2, 0, 0)], coefficient(q[0][0], m-1, m))
    for n in range(1, source):
        for m in range(n % 2, target, 2):
            total = ZERO
            if m:
                total = scale(previous[index(m-1, n-1, 0)],
                              coefficient(q[1][0], m, n))
            if n >= 2:
                total = add(total, scale(previous[index(m, n-2, 0)],
                                        coefficient(q[1][1], n-1, n)))
            previous[index(m, n, 0)] = total
    for p in range(1, target):
        for m in range(target):
            for n in range((m+p) % 2, source, 2):
                total = ZERO
                if m:
                    total = scale(previous[index(m-1, n, p-1)],
                                  coefficient(q[2][0], m, p))
                if n:
                    total = add(total, scale(previous[index(m, n-1, p-1)],
                                            coefficient(q[2][1], n, p)))
                if p >= 2:
                    total = add(total, scale(previous[index(m, n, p-2)],
                                            coefficient(q[2][2], p-1, p)))
                previous[index(m, n, p)] = total
    yield 0, previous
    before = None
    for s in range(1, source):
        current = [ZERO]*size
        cm = [coefficient(q[3][0], m, s) for m in range(target)]
        cn = [coefficient(q[3][1], n, s) for n in range(source)]
        cp = [coefficient(q[3][2], p, s) for p in range(target)]
        cs = coefficient(q[3][3], s-1, s)
        for m in range(target):
            for n in range(source):
                for p in range((m+n+s) % 2, target, 2):
                    total = ZERO
                    if m:
                        total = scale(previous[index(m-1, n, p)], cm[m])
                    if n:
                        total = add(total, scale(previous[index(m, n-1, p)], cn[n]))
                    if p:
                        total = add(total, scale(previous[index(m, n, p-1)], cp[p]))
                    if s >= 2:
                        total = add(total, scale(before[index(m, n, p)], cs))
                    current[index(m, n, p)] = total
        yield s, current
        before, previous = previous, current


def finite_channel(code, cutoff):
    source, target = len(code), cutoff+1
    bound = [[rational(x) for x in row] for row in code]
    active = [n for n, row in enumerate(code) if any(row)]
    action = [[[ZERO]*(target*target) for _ in range(2)] for _ in range(2)]
    for s, plane in planes(target, source):
        if s not in active:
            continue
        for i in range(2):
            first = [ZERO]*(target*target)
            for n in active:
                for m in range(target):
                    offset = (m*source+n)*target
                    for p in range(target):
                        j = m*target+p
                        first[j] = add(first[j], scale(plane[offset+p], bound[n][i]))
            for j in range(2):
                for k, value in enumerate(first):
                    action[i][j][k] = add(action[i][j][k], scale(value, bound[s][j]))
    output = target+1  # one receiver erasure symbol
    rho = [[ZERO]*(2*output) for _ in range(2*output)]
    for i in range(2):
        for j in range(2):
            trace = ZERO
            for m in range(target):
                for p in range(target):
                    low, high = action[i][j][m*target+p]
                    value = low >> 1, -((-high) >> 1)
                    rho[i*output+m][j*output+p] = value
                    if m == p:
                        trace = add(trace, value)
            full = DEN//2 if i == j else 0
            rho[i*output+target][j*output+target] = full-trace[1], full-trace[0]
    return rho


def recovery_lower(rho, blocks, factor_bits):
    """Y=LL^T; exact positive TP completion, evaluated on intervals."""
    assert factor_bits == 40
    size, output = len(rho), len(rho)//2
    y = [[0]*size for _ in range(size)]
    covered = []
    for block in blocks:
        indices = block["output_indices"]
        assert indices == sorted(set(indices))
        covered += indices
        global_indices = indices+[output+i for i in indices]
        factor = block["factor"]
        assert len(factor) == len(global_indices)
        assert all(len(row) == len(factor) for row in factor)
        assert all(isinstance(x, int) and not isinstance(x, bool)
                   for row in factor for x in row)
        for a, row in enumerate(factor):
            for b, other in enumerate(factor):
                y[global_indices[a]][global_indices[b]] = sum(x*z for x, z in zip(row, other))
    assert sorted(covered) == list(range(output))
    s = [[y[i][j]+y[output+i][output+j] for j in range(output)]
         for i in range(output)]
    kappa = max(s[i][i]+sum(abs(s[i][j]) for j in range(output) if j != i)
                for i in range(output))
    assert kappa > 0
    xn = [[2*y[i][j] for j in range(size)] for i in range(size)]
    for i in range(output):
        for j in range(output):
            completion = (kappa if i == j else 0)-s[i][j]
            xn[i][j] += completion
            xn[output+i][output+j] += completion
            assert xn[i][j]+xn[output+i][output+j] == (2*kappa if i == j else 0)
    # X=xn/(2*kappa) is PSD and Tr_R X=I. The input Choi is normalized,
    # so entanglement fidelity is Tr(rho X)/2.
    numerator = 0
    for i in range(size):
        for j in range(size):
            weight = xn[j][i]
            numerator += weight*rho[i][j][0 if weight >= 0 else 1]
    return F(numerator, 4*kappa*DEN)


def independent_moment_guards():
    """Direct normalordered real-displacement polynomials, not Wick recursion."""
    count = 0
    for s, plane in planes(3, 3):
        for m, n, p in product(range(3), repeat=3):
            raw = F(0)
            for k in range(min(m, n)+1):
                a = F(factorial(m)*factorial(n)*(-1)**(n-k),
                      factorial(m-k)*factorial(n-k)*factorial(k))
                for l in range(min(p, s)+1):
                    b = F(factorial(p)*factorial(s)*(-1)**(s-l),
                          factorial(p-l)*factorial(s-l)*factorial(l))
                    degree = m+n+p+s-2*k-2*l
                    if degree % 2 == 0:
                        moment = F(1, 10**(degree//2))
                        for j in range(1, degree, 2):
                            moment *= j
                        raw += a*b*moment
            lo, hi = plane[(m*3+n)*3+p]
            square = raw*raw*F(4, 5)
            for j in (m, n, p, s):
                square /= factorial(j)
            if raw < 0:
                lo, hi = -hi, -lo
            if raw:
                assert (lo <= 0 or F(lo, DEN)**2 <= square)
                assert hi >= 0 and F(hi, DEN)**2 >= square
            else:
                assert lo <= 0 <= hi
            count += 1
    return count


def verify():
    data = json.loads(Path(__file__).with_name("heat_gkp_recovery.json").read_text(encoding="utf-8"))
    assert data["schema"] == "heat-gkp-recovery-v1"
    assert data["source_cutoff"] == 32 and data["output_cutoff"] == 24
    assert F(data["q_variance"]) == F(1, 4)
    code = [[F(x) for x in row] for row in data["source"]]
    assert len(code) == 33 and all(len(row) == 2 for row in code)
    assert all(row == [0, 0] for row in code[1::2])
    for i in range(2):
        for j in range(2):
            assert sum(row[i]*row[j] for row in code) == F(i == j)
    energy = [[sum(n*row[i]*row[j] for n, row in enumerate(code))
               for j in range(2)] for i in range(2)]
    a, b, c = F(117, 50)-energy[0][0], -energy[0][1], F(117, 50)-energy[1][1]
    assert a > 0 and c > 0 and a*c-b*b > 0
    guards = independent_moment_guards()
    rho = finite_channel(code, 24)
    score = recovery_lower(rho, data["blocks"], data["factor_bits"])
    assert score > F(919, 1000)
    return {"status": "passed", "dyadic_interval_bits": BITS,
            "source_fock_dimension": 33, "receiver_output_dimension": 26,
            "normalized_choi_dimension": 52, "recovery_blocks": len(data["blocks"]),
            "independent_gaussian_moment_guards": guards,
            "all_input_source_energy_upper": "117/50",
            "certified_entanglement_fidelity_lower": str(score),
            "strict_comparison_lower": "919/1000",
            "scope": "Exact finite rational code, Gaussian channel and completed recovery witness. "
                     "No optimizer, infinite heat-source approximation, decoder implementation, "
                     "ordinary optimum or measured hardware advantage."}


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2, sort_keys=True))
