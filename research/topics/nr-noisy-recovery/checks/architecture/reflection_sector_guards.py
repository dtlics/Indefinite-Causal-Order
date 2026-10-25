"""Exact finite guards for the declared ideal global Rydberg symmetry cut.

No exponentiation, optimization, noisy apparatus simulation or design test.
The analytic support and Haar-moment arguments remain proof inputs.
"""
from fractions import Fraction as F

if not __debug__:
    raise RuntimeError('Run exact reflection fixtures without -O.')
from verify_fault_simulation import (ZERO, ONE, gaussian, add, times,
                                     identity, adjoint, matmul, tensor)


def scale(a, k):
    return [[times(x, k) for x in row] for row in a]


def plus(a, b):
    return [[add(x, y) for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def tr(a):
    out = ZERO
    for j in range(len(a)):
        out = add(out, a[j][j])
    return out


def reverse_bits(x, n):
    return sum(((x >> j) & 1) << (n-1-j) for j in range(n))


def global_rows(n, omega, delta, coupling):
    """Sparse exact H=omega sum X - delta sum n + sum n_j n_k/|j-k|^6."""
    rows = []
    for b in range(1 << n):
        bits = [(b >> j) & 1 for j in range(n)]
        diag = -delta*sum(bits)
        diag += coupling*sum((F(bits[j]*bits[k], (k-j)**6)
                              for j in range(n) for k in range(j+1, n)), F(0))
        row = {b: diag}
        for j in range(n):
            row[b ^ (1 << j)] = omega
        rows.append(row)
    return rows


def compressed_diagonal_trace(n, a, b):
    """Tr(P_+ A P_+ B) for diagonal A,B, without dense 2^n matrices."""
    out = F(0)
    for x in range(1 << n):
        rx = reverse_bits(x, n)
        ks = {x, rx}
        p = F(1) if x == rx else F(1, 2)
        for k in ks:
            out += p*p*a[k]*b[x]
    return out


def check():
    cases = []
    for n in range(2, 9):
        d = 1 << n
        palindromes = sum(reverse_bits(x, n) == x for x in range(d))
        assert palindromes == (1 << ((n+1)//2))
        rplus, rminus = (d+palindromes)//2, (d-palindromes)//2
        assert rplus+rminus == d
        # Check the three actual generator types separately, and a mixed H.
        for pars in [(F(1), F(0), F(0)), (F(0), F(1), F(0)),
                     (F(0), F(0), F(1)), (F(3, 2), F(2, 5), F(7, 3))]:
            h = global_rows(n, *pars)
            for x in range(d):
                reflected = {reverse_bits(y, n): v for y, v in h[x].items()}
                assert h[reverse_bits(x, n)] == reflected
        zfirst = [F((-1)**(x & 1)) for x in range(d)]
        zlast = [F((-1)**((x >> (n-1)) & 1)) for x in range(d)]
        contrast = [a-b for a, b in zip(zfirst, zlast)]
        assert compressed_diagonal_trace(n, contrast, contrast) == 0
        assert sum(contrast) == 0
        full_contrast = sum(c*c for c in contrast)/F(d*(d+1))
        assert full_contrast == F(2, d+1)
        variance = compressed_diagonal_trace(n, zfirst, zfirst)/F(rplus*(rplus+1))
        covariance = compressed_diagonal_trace(n, zfirst, zlast)/F(rplus*(rplus+1))
        assert variance == covariance > 0
        if n == 8:
            assert (rplus, rminus, F(rminus, d)) == (136, 120, F(15, 32))
            assert variance == F(9, 2329)
            assert full_contrast == F(2, 257)
        cases.append({'n': n, 'd': d, 'rplus': rplus, 'rminus': rminus,
                      'support_trace_distance_lower': str(F(rminus, d)),
                      'full_Haar_contrast_second_moment': str(full_contrast),
                      'sector_Haar_mirror_covariance': str(covariance)})
    # Local mirror-pair sqrt-SWAP identity. Its identity extension commutes
    # with whole-chain reversal; this is not a compiled Rydberg pulse.
    i = identity(2)
    z = [[ONE, ZERO], [ZERO, gaussian(-1)]]
    swap = [[gaussian(int(j == ((k & 1)*2+(k >> 1))))
             for k in range(4)] for j in range(4)]
    psym = scale(plus(identity(4), swap), F(1, 2))
    pasym = scale(plus(identity(4), scale(swap, -1)), F(1, 2))
    u = [[add(a, (F(0), b[0])) for a, b in zip(ar, br)]
         for ar, br in zip(psym, pasym)]
    assert matmul(adjoint(u), u) == identity(4)
    assert matmul(swap, u) == matmul(u, swap)
    w, v = tensor(z, i), tensor(i, z)
    a = matmul(matmul(adjoint(u), w), u)
    b = matmul(matmul(v, a), v)
    assert b == matmul(matmul(swap, a), swap)
    assert matmul(matmul(psym, a), psym) == matmul(matmul(psym, b), psym)
    self_trace = tr(matmul(matmul(matmul(psym, a), psym), a))
    cross_trace = tr(matmul(matmul(matmul(psym, a), psym), b))
    assert self_trace == cross_trace == gaussian(2)
    assert tr(matmul(a, b)) == ZERO
    return {'status': 'passed', 'reflection_generator_and_moment_cases': cases,
            'sqrt_SWAP_full_trace_OTOC': '0',
            'sqrt_SWAP_normalized_sector_correlation': '1',
            'scope': 'Declared noiseless uniform open chain/global controls only; sector-Haar formulas are conditional, actual quench mixing and noisy hardware design/OTOC bias are not certified.'}


if __name__ == '__main__':
    import json
    print(json.dumps(check(), sort_keys=True))
