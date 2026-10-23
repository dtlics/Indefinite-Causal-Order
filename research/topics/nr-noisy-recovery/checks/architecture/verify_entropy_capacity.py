"""Finite exact guards for the Pauli self-commutation entropy certificate.

The all-dimension entropy argument and the quantum coding theorem are
analytic dependencies, not consequences of these finite checks.
"""

from fractions import Fraction as F
from math import isqrt
import json

if not __debug__:
    raise RuntimeError("Run entropy/capacity guards without -O.")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def bracket(a, b, n):
    mask = (1 << n) - 1
    return (((a & mask) & (b >> n)).bit_count()
            + ((b & mask) & (a >> n)).bit_count()) & 1


def bias(p, q, h):
    return sum((pa * qb * h[a][b]
                for a, pa in enumerate(p) if pa
                for b, qb in enumerate(q) if qb), F(0))


def uniform(size, support):
    support = list(support)
    require(support, "nonempty support")
    p = [F(0)] * size
    for a in support:
        p[a] = F(1, len(support))
    return p


def mix(weighted_laws):
    size = len(weighted_laws[0][1])
    result = [sum((w * p[a] for w, p in weighted_laws), F(0))
              for a in range(size)]
    require(min(result) >= 0 and sum(result) == 1, "normalized mixture")
    return result


def sqrt_upper(value, denominator=10**6):
    """Smallest grid rational >= sqrt(value), using integer arithmetic."""
    require(value >= 0 and denominator > 0, "square-root domain")
    numerator, divisor = value.numerator, value.denominator
    scaled = numerator * denominator * denominator
    k = isqrt(scaled // divisor)
    if k * k * divisor < scaled:
        k += 1
    result = F(k, denominator)
    require(result * result >= value, "upper square-root certificate")
    if k:
        require(F(k - 1, denominator) ** 2 < value, "smallest grid upper root")
    return result


def conservative_certificate(n, identity_lower, eta_lower):
    """Use h2 <= 1, C_D < 3 and a certified upper square root."""
    root = sqrt_upper(1 - eta_lower)
    return max(F(0), (identity_lower - root) * n
               - 1 - 3 * (1 - identity_lower))


def verify_entropy_capacity():
    matrix_entries = threshold_cases = conditional_cases = root_cases = 0
    counter_cases = full_support_cases = distribution_cases = 0
    for n in (1, 2, 3):
        d, size = 1 << n, 1 << (2 * n)
        h = [[1 - 2 * bracket(a, b, n) for b in range(size)]
             for a in range(size)]
        for a in range(size):
            for b in range(size):
                require(sum(h[a][j] * h[j][b] for j in range(size))
                        == (size if a == b else 0), "character orthogonality")
                matrix_entries += 1
        lag = [z << n for z in range(d)]
        require(all(h[a][b] == 1 for a in lag for b in lag),
                "commuting Lagrangian")
        identity = uniform(size, [0])
        point = uniform(size, [1])
        all_law = uniform(size, range(size))
        nonidentity = uniform(size, range(1, size))
        lag_nonidentity = uniform(size, lag[1:])
        outside = uniform(size, [a for a in range(size) if a not in lag])
        axes = uniform(size, [(1 << j) for j in range(n)]
                       + [(1 << (n + j)) for j in range(n)])
        dense = [F(a + 1, size * (size + 1) // 2) for a in range(size)]
        laws = [point, all_law, nonidentity, lag_nonidentity, axes, dense]
        require(bias(axes, axes, h) == 1 - F(1, n),
                "near-commuting but not close-to-commuting family")
        require(bias(lag_nonidentity, outside, h) == -F(1, d - 1),
                "Lagrangian/outside cross bias")
        require(bias(outside, outside, h) == 0, "outside self bias")
        for alpha in (F(1, 100), F(1, 4), F(3, 4)):
            q = mix([(1 - alpha, lag_nonidentity), (alpha, outside)])
            require(bias(q, q, h) == (1 - alpha) ** 2
                    - 2 * alpha * (1 - alpha) / (d - 1),
                    "dimension-scaled entropy stress-family bias")
            laws.append(q)
            counter_cases += 1
        if n >= 2:
            u = 1
            support = [a for a in range(size) if not bracket(a, u, n)
                       and a not in (0, u)]
            require(len(support) == size // 2 - 2, "hyperplane support count")
            require(all(sum(h[a][b] for b in support) == -2 for a in support),
                    "hyperplane character subtraction")
            q = mix([(F(1, 4), point),
                     (F(3, 4), uniform(size, support))])
            require(q[0] == 0 and bias(q, q, h)
                    == F(7, 16) - F(9, 4 * (size - 4)),
                    "counterexample to the stronger square-root-c coefficient")
            laws.append(q)
            counter_cases += 1
        full = mix([(F(19, 50), identity),
                    (F(61, 100), uniform(size, lag)),
                    (F(1, 100), all_law)])
        expected_eta = (F(99, 100) ** 2 + 2 * F(19, 50) * F(1, 100)
                        + 2 * F(61, 100) * F(1, 100) / d
                        + F(1, 100) ** 2 / size)
        require(min(full) > 0 and bias(full, full, h) == expected_eta,
                "full-support commuting-burst plus depolarizing mixture")
        full_support_cases += 1
        laws.append(full)
        for q in laws:
            require(sum(q) == 1 and min(q) >= 0, "valid law")
            c = bias(q, q, h)
            require(-1 <= c <= 1, "bias range")
            distribution_cases += 1
            for tau in (F(0), F(1, 16), F(1, 4), F(1), F(4), F(d)):
                tail = [value if value <= tau / d else F(0) for value in q]
                w = sum(tail)
                tail_bias = bias(tail, tail, h)
                require(tail_bias <= d * sum(value * value for value in tail),
                        "finite spectral-norm bound")
                require(d * sum(value * value for value in tail) <= tau * w,
                        "threshold l2 bound")
                require(w * w - tail_bias <= 1 - c,
                        "restricted anticommutation is nonnegative submass")
                require(c <= 1 - w * w + tau * w,
                        "quadratic tail-mass certificate")
                require(max(F(0), w - tau) ** 2 <= 1 - c,
                        "positive-part tail square")
                threshold_cases += 1
            root = sqrt_upper(1 - c)
            require(root * root >= 1 - c, "rational square-root enclosure")
            root_cases += 1
            if q[0] == 0:
                for r in (F(1, 10), F(3, 5), F(1)):
                    p = mix([(1 - r, identity), (r, q)])
                    eta = bias(p, p, h)
                    require(p[0] == 1 - r and eta == 1 - r * r * (1 - c),
                            "conditional-nonidentity self-bias relation")
                    require(1 - eta == r * r * (1 - c),
                            "capacity square-root conversion")
                    conditional_cases += 1
    # An actual full-support law realizes the claimed confidence box at n32.
    n, d = 32, 1 << 32
    a, b, z = F(19, 50), F(61, 100), F(1, 100)
    p0 = a + b / d + z / (d * d)
    eta = (a + b) ** 2 + 2 * a * z + 2 * b * z / d + z * z / (d * d)
    require(a + b + z == 1 and min(a, b, z) > 0, "large-D valid full-support law")
    require(p0 >= F(19, 50) and eta >= F(24, 25), "realizable confidence box")
    require(sqrt_upper(1 - F(24, 25)) == F(1, 5), "exact confidence-box root")
    certified = conservative_certificate(n, F(19, 50), F(24, 25))
    require(certified == F(29, 10), "positive 2.9-qubit conservative certificate")
    # log2(D^2-1)>2n-1 and h2>=0 already make the p0-only Fano expression negative.
    require(n - (1 - p0) * (2 * n - 1) < 0,
            "identity-probability-only certificate cannot certify this law")
    full_support_cases += 1
    for value in (F(0), F(1, 25), F(2), F(7, 9), F(1, 10**12)):
        sqrt_upper(value)
        root_cases += 1
    return {
        "status": "passed", "character_orthogonality_entries": matrix_entries,
        "distribution_cases": distribution_cases, "threshold_cases": threshold_cases,
        "conditional_nonidentity_cases": conditional_cases,
        "rational_square_root_cases": root_cases, "stress_counterexamples": counter_cases,
        "full_support_mixtures": full_support_cases,
        "positive_example": {"n": n, "p0_lower": "19/50", "eta_lower": "24/25",
                             "certified_qubits": str(certified),
                             "p0_only_certificate_positive": False},
        "scope": ("Finite exact algebra and example guards; does not prove the general "
                  "entropy inequality or coding theorem, validate a physical noise model, "
                  "construct a decoder, or establish an ordinary-query lower bound.")
    }


if __name__ == "__main__":
    print(json.dumps(verify_entropy_capacity(), sort_keys=True))
