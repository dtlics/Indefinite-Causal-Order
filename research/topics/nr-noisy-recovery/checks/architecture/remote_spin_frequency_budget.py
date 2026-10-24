"""Exact scalar RS44 common-frequency CZ budget; standard library only.

The analytic RS31/Sturm proof is in methods/remote-spin-phase.md.
This replay does not certify a hardware model or coherent spectral readout.
"""
from fractions import Fraction as F
from math import comb


def trim(a):
    a = list(a)
    while len(a) > 1 and not a[-1]:
        a.pop()
    return a


def add(a, b):
    out = [F(0)] * max(len(a), len(b))
    for i, v in enumerate(a):
        out[i] += v
    for i, v in enumerate(b):
        out[i] += v
    return trim(out)


def scale(a, c):
    return trim([c * v for v in a])


def mul(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            out[i + j] += u * v
    return trim(out)


def evaluate(a, x):
    out = F(0)
    for v in reversed(a):
        out = out * x + v
    return out


def shift(a, c):
    out = [F(0)] * len(a)
    for n, v in enumerate(a):
        for j in range(n + 1):
            out[j] += v * comb(n, j) * c ** (n - j)
    return trim(out)


def remainder(a, b):
    a = trim(a)
    b = trim(b)
    if b == [0]:
        raise ValueError("zero polynomial divisor")
    while a != [0] and len(a) >= len(b):
        d = len(a) - len(b)
        c = a[-1] / b[-1]
        for j, v in enumerate(b):
            a[j + d] -= c * v
        a = trim(a)
    return a


def sign(x):
    return (x > 0) - (x < 0)


def variations(seq):
    seq = [v for v in seq if v]
    return sum(a != b for a, b in zip(seq, seq[1:]))


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def zadd(a, b):
    return a[0] + b[0], a[1] + b[1]


def zmul(a, b):
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def zdiv(a, b):
    d = b[0] * b[0] + b[1] * b[1]
    return ((a[0] * b[0] + a[1] * b[1]) / d,
            (a[1] * b[0] - a[0] * b[1]) / d)


def response(nu, rates, bright):
    g, k, kr, gamma = rates
    denominator = zadd(zmul((k, -nu), (gamma, -nu)),
                       (bright * g * g, F(0)))
    reflected = zdiv((2 * kr * gamma, -2 * kr * nu), denominator)
    return 1 - reflected[0], -reflected[1]


def verify(expected_rates=None):
    rates = ((F(38, 5), F(5, 2), F(23, 10), F(3)),
             (F(38, 5), F(14, 5), F(12, 5), F(3)))
    if expected_rates is not None:
        require(tuple(map(tuple, expected_rates)) == rates, "shared RS44 parameters")
    upper = F(3649, 10000)
    cutoff = F(181, 2500)
    nums, dens = [], []
    formula_cases = 0
    dd_num, dd_den = [F(1)], [F(1)]
    for g, k, kr, gamma in rates:
        n = scale([(k - 2 * kr) ** 2, F(1)], 4 * kr ** 2 * g ** 4)
        modulus = add(mul([k * gamma + g * g, F(-1)],
                          [k * gamma + g * g, F(-1)]),
                      [F(0), (k + gamma) ** 2])
        d = mul(mul([k * k, F(1)], [k * k, F(1)]), modulus)
        nums.append(n)
        dens.append(d)
        require(len(n) == 2 and len(d) == 5 and n[-1] > 0 and d[-1] > 0,
                "squared contrast high-frequency degree/sign changed")
        for nu in (F(0), F(1, 2), F(-1, 2), F(3), F(7), F(15)):
            dark = response(nu, (g, k, kr, gamma), 0)
            bright = response(nu, (g, k, kr, gamma), 1)
            contrast = (bright[0] - dark[0], bright[1] - dark[1])
            product = zmul(dark, contrast)
            require(product[0] ** 2 + product[1] ** 2 ==
                    evaluate(n, nu * nu) / evaluate(d, nu * nu),
                    "complex source response/squared contrast transcription")
            formula_cases += 1
        require(k * k > (k - 2 * kr) ** 2 > 0,
                "dark response is not monotonically increasing in frequency squared")
        dd_num = mul(dd_num, [(k - 2 * kr) ** 2, F(1)])
        dd_den = mul(dd_den, [k * k, F(1)])
    dark_at_cut = evaluate(dd_num, cutoff) / evaluate(dd_den, cutoff)
    require(dark_at_cut == F(57044143, 156329243), "dark cutoff transcription")
    require(dark_at_cut < upper, "low-frequency budget fails")
    p = add(scale(mul(dens[0], dens[1]), 16 * upper * upper),
            scale(mul(nums[0], nums[1]), F(-1)))
    p = shift(p, cutoff)
    require(p[0] > 0 and len(p) == 9, "shifted polynomial endpoint/degree")
    chain = [p, [F(i) * p[i] for i in range(1, len(p))]]
    while chain[-1] != [0]:
        nxt = scale(remainder(chain[-2], chain[-1]), F(-1))
        if nxt == [0]:
            break
        chain.append(nxt)
    at_zero = [sign(q[0]) for q in chain]
    at_infinity = [sign(q[-1]) for q in chain]
    expected = [1, 1, -1, -1, -1, 1, 1, 1, 1]
    require([len(q) - 1 for q in chain] == list(range(8, -1, -1)),
            "Sturm chain degrees changed")
    require(at_zero == at_infinity == expected, "Sturm endpoint signs changed")
    require(variations(at_zero) - variations(at_infinity) == 0,
            "positive root not excluded")
    return {"status": "passed", "arithmetic": "standard-library exact rational",
            "upper": str(upper), "frequency_squared_split": str(cutoff),
            "dark_at_split": str(dark_at_cut), "polynomial_degree": len(p) - 1,
            "exact_complex_response_formula_cases": formula_cases,
            "sturm_polynomials": len(chain), "signs_at_zero_and_infinity": expected,
            "positive_root_count": 0,
            "scope": "RS44 scalar monochromatic source rates, every common detuning; "
                     "dark-dark and RS31 average-concurrence bounds; no coherent spectral erasure, "
                     "route-controlled spin interventions, complete-loss instrument or hardware rate"}


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), sort_keys=True))
