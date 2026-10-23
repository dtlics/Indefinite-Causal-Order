"""Outward rational intervals for one heat-regularized GKP tail screen.

Replays the raw Mehler Gram, all-input moment and frozen tail inequalities
in methods/heat-gkp-certification.md. No floating arithmetic, quadrature, recovery
SDP, hardware claim or static record is used. Parameters are fixed.
"""
if not __debug__:
    raise RuntimeError("The certificate requires assertions; omit -O")

from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from math import isqrt
import json

BITS = 192
DEN = 1 << BITS


def down(x):
    return F((x * DEN).numerator // (x * DEN).denominator, DEN)


def up(x):
    return -down(-x)


class I:
    def __init__(self, lo, hi=None):
        lo, hi = F(lo), F(lo if hi is None else hi)
        assert lo <= hi
        self.lo, self.hi = down(lo), up(hi)

    def __add__(self, other):
        other = interval(other)
        return I(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -interval(other)

    def __rsub__(self, other):
        return interval(other) + -self

    def __mul__(self, other):
        other = interval(other)
        ends = [x * y for x in (self.lo, self.hi) for y in (other.lo, other.hi)]
        return I(min(ends), max(ends))

    __rmul__ = __mul__

    def reciprocal(self):
        assert self.lo > 0 or self.hi < 0
        return I(1 / self.hi, 1 / self.lo)

    def __truediv__(self, other):
        return self * interval(other).reciprocal()

    def __rtruediv__(self, other):
        return interval(other) * self.reciprocal()

    def sqrt(self):
        assert self.lo >= 0
        a, b = self.lo * DEN * DEN, self.hi * DEN * DEN
        assert a.denominator == b.denominator == 1
        low, high = isqrt(a.numerator), isqrt(b.numerator)
        return I(F(low, DEN), F(high + 1, DEN))

    def exp(self):
        return I(exp_point(self.lo).lo, exp_point(self.hi).hi)


def interval(x):
    return x if isinstance(x, I) else I(x)


@lru_cache(None)
def exp_point(q):
    q = F(q)
    if q > 0:
        return exp_point(-q).reciprocal()
    if q == 0:
        return I(1)
    reductions = 0
    while -q / (1 << reductions) > F(1, 32):
        reductions += 1
    t = I(-q / (1 << reductions))
    term, total = I(1), I(1)
    for k in range(1, 25):
        term = term * t / k
        total = total + (term if k % 2 == 0 else -term)
    # An even alternating partial sum is above exp(-t); the next
    # positive term bounds its excess. Interval rounding is retained.
    next_term = term * t / 25
    answer = I(max(F(0), total.lo - next_term.hi), min(F(1), total.hi))
    for _ in range(reductions):
        answer = answer * answer
    return answer


def atan_inverse(base, terms=80):
    total = sum((F((-1) ** k, (2 * k + 1) * base ** (2 * k + 1))
                 for k in range(terms)), F(0))
    next_term = F((-1) ** terms, (2 * terms + 1) * base ** (2 * terms + 1))
    return I(min(total, total + next_term), max(total, total + next_term))


PI = 16 * atan_inverse(5) - 4 * atan_inverse(239)
assert F(3) < PI.lo < PI.hi < F(22, 7)


def gaussian_tail(c, cutoff):
    c = I(c)
    assert c.lo > 0
    return 2 * (-c * (cutoff + 1) ** 2).exp() / (
        1 - (-c * (2 * cutoff + 3)).exp())


@lru_cache(None)
def gram(delta, cutoff=20):
    delta = F(delta)
    assert delta > 0
    e2 = I(2 * delta).exp()
    tanh = (e2 - 1) / (e2 + 1)
    coth = 1 / tanh
    sinh2 = (e2 - 1 / e2) / 2
    prefactor = I(delta).exp() / (2 * PI * sinh2).sqrt()
    c = (PI * tanh / 2).lo
    full_sum_bound = 1 + (PI / c).sqrt()
    missing = (2 * prefactor * full_sum_bound * gaussian_tail(c, cutoff)).hi
    cache = {}
    out = {}
    for left, right in ((0, 0), (0, 1), (1, 1)):
        counts = Counter(((k + l) ** 2, (k - l) ** 2)
                         for k in range(-cutoff, cutoff + 1) if k % 2 == left
                         for l in range(-cutoff, cutoff + 1) if l % 2 == right)
        value = I(0)
        for (m2, n2), count in counts.items():
            key = (m2, n2)
            if key not in cache:
                cache[key] = (-PI * (m2 * tanh + n2 * coth) / 4).exp()
            value += count * cache[key]
        out[left, right] = prefactor * value + I(0, missing)
    return out, missing


def positive_2x2(a, b, d):
    if min(a.lo, d.lo) < 0:
        return False
    return a.lo * d.lo - max(abs(b.lo), abs(b.hi)) ** 2 >= 0


def moment_bound(delta, exponent):
    delta, exponent = F(delta), F(exponent)
    assert 0 < exponent < 2 * delta
    g, _ = gram(delta)
    h, _ = gram(delta - exponent / 2)
    assert positive_2x2(g[0, 0], g[0, 1], g[1, 1])

    def sufficient(c):
        return positive_2x2(c * g[0, 0] - h[0, 0],
                            c * g[0, 1] - h[0, 1],
                            c * g[1, 1] - h[1, 1])

    low, high = F(1), F(2)
    while not sufficient(high):
        high *= 2
    for _ in range(80):
        middle = (low + high) / 2
        if sufficient(middle):
            high = middle
        else:
            low = middle
    assert sufficient(high)
    return high


def verify():
    delta, exponent = F(1, 4), F(1, 4)
    g, lattice_error = gram(delta)
    h, shifted_lattice_error = gram(delta - exponent / 2)
    moment = moment_bound(delta, exponent)
    small = F(1, 1024)
    energy_moment = moment_bound(delta, small)
    energy = (energy_moment - 1) / (I(small).exp().lo - 1)
    # Gershgorin gives an elementary strictly positive conditioning guard.
    minimum = min(g[0, 0].lo, g[1, 1].lo) - max(abs(g[0, 1].lo), abs(g[0, 1].hi))
    assert minimum > F(3, 5)
    exp_quarter = I(exponent).exp()
    assert F(11, 9) < exp_quarter.lo and F(23, 19) < exp_quarter.lo
    source_tail = (I(-exponent * 129).exp() * moment).hi
    # Output bounds also cover the exact polar-normalized Fock128
    # prefix source: its moment is at most moment/(1-source_tail).
    prefix_moment = moment / (1 - source_tail)
    switch_tail = F(5, 6) ** 129 * F(10, 9) * prefix_moment
    aligned_final_tail = F(5, 6) ** 129 * F(20, 19) * prefix_moment
    # Weighted Hilbert--Schmidt squeezing bound, g=1/2, kappa=4.
    em = I(-exponent).exp()
    nu = (1 + em) / (2 * (1 - em))
    z_pre, u_pre = F(21, 20), F(1, 21)
    a = 1 - u_pre * (4 * nu + F(1, 2))
    b = 1 - u_pre * (nu / 4 + F(1, 2))
    assert min(a.lo, b.lo) > 0
    hs = (1 / ((1 - em) * z_pre * (a * b).sqrt())).hi
    pre_tail = F(20, 21) ** 513 * hs * prefix_moment
    # Total pre-undo aligned noise is one-axis variance a+b=1.
    assert F(40, 39) < z_pre
    aligned_intermediate_tail = F(40, 41) ** 1025 * F(40, 39) * hs * prefix_moment
    assert source_tail < F(1, 10 ** 12)
    assert switch_tail < F(1, 10 ** 9)
    assert aligned_final_tail < F(1, 10 ** 9)
    assert pre_tail < F(1, 10 ** 8)
    assert aligned_intermediate_tail < F(1, 10 ** 8)
    prefix_energy = energy / (1 - source_tail)
    common_peak = 4 * (prefix_energy + F(1, 2))
    cutoff_error = (I(source_tail).sqrt() + I(switch_tail).sqrt() + switch_tail / 2).hi
    ceilings = {"moment": F(2), "mean_energy": F(234, 100),
                "source_p": F(2, 10 ** 14), "switch_output_p": F(136, 10 ** 12),
                "pre_squeeze_p": F(263, 10 ** 12),
                "aligned_intermediate_p": F(204, 10 ** 12),
                "aligned_final_p": F(129, 10 ** 12), "common_peak": F(11358, 1000),
                "source_plus_output_trace_distance": F(12, 10 ** 6)}
    values = (moment, energy, source_tail, switch_tail, pre_tail,
              aligned_intermediate_tail, aligned_final_tail, common_peak, cutoff_error)
    assert all(value < ceiling for value, ceiling in zip(values, ceilings.values()))
    assert prefix_moment < F(2)
    assert prefix_energy < F(117, 50)
    assert hs < F(1218, 125)
    assert prefix_energy + F(1, 2) < F(71, 25)
    ceilings.update({"prefix_moment": F(2), "prefix_mean_energy": F(117, 50),
                     "squeeze_hilbert_schmidt_constant": F(1218, 125),
                     "declared_switch_oscillator_peak": F(71, 25)})
    return {
        "status": "passed",
        "parameters": {"dyadic_bits": BITS, "mehler_box": 20,
                       "delta": "1/4", "input_exponent": "1/4",
                       "energy_exponent": "1/1024", "source_cutoff": 128,
                       "output_cutoff": 128, "pre_squeeze_cutoff": 512,
                       "pre_undo_cutoff": 1024, "squeeze_g": "1/2",
                       "noise_a": "1/2", "noise_b": "1/2",
                       "output_z": "6/5", "pre_squeeze_z": "21/20",
                       "pre_undo_z": "41/40",
                       "switch_moment_prefactor": "10/9",
                       "aligned_final_moment_prefactor": "20/19",
                       "pre_undo_moment_prefactor": "40/39"},
        "gram_eigenvalue_strict_lower": "3/5",
        "strict_upper_bounds": {key: str(value) for key, value in ceilings.items()},
        "prefix_source": "Exact polar-normalized Fock128 prefix of the full-Gram-normalized "
                         "heat code. Source probability bounds the original heat input; all "
                         "reported output tails also cover the prefix via moment/(1-source_p). "
                         "Source-isometry trace distance is at most sqrt(source_p).",
        "scope": "Fixed-parameter rational interval certificate, uniform over logical inputs "
                 "and references. Common peak is a directly certified ensemble-mean "
                 "admissibility cap for two fixed circuits, without equal realized peaks "
                 "or encoder optimization; "
                 "combined trace distance includes source and final overflow errors. "
                 "No quadrature, finite recovery SDP, device implementation, equal-resource "
                 "optimum or ordinary-dominance claim is certified."}


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2, sort_keys=True))
