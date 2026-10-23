"""Exact coefficient/norm checks for the Raman finite-response guard.

Imports have no output or file effects. Uniform node/kernel/dilation
certificates, Markov decay, composition and clock costs remain analytic
conditional inputs; no fitted-linewidth or measured-device bound is inferred.
"""
from collections import defaultdict
from fractions import Fraction as F
from math import isqrt
import json

if not __debug__:
    raise RuntimeError("Exact Raman tail checks require assertions; do not use -O.")


def verify_raman_temporal_tail():
    """Rebuild all side-clock coefficients and exact norm/margin arithmetic."""
    def clean(d):
        return {k: v for k, v in d.items() if v}

    def query(field, spin):
        out = defaultdict(F)
        for (time, p, a, b, word), value in field.items():
            out[(time, p, a, b, word+'a')] += value
            if spin == 'A':
                out[(time, a, p, b, word+'b')] += value
            else:
                out[(time, b, a, p, word+'b')] += value
        return clean(out)

    x, y = (1, -1, -1), (1, 1, -1)
    source = {(t, p, 0, 0, ''): F((x, y)[p][t])
              for t in range(3) for p in range(2)}
    after_a = query(source, 'A')
    intermediate = defaultdict(F)
    taps = (((1, 1), (1, 1)), ((1, -1), (-1, 1)))
    for (time, p, a, b, word), value in after_a.items():
        for delay, tap in enumerate(taps):
            for op in range(2):
                intermediate[(time+delay, op, a, b, word)] += value*F(tap[op][p], 2)
    after_b = query(clean(intermediate), 'B')
    output = defaultdict(F)
    for (time, p, a, b, word), value in after_b.items():
        # Plus readout; common source/readout factor 1/sqrt(20) omitted.
        output[(time+1-p, a, b, word)] += value
    output = clean(output)

    expected = {
        'aa': {0: F(1), 1: F(1), 3: F(4)},
        'ba': {0: F(1, 2), 1: F(1, 2), 3: F(1, 2), 4: F(1, 2)},
        'ab': {1: F(2), 3: F(4)},
        'bb': {1: F(1), 2: F(2), 3: F(2), 4: F(1)},
    }
    for word in expected:
        actual = {k: sum(output.get((k, a, b, word), F(0))**2
                         for a in range(2) for b in range(2))
                  for k in range(5)}
        assert {k: v for k, v in actual.items() if v} == expected[word]
    assert {k: v for k, v in output.items() if k[0] == 2} == {
        (2, 1, 0, 'bb'): F(1), (2, 0, 1, 'bb'): F(-1)}

    # Exact side-clock norm sums in Q(sqrt(2)); pair (a,b) means a+b sqrt(2).
    roots = {F(1): (F(1), F(0)), F(4): (F(2), F(0)),
             F(1, 2): (F(0), F(1, 2)), F(2): (F(0), F(1))}
    radical_sums = {}
    for word, clocks in expected.items():
        a = b = F(0)
        for k, norm2 in clocks.items():
            if k != 2:
                ra, rb = roots[norm2]
                assert ra*rb == 0 and ra*ra+2*rb*rb == norm2
                a += ra
                b += rb
        radical_sums[word] = (a, b)
    assert radical_sums == {'aa': (4, 0), 'ba': (0, 2),
                            'ab': (2, 1), 'bb': (2, 1)}
    assert sum(a for a, b in radical_sums.values()) == 8
    assert sum(b for a, b in radical_sums.values()) == 4
    # (8+4sqrt2)/sqrt20=(4+2sqrt2)/sqrt5; all terms are positive.
    assert (F(8, 2), F(4, 2)) == (4, 2)

    # An exact passive identity-only LTI response creates a false central flag.
    aa = {k: output.get((k, 0, 0, 'aa'), F(0)) for k in range(5)}
    assert {k: v for k, v in aa.items() if v} == {0: 1, 1: 1, 3: -2}
    false_amplitude = (aa[2]+aa[1])/2  # a_A(z)=(1+z)/2, a_B=1
    assert false_amplitude == F(1, 2)
    assert false_amplitude**2/20 == F(1, 80)
    assert F(1, 10)-F(2, 27) == F(7, 270)

    def sqrt_interval(value, denominator=10**12):
        assert value >= 0
        numerator = isqrt(value.numerator*denominator**2//value.denominator)
        lower, upper = F(numerator, denominator), F(numerator+1, denominator)
        assert lower*lower <= value < upper*upper
        return lower, upper

    r2lo, r2hi = sqrt_interval(F(2))
    r5lo, r5hi = sqrt_interval(F(5))
    cdlo, cdhi = (4+2*r2lo)/r5hi, (4+2*r2hi)/r5lo
    assert F(30537654, 10**7) < cdlo < cdhi < F(30537655, 10**7)
    rdlo, rdhi = sqrt_interval(F(1, 10))
    rslo, rshi = sqrt_interval(F(2, 27))
    marginlo, marginhi = rdlo-rshi, rdhi-rslo
    assert F(4406223, 10**8) < marginlo < marginhi < F(4406225, 10**8)

    # Complex accepted geometry: ideal vector (a,0), actual (x+iu,y+iv).
    # e^2 p-a^2 bad=(p-a x)^2+a^2 u^2, so bad/p<=e^2/a^2.
    geometry_cases = 0
    grid = [F(k, 10) for k in range(-2, 3)]
    for a in (F(1, 7), F(1, 3), F(1, 2)):
        for x in grid:
            for u in grid:
                for y in grid:
                    for v in (F(-1, 10), F(0), F(1, 10)):
                        bad = y*y+v*v
                        p = x*x+u*u+bad
                        e2 = (x-a)**2+u*u+bad
                        assert e2*p-a*a*bad == (p-a*x)**2+a*a*u*u
                        assert bad <= e2
                        geometry_cases += 1

    # Equal zero accepted maps do not constrain retained failure spin states.
    rejected_identity, rejected_x = (F(1), F(0)), (F(0), F(1))
    assert sum(x*y for x, y in zip(rejected_identity, rejected_x)) == 0
    return {
        'coefficient_squared_norms': {
            word: {str(k): str(n) for k, n in clocks.items()}
            for word, clocks in expected.items()},
        'direct_tail_constant': '(4+2 sqrt(2))/sqrt(5)',
        'direct_tail_constant_rational_enclosure': ['30537654/10000000', '30537655/10000000'],
        'accepted_amplitude_margin': '1/sqrt(10)-sqrt(2/27)',
        'amplitude_margin_rational_enclosure': ['4406223/100000000', '4406225/100000000'],
        'complete_all_launch_yield_margin': '7/270 times B_I',
        'identity_only_LTI_false_herald': '1/80',
        'complex_rational_geometry_cases': geometry_cases,
        'scope': ('Exact finite polynomial/norm arithmetic; common-frame stationary accepted kernels, '
                  'uniform complete-node tail bounds, Markov decay and full failure-output '
                  'dilation certificates are analytic conditional inputs, not device measurements.'),
    }


if __name__ == '__main__':
    print(json.dumps(verify_raman_temporal_tail(), sort_keys=True))
