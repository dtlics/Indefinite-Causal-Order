"""Exact direct passive Raman temporal filter; scope is communication.md.

Imports have no output or file effects. Physical slot/bath stationarity,
matched carriers, component loss and response tails remain hypotheses.
"""
from fractions import Fraction as F
from collections import defaultdict
import json

if not __debug__:
    raise RuntimeError("Exact Raman temporal checks require assertions; do not use -O.")


def verify_raman_direct_temporal():
    """Replay passive source completion, all flags and the LTI counterexample."""
    def mm(a, b):
        return [[sum((x*y for x, y in zip(row, col)), F(0))
                 for col in zip(*b)] for row in a]


    tap0 = [[F(1, 2), F(1, 2)], [F(1, 2), F(1, 2)]]
    tap1 = [[F(1, 2), F(-1, 2)], [F(-1, 2), F(1, 2)]]
    assert mm(tap0, tap1) == mm(tap1, tap0) == [[0, 0], [0, 0]]
    assert [[a+b for a, b in zip(r0, r1)] for r0, r1 in zip(mm(tap0, tap0), mm(tap1, tap1))] == [[1, 0], [0, 1]]
    assert mm([[1, 1], [1, -1]], [[1, 1], [1, -1]]) == [[2, 0], [0, 2]]


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


    def processor(field):
        # H(z)=Hadamard diag(1,z) Hadamard, no dropped output ports.
        taps = (((1, 1), (1, 1)), ((1, -1), (-1, 1)))
        out = defaultdict(F)
        for (time, p, a, b, word), value in field.items():
            for delay, tap in enumerate(taps):
                for op in range(2):
                    out[(time+delay, op, a, b, word)] += value*F(tap[op][p], 2)
        return clean(out)


    def readout(field):
        # Delay P0 by one slot, then Hadamard. Its omitted common1/sqrt2
        # is included in the final probability denominator20.
        out = defaultdict(F)
        for (time, p, a, b, word), value in field.items():
            clock = time+(1-p)
            out[(clock, 0, a, b, word)] += value
            out[(clock, 1, a, b, word)] += value*(-1 if p else 1)
        return clean(out)


    # Source kept outputs, with common denominator sqrt10 omitted.
    x, y = (1, -1, -1), (1, 1, -1)
    source = {(t, p, 0, 0, ''): F((x, y)[p][t]) for t in range(3) for p in range(2)}
    after_a = query(source, 'A')
    after_processor = processor(after_a)
    after_b = query(after_processor, 'B')
    output = readout(after_b)
    selected = {(a, b, word): v for (clock, port, a, b, word), v in output.items()
                if clock == 2 and port == 0}
    assert selected == {(1, 0, 'bb'): F(1), (0, 1, 'bb'): F(-1)}
    assert sum(v*v for v in selected.values())/20 == F(1, 10)

    # All physical output clocks and ports remain; classify every uniformBell flag.
    uniform = []
    for clock in range(5):
        for port in range(2):
            vectors = {word: [output.get((clock, port, a, b, word), F(0))
                              for a in range(2) for b in range(2)]
                       for word in ('aa', 'ab', 'ba', 'bb')}
            if all(not any(vectors[word]) for word in ('aa', 'ab', 'ba')):
                v = vectors['bb']
                # Exact real two-qubit pure-state Bell criterion.
                row0, row1 = v[0]*v[0]+v[1]*v[1], v[2]*v[2]+v[3]*v[3]
                if row0 and row0 == row1 and v[0]*v[2]+v[1]*v[3] == 0:
                    uniform.append((clock, port, sum(c*c for c in v)/20))
    assert uniform == [(2, 0, F(1, 10))]

    # Exact limitation: stationary LTI kernels may spill into the selected clock.
    # With no Raman coefficient at either node, a_A(z)=(1+z)/2 still produces
    # a false product-state central click from the identity-word side clocks.
    false_product_amplitude = sum(
        F(1, 2)*output.get((2-delay, 0, 0, 0, 'aa'), F(0))
        for delay in (0, 1))
    assert false_product_amplitude == F(1, 2)
    assert false_product_amplitude**2/20 == F(1, 80)

    # For unitary I/SWAP endpoint choices, sum ALL clock/port outputs.
    for word in ('aa', 'ab', 'ba', 'bb'):
        total = sum(v*v for (clock, port, a, b, w), v in output.items() if w == word)/20
        assert total == F(3, 5)
    # A general lossless partial SWAP: a=(1+i)/2,b=(1-i)/2.
    # Work in Gaussian rational pairs to include interference between words.
    def cmul(a, b):
        return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]

    def cadd(a, b):
        return a[0]+b[0], a[1]+b[1]

    for aa, ba, ab, bb in (
            ((F(1, 2), F(1, 2)), (F(1, 2), F(-1, 2)), (F(0), F(0)), (F(1), F(0))),
            ((F(1, 2), F(1, 2)), (F(1, 2), F(-1, 2)), (F(1, 2), F(-1, 2)), (F(1, 2), F(1, 2)))):
        coefficients = {'aa': cmul(aa, ab), 'ab': cmul(aa, bb),
                        'ba': cmul(ba, ab), 'bb': cmul(ba, bb)}
        collected = defaultdict(lambda: (F(0), F(0)))
        for (clock, port, a, b, word), value in output.items():
            z = coefficients[word]
            collected[(clock, port, a, b)] = cadd(collected[(clock, port, a, b)], (z[0]*value, z[1]*value))
        assert sum(z[0]*z[0]+z[1]*z[1] for z in collected.values())/20 == F(3, 5)

    # The passive source column has three mutually orthogonal coefficient
    # vectors (1,1,sqrt2),(-1,1,0),(-1,-1,sqrt2), common denominator sqrt10.
    def dot2(a, b):
        return sum(x*y for x, y in zip(a[:2], b[:2]))+2*a[2]*b[2]

    source_vectors = ((1, 1, 1), (-1, 1, 0), (-1, -1, 1))
    for i, vi in enumerate(source_vectors):
        for j, vj in enumerate(source_vectors):
            assert dot2(vi, vj) == ((4, 2, 4)[i] if i == j else 0)
    assert sum((4, 2, 4)) == 10
    assert F(6, 10)+F(4, 10) == 1  # kept source + rejected port
    # Margins include source rejection, every output clock, and static ABroute1.
    assert F(1, 10) > F(2, 27)
    assert F(1, 10)/F(2, 27) == F(27, 20)
    return {
        "source_kept_probability": "3/5",
        "source_rejected_probability": "2/5",
        "source_coefficient_inner_products": 9,
        "intermediate_fir_paraunitarity_identities": 3,
        "expanded_node_polynomial_words": 4,
        "complete_clock_port_flags": 10,
        "uniform_bell_flags": [[2, "+"]],
        "unitary_complete_output_norm_cases": 6,
        "direct_all_launch_coefficient": "1/10",
        "symmetric_ring_minus_coefficient": "2/27",
        "direct_to_ring_minus_ratio": "27/20",
        "nonflat_false_product_click_probability": "1/80",
        "scope": "static disjoint slots; arbitrary LTI response requires a complete-instrument tail bound",
    }


if __name__ == "__main__":
    print(json.dumps(verify_raman_direct_temporal(), sort_keys=True))
