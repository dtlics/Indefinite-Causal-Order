"""Exact conditional-expectation self-switch and gauge-channel identities.

Rationally weighted Kraus operators avoid square-root approximation. The
general algebra, Haar moment and Schmidt-number arguments remain analytic.
"""
from fractions import Fraction as F
import json

if not __debug__:
    raise RuntimeError("Exact memory-algebra checks require assertions.")


def zeros(d):
    return [[F(0) for _ in range(d)] for _ in range(d)]


def add(*arrays):
    return [[sum(items, F(0)) for items in zip(*rows)]
            for rows in zip(*arrays)]


def scale(a, value):
    return [[value*x for x in row] for row in a]


def transpose(a):
    return list(map(list, zip(*a)))


def mul(a, b):
    d, out = len(a), zeros(len(a))
    for x in range(d):
        for k in range(d):
            if a[x][k]:
                for y in range(d):
                    out[x][y] += a[x][k]*b[k][y]
    return out


def operators(sectors):
    d = sum(g*l for g, l in sectors)
    result, labels, start = [], [], 0
    for label, (g, l) in enumerate(sectors):
        labels.extend([(label, g, i, a) for i in range(g) for a in range(l)])
        for i in range(g):
            for j in range(g):
                k = zeros(d)
                for a in range(l):
                    k[start+i*l+a][start+j*l+a] = F(1)
                result.append((F(1, g), k))
        start += g*l
    return d, result, labels


def channel(terms, data):
    out = zeros(len(data))
    for weight, k in terms:
        out = add(out, scale(mul(mul(k, data), transpose(k)), weight))
    return out


def cross_and_flags(terms, data):
    d = len(data)
    cross, plus, minus = zeros(d), zeros(d), zeros(d)
    for wa, a in terms:
        for wb, b in terms:
            ba, ab = mul(b, a), mul(a, b)
            cross = add(cross, scale(mul(mul(ba, data), transpose(ab)), wa*wb))
            for sign in (1, -1):
                k = scale(add(ba, scale(ab, sign)), F(1, 2))
                mapped = scale(mul(mul(k, data), transpose(k)), wa*wb)
                if sign == 1:
                    plus = add(plus, mapped)
                else:
                    minus = add(minus, mapped)
    return cross, plus, minus


def verify_memory_algebra():
    units = haar_units = flag_blocks = 0
    for sectors in (((2, 1),), ((3, 1),), ((2, 2),),
                    ((1, 2), (2, 1)), ((2, 2), (1, 1))):
        d, terms, labels = operators(sectors)
        effect = zeros(d)
        for weight, k in terms:
            effect = add(effect, scale(mul(transpose(k), k), weight))
        assert effect == [[F(i == j) for j in range(d)] for i in range(d)]
        eta = F(0)
        for x in range(d):
            for y in range(d):
                data = zeros(d)
                data[x][y] = F(1)
                direct, plus, minus = cross_and_flags(terms, data)
                expected = zeros(d)
                if labels[x][0] == labels[y][0]:
                    expected[x][y] = F(1, labels[x][1]**2)
                assert direct == expected
                ordinary = channel(terms, data)
                assert channel(terms, ordinary) == ordinary
                assert plus == scale(add(ordinary, expected), F(1, 2))
                assert minus == scale(add(ordinary, scale(expected, -1)), F(1, 2))
                assert add(plus, minus) == ordinary
                if x == y:
                    eta += sum((direct[i][i] for i in range(d)), F(0))/d
                units += 1
                flag_blocks += 2
        assert eta == sum((F(l, g*d) for g, l in sectors), F(0))

    # Independently contract the exact complex Haar second moment, then
    # compare the two measure-and-prepare expressions on all matrix units.
    for g in (2, 3, 4):
        for x in range(g):
            for y in range(g):
                data, dep = zeros(g), zeros(g)
                data[x][y] = F(1)
                if x == y:
                    for i in range(g):
                        dep[i][i] = F(1, g)
                moment = [[F((i == j and x == y)+(i == x and j == y), g*(g+1))
                           for j in range(g)] for i in range(g)]
                haar_same = scale(moment, g)
                assert haar_same == scale(add(data, scale(dep, g)), F(1, g+1))
                haar_complement = scale(add(dep, scale(moment, -1)), F(g, g-1))
                phi_minus = scale(add(scale(dep, g*g), scale(data, -1)), F(1, g*g-1))
                assert haar_complement == phi_minus
                mixture = add(scale(haar_same, F(g+1, g*g+1)),
                              scale(dep, 1-F(g+1, g*g+1)))
                phi_plus = scale(add(scale(dep, g*g), data), F(1, g*g+1))
                assert mixture == phi_plus
                haar_units += 1
    return {
        "status": "passed", "arithmetic": "exact weighted rational matrices",
        "sector_families": 5, "reference_complete_matrix_units": units,
        "complete_flag_matrix_blocks": flag_blocks,
        "haar_moment_measure_prepare_units": haar_units,
        "scope": ("Finite cross/flag and Haar-coefficient identities. The universal "
                  "conditional-expectation, entanglement-breaking and Schmidt-number "
                  "proofs and physical independent-slot/access assumptions remain analytic; "
                  "no ordinary optimality or native advantage claim.")
    }


if __name__ == '__main__':
    print(json.dumps(verify_memory_algebra(), indent=2))
