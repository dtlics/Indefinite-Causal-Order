"""Exact finite guards for cross-paired Pauli coset scalar estimation.

The all-n moment, query and resource bounds remain analytic in
architecture-baselines.md#nr-r06-pauli-coset-scalar.
"""
if not __debug__:
    raise RuntimeError("Run without -O")

from fractions import Fraction as F
import json

def bracket(a, b, n):
    mask = (1 << n) - 1
    return ((((a & mask) & (b >> n)).bit_count()
             + ((b & mask) & (a >> n)).bit_count()) & 1)


def lagrangians(n):
    spaces = {(0,)}
    for _ in range(n):
        extended = set()
        for ell in spaces:
            for v in range(1, 1 << (2*n)):
                if v not in ell and not any(bracket(v, u, n) for u in ell):
                    extended.add(tuple(sorted(ell + tuple(v ^ u for u in ell))))
        spaces = extended
    expected = 1
    for j in range(1, n+1):
        expected *= (1 << j) + 1
    assert len(spaces) == expected
    return sorted(spaces)


def char(a, b, n):
    return 1 - 2 * bracket(a, b, n)


def sublabel(a, n, start, width):
    mask = (1 << width) - 1
    return ((a >> start) & mask) | (((a >> (n + start)) & mask) << width)


def samples(p, n, r):
    m, d = n - r, 1 << (n - r)
    ls = lagrangians(m)
    out = []
    for a, pa in enumerate(p):
        if not pa:
            continue
        ar = sublabel(a, n, 0, r)
        am = sublabel(a, n, r, m)
        for ell in ls:
            v = []
            for x in range(len(p)):
                if sublabel(x, n, 0, r) != ar:
                    v.append(F(0))
                else:
                    xm = sublabel(x, n, r, m)
                    v.append(F(1) if xm ^ am in ell else -F(1, d))
            out.append((pa / len(ls), v))
    return out


def mul(a, b):
    return [[sum(x * y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def bilinear(x, h, y):
    return sum(xi * sum(hij * yj for hij, yj in zip(row, y))
               for xi, row in zip(x, h))


def moment(data):
    size = len(data[0][1])
    mean = [sum(w * v[x] for w, v in data) for x in range(size)]
    mat = [[sum(w * v[x] * v[y] for w, v in data)
            for y in range(size)] for x in range(size)]
    return mean, mat


def direct_n2(xs, ys, h):
    # Collapse the two exchangeable copies to a distribution of sample sums.
    def sums(data):
        out = {}
        for w, x in data:
            for z, y in data:
                v = tuple((a + b) / 2 for a, b in zip(x, y))
                out[v] = out.get(v, F(0)) + w * z
        return out
    left, right = sums(xs), sums(ys)
    avg = F(0)
    second = F(0)
    for x, wx in left.items():
        for y, wy in right.items():
            value = bilinear(x, h, y)
            avg += wx * wy * value
            second += wx * wy * value * value
    return avg, second - avg * avg


def check_case(n, r, p, q, direct=False):
    d, size = 1 << (n - r), 1 << (2 * n)
    assert len(p) == len(q) == size and sum(p) == sum(q) == 1
    xs, ys = samples(p, n, r), samples(q, n, r)
    mean_p, mp = moment(xs)
    mean_q, mq = moment(ys)
    assert mean_p == p and mean_q == q
    h = [[F(char(a, b, n)) for b in range(size)] for a in range(size)]
    eta = bilinear(p, h, q)
    hp = [sum(a * b for a, b in zip(row, p)) for row in h]
    hq = [sum(a * b for a, b in zip(row, q)) for row in h]
    ma = bilinear(hq, mp, hq)
    mb = bilinear(hp, mq, hp)
    hmqh = mul(mul(h, mq), h)
    m1 = sum(mp[i][j] * hmqh[j][i]
             for i in range(size) for j in range(size))
    va, vb = ma - eta * eta, mb - eta * eta
    degenerate = m1 - ma - mb + eta * eta
    assert va >= 0 and vb >= 0 and degenerate >= 0
    assert ma <= 1 + 2 * d and mb <= 1 + 2 * d
    assert m1 <= 5 * d * d and degenerate <= 5 * d * d
    for count in (1, 2, 7):
        variance = (va + vb) / count + degenerate / (count * count)
        bound = F(2 + 4 * d, count) + F(5 * d * d, count * count)
        assert variance <= bound
        if direct and count == 2:
            direct_mean, direct_variance = direct_n2(xs, ys, h)
            assert direct_mean == eta and direct_variance == variance
    return {"n": n, "references": r, "eta": str(eta),
            "first_variance_A": str(va), "first_variance_B": str(vb),
            "degenerate_variance": str(degenerate), "direct_N2": direct}


def verify_moments_and_affine():
    projected_labels = affine_pairs = entry_guards = 0
    counts = {}
    for n in (1, 2):
        d, size = 1 << n, 1 << (2*n)
        all_l = lagrangians(n)
        counts[str(n)] = len(all_l)
        _, m0 = moment(samples([F(x == 0) for x in range(size)], n, 0))
        for x in range(size):
            for y in range(size):
                if x == y == 0:
                    predicted = F(1)
                elif not x or not y:
                    predicted = F(0)
                elif x == y:
                    predicted = F(1, d)
                elif bracket(x, y, n):
                    predicted = -F(1, d*d)
                else:
                    predicted = F(1, d*(d+2))
                assert m0[x][y] == predicted
                entry_guards += 1
        t, rank = F(2*(d+1), d*(d+2)), (d*d+d-2)//2
        for a in range(size):
            _, ma = moment(samples([F(x == a) for x in range(size)], n, 0))
            assert ma == [[m0[x ^ a][y ^ a] for y in range(size)] for x in range(size)]
            pi = [[(ma[x][y]-F(x == y == a))/t for y in range(size)] for x in range(size)]
            assert mul(pi, pi) == pi
            assert all(pi[a][x] == pi[x][a] == 0 for x in range(size))
            assert sum(pi[x][x] for x in range(size)) == rank
            projected_labels += 1
        h = [[char(x, y, n) for y in range(size)] for x in range(size)]
        records = []
        for ell in all_l:
            cosets = {tuple(sorted(a ^ u for u in ell)) for a in range(size)}
            for coset in cosets:
                weighted = [d if x in coset else -1 for x in range(size)]
                transform = [sum(hxy*wy for hxy, wy in zip(row, weighted)) for row in h]
                records.append((set(ell), set(coset), weighted, transform))
        for la, ca, wa, _ in records:
            for lb, cb, _, hb in records:
                direct = F(sum(x*y for x, y in zip(wa, hb)), d*d)
                intersection, kernel = ca & lb, la & lb
                s = F(0)
                if intersection:
                    x0, b0 = min(intersection), min(cb)
                    assert intersection == {x0 ^ k for k in kernel}
                    if all(char(k, b0, n) == 1 for k in kernel):
                        s = F(len(kernel), d)*char(x0, b0, n)
                affine = (d+1)**2*s-(d+1)*(int(0 in ca)+int(0 in cb))+1
                assert direct == affine
                affine_pairs += 1
    return projected_labels, entry_guards, affine_pairs, counts


def verify_pauli_cross_pair():
    projected, entries, affine_pairs, counts = verify_moments_and_affine()
    cases = []
    for n, r in ((1, 0), (2, 0), (2, 1)):
        size = 1 << (2*n)
        uniform = [F(1, size)] * size
        point = [F(x == 1) for x in range(size)]
        skew = [F(i+1, size*(size+1)//2) for i in range(size)]
        for p, q in ((uniform, uniform), (point, skew), (skew, skew)):
            cases.append(check_case(n, r, p, q, direct=n == 1))
    # These labels correlate R and M perfectly within each error law;
    # the A/B laws themselves are still sampled independently.
    p = [F(x in (0, 3, 12, 15), 4) for x in range(16)]
    q = [F(x in (0, 6, 9, 15), 4) for x in range(16)]
    cases.append(check_case(2, 1, p, q))
    signs = 0
    for a in range(16):
        for b in range(16):
            assert char(a, b, 2) == (char(sublabel(a, 2, 0, 1), sublabel(b, 2, 0, 1), 1)
                                    * char(sublabel(a, 2, 1, 1), sublabel(b, 2, 1, 1), 1))
            signs += 1
    assert F(5, 32)+F(5, 1024) < F(1, 4)
    return {
        "status": "passed", "arithmetic": "exact rational",
        "lagrangian_counts": counts, "conditional_moment_projectors": projected,
        "zero_label_moment_entries": entries, "affine_pair_kernels": affine_pairs,
        "bilinear_variance_cases": len(cases),
        "variance_sample_counts_per_case": [1, 2, 7],
        "direct_N2_distributions": sum(x["direct_N2"] for x in cases),
        "partial_reference_signs": signs, "correlated_partial_label_case": cases[-1],
        "scope": ("Finite n=1,2 coset moments, affine kernels and exact variance checks; "
                  "all-n spectral/variance, sampling, classical cost and physical access "
                  "arguments remain analytic. No optimal ordinary frontier or SPAM claim.")
    }


if __name__ == "__main__":
    print(json.dumps(verify_pauli_cross_pair(), sort_keys=True))

