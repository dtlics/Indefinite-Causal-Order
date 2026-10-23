"""Exact finite replay for the public-tableau burst calibration proof."""
if not __debug__:
    raise RuntimeError("Assertions must be enabled.")


def verify():
    from fractions import Fraction as F
    from itertools import product

    n, size = 2, 16

    def split(a):
        return a & 3, a >> 2

    def chi(a, b):
        x, z = split(a)
        y, w = split(b)
        return (-1) ** (((x & w).bit_count() + (z & y).bit_count()) % 2)

    def action(a, t):
        x, z = split(a)
        return t ^ x, ((x & z).bit_count() + 2 * (z & t).bit_count()) % 4

    def tableau(a):
        x, z = split(a)
        # H on site0 followed by CNOT0->1.
        x, z = (x & 2) | (z & 1), (z & 2) | (x & 1)
        x ^= (x & 1) << 1
        z ^= (z & 2) >> 1
        return x | (z << 2)

    symplectic = 0
    for a in range(size):
        for b in range(size):
            assert chi(a, b) == chi(tableau(a), tableau(b))
            symplectic += 1

    pcs_basis = 0
    for r in range(size):
        for a in range(size):
            k = int(chi(r, a) == -1)
            for c in range(2):
                for t in range(4):
                    t1, e1 = action(r, t) if c else (t, 0)
                    t2, e2 = action(a, t1)
                    t3, e3 = action(r, t2) if c else (t2, 0)
                    direct = (t3, (e1 + e2 + e3) % 4)
                    ta, ea = action(a, t)
                    assert direct == (ta, (ea + 2 * k * c) % 4)
                    pcs_basis += 1

    local = [(F(3, 5), F(1, 5), F(1, 10), F(1, 10)),
             (F(1, 2), F(1, 4), F(1, 8), F(1, 8))]
    alpha, beta = F(1, 3), F(2, 3)
    # Local label order I,X,Z,Y agrees with the binary convention.
    rlaw = [F(0)] * size
    plaw = [F(0)] * size
    for a in range(size):
        x, z = split(a)
        rlaw[a] = product_probability = F(1)
        for i in range(n):
            product_probability *= local[i][((x >> i) & 1) | (((z >> i) & 1) << 1)]
        rlaw[a] = product_probability
        plaw[tableau(a)] += beta * product_probability
    plaw[0] += alpha
    assert sum(plaw) == sum(rlaw) == 1

    def eigen(law, q):
        return sum(p * chi(a, q) for a, p in enumerate(law))

    def local_eigen(i, axis):
        x, z = axis & 1, axis >> 1
        q = (x << i) | ((z << i) << n)
        return sum(rlaw[a] * chi(a, q) for a in range(size))

    probes = 0
    for q in range(size):
        x, z = split(q)
        f = F(1)
        for i in range(n):
            axis = ((x >> i) & 1) | (((z >> i) & 1) << 1)
            f *= local_eigen(i, axis)
        assert eigen(plaw, tableau(q)) == alpha + beta * f
        probes += 1

    u, v = local_eigen(0, 1), local_eigen(1, 1)
    x, y, z = alpha + beta * u, alpha + beta * v, alpha + beta * u * v
    d = 1 - x - y + z
    assert d == beta * (1 - u) * (1 - v) > 0
    assert (z - x * y) / d == alpha

    def eta_from_local(laws, a):
        hprod = F(1)
        for law in laws:
            hprod *= 1 - 4 * (law[1] * law[2] + law[1] * law[3] + law[2] * law[3])
        return 1 - (1 - a) ** 2 + (1 - a) ** 2 * hprod

    eta_direct = sum(pa * pb * chi(a, b)
                     for a, pa in enumerate(plaw) for b, pb in enumerate(plaw))
    assert eta_direct == eta_from_local(local, alpha)
    assert plaw[0] == alpha + beta * local[0][0] * local[1][0]

    # Every corner of the three-mean error cube, followed by every corner
    # of the six local-mean cube, is checked with exact rational arithmetic.
    beta_min, d_min = beta, d
    delta = d_min / 1000
    A = 14 * delta / d_min
    L = 2 * (delta + 2 * A) / beta_min
    f_local = [[alpha + beta * local_eigen(i, axis) for axis in (1, 2, 3)]
               for i in range(n)]
    corners = 0
    for sx, sy, sz in product((-1, 1), repeat=3):
        hx, hy, hz = x + sx * delta, y + sy * delta, z + sz * delta
        hd = 1 - hx - hy + hz
        assert hd >= d_min / 2
        ha = min(max((hz - hx * hy) / hd, 0), 1 - beta_min / 2)
        assert abs(ha - alpha) <= A
        for signs in product((-1, 1), repeat=6):
            recovered = []
            for i in range(n):
                ls = [(f_local[i][j] + signs[3 * i + j] * delta - ha) / (1 - ha)
                      for j in range(3)]
                assert all(abs(ls[j] - local_eigen(i, j + 1)) <= L for j in range(3))
                lx, lz, ly = ls
                raw = [(1 + lx + ly + lz) / 4,
                       (1 + lx - ly - lz) / 4,
                       (1 - lx - ly + lz) / 4,
                       (1 - lx + ly - lz) / 4]
                clipped = [max(v, 0) for v in raw]
                repaired = [v / sum(clipped) for v in clipped]
                assert sum(abs(a - b) for a, b in zip(raw, local[i])) <= 3 * L
                assert sum(abs(a - b) for a, b in zip(repaired, local[i])) <= 6 * L
                recovered.append(repaired)
            he = eta_from_local(recovered, ha)
            hp0 = ha + (1 - ha) * recovered[0][0] * recovered[1][0]
            assert abs(he - eta_direct) <= 12 * n * L + 4 * A
            assert abs(hp0 - plaw[0]) <= 6 * n * L + 2 * A
            corners += 1
    return {"status": "passed",
            "symplectic_pairs": symplectic, "pcs_basis_vectors": pcs_basis,
            "all_logical_probes": probes, "rational_sensitivity_corners": corners}


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), sort_keys=True))
