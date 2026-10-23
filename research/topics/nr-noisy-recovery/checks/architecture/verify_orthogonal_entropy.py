"""Exact non-Pauli guards for the orthogonal-random-unitary entropy method.

Uses Gaussian rational arithmetic only. The general entropy and coding
arguments remain analytic; no finite replay is a proof for every family.
"""
from fractions import Fraction as F
import json

if not __debug__:
    raise RuntimeError("Run orthogonal-unitary entropy guards without -O.")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


class G:
    def __init__(self, real=0, imag=0):
        self.r, self.i = F(real), F(imag)

    @staticmethod
    def of(x):
        return x if isinstance(x, G) else G(x)

    def __add__(self, x):
        x = G.of(x)
        return G(self.r + x.r, self.i + x.i)

    __radd__ = __add__

    def __neg__(self):
        return G(-self.r, -self.i)

    def __sub__(self, x):
        return self + -G.of(x)

    def __rsub__(self, x):
        return G.of(x) + -self

    def __mul__(self, x):
        x = G.of(x)
        return G(self.r * x.r - self.i * x.i,
                 self.r * x.i + self.i * x.r)

    __rmul__ = __mul__

    def __truediv__(self, scalar):
        return G(self.r / scalar, self.i / scalar)

    def __eq__(self, x):
        x = G.of(x)
        return self.r == x.r and self.i == x.i

    def conj(self):
        return G(self.r, -self.i)

    def norm2(self):
        return self.r * self.r + self.i * self.i


def eye(d):
    return [[G(int(i == j)) for j in range(d)] for i in range(d)]


def adj(a):
    return [[a[j][i].conj() for j in range(len(a))] for i in range(len(a))]


def mul(a, b):
    d = len(a)
    return [[sum((a[i][k] * b[k][j] for k in range(d)), G())
             for j in range(d)] for i in range(d)]


def trace(a):
    return sum((a[i][i] for i in range(len(a))), G())


def add(a, b, sign=1):
    return [[x + sign * y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def scale(a, scalar):
    return [[x * scalar for x in row] for row in a]


def frob2(a):
    return sum((x.norm2() for row in a for x in row), F(0))


def root_basis():
    d, units = 4, []
    phases = [G(1), G(0, 1), G(F(3, 5), F(4, 5)), G(F(5, 13), F(12, 13))]
    for a, z in enumerate(phases):
        rows = [[G(1)] * d, [G(1), z, G(-1), -z],
                [G(1), G(-1), G(1), G(-1)], [G(1), -z, G(-1), z]]
        for row in rows:
            u = [[G() for _ in range(d)] for _ in range(d)]
            for k in range(d):
                u[(k + a) % d][k] = row[k]
            units.append(u)
    return units


def commutator_table(units):
    d, table = len(units[0]), []
    for ui in units:
        row = []
        for uj in units:
            comm = mul(mul(mul(adj(uj), adj(ui)), uj), ui)
            row.append(trace(comm).r / d)
            difference = add(mul(ui, uj), mul(uj, ui), -1)
            require(frob2(difference) / (2 * d) == 1 - row[-1],
                    "nonnegative commutator-energy identity")
        table.append(row)
    return table


def choi(units, weights):
    d = len(units[0])
    vectors = [[u[a][b] for a in range(d) for b in range(d)] for u in units]
    return [[sum((w * x[k] * x[l].conj() for w, x in zip(weights, vectors)), G()) / d
             for l in range(d * d)] for k in range(d * d)]


def bias(weights, table):
    return sum((x * y * table[i][j] for i, x in enumerate(weights)
                for j, y in enumerate(weights)), F(0))


def flag_probabilities(ui, uj, state):
    """Full switch of equal iid two-unitary mixture; all four Kraus pairs."""
    plus = minus = F(0)
    for a in (ui, uj):
        for b in (ui, uj):
            ab, ba = mul(a, b), mul(b, a)
            kp, km = scale(add(ab, ba), F(1, 4)), scale(add(ab, ba, -1), F(1, 4))
            pp, pm = trace(mul(mul(kp, state), adj(kp))), trace(mul(mul(km, state), adj(km)))
            require(pp.i == pm.i == 0, "real flag probabilities")
            plus += pp.r
            minus += pm.r
    require(plus >= 0 and minus >= 0 and plus + minus == 1, "full flagged normalization")
    return plus, minus


def verify():
    base, d = root_basis(), 4
    # Common dense rational conjugation tests a nonmonomial physical basis too.
    v = [1, 2, 3, 4]
    rotation = [[G(int(i == j) - F(v[i] * v[j], 15))
                 for j in range(d)] for i in range(d)]
    require(mul(rotation, adj(rotation)) == eye(d), "dense rational frame")
    dense = [mul(mul(rotation, u), adj(rotation)) for u in base]
    require(any(sum(x != 0 for row in u for x in row) > d for u in dense),
            "nonmonomial unitary family")
    gram_cases = energy_cases = tail_cases = index_cases = target_cases = 0
    reference_table = None
    for family in (base, dense):
        require(family[0] == eye(d), "identity included")
        for i, ui in enumerate(family):
            require(mul(adj(ui), ui) == eye(d), "unitary family member")
            for j, uj in enumerate(family):
                require(trace(mul(adj(ui), uj)) == (d if i == j else 0),
                        "orthogonal unitary basis")
                gram_cases += 1
        table = commutator_table(family)
        energy_cases += len(family) ** 2
        require(any(c not in (F(-1), F(1)) for row in table for c in row),
                "commutators need not be Pauli scalar signs")
        require(all(table[i][j] == table[j][i] for i in range(16) for j in range(16)),
                "real symmetric commutator table")
        if reference_table is None:
            reference_table = table
        else:
            require(table == reference_table, "common frame preserves scalar table")
        point = [F(1)] + [F(0)] * 15
        uniform = [F(1, 16)] * 16
        pair = [F(1, 2) if i in (1, 4) else F(0) for i in range(16)]
        weighted = [F(i + 1, 136) for i in range(16)]
        full = [F(19, 50) * point[i] + F(61, 100) * F(i < 4, 4)
                + F(1, 100) * uniform[i] for i in range(16)]
        for q in (point, uniform, pair, weighted, full):
            require(sum(q) == 1 and min(q) >= 0, "valid orthogonal-unitary law")
            c = bias(q, table)
            require(-1 <= c <= 1, "helper trace statistic range")
            for tau in (F(0), F(1, 16), F(1, 4), F(1), F(4)):
                weights = [x if x <= tau / d else F(0) for x in q]
                rho = choi(family, weights)
                w, cv = sum(weights), bias(weights, table)
                rho_purity = frob2(rho)
                require(rho_purity == sum(x * x for x in weights),
                        "orthogonal mixture Choi purity")
                reshuffled = sum((rho[a * d + b][c0 * d + e]
                                  * rho[c0 * d + a][e * d + b]
                                  for a in range(d) for b in range(d)
                                  for c0 in range(d) for e in range(d)), G())
                require(d * reshuffled.r == cv, "exact bilinear Choi index formula")
                require(abs(cv) <= d * rho_purity,
                        "absolute bilinear Cauchy bound")
                require(w * w - cv <= 1 - c, "tail commutator energy is a submass")
                require(cv <= tau * w and w * w - tau * w <= 1 - c,
                        "entropy threshold inequality")
                index_cases += 1
                tail_cases += 1
        require(bias(uniform, table) == F(1, 16), "depolarizing basis mixture")
        # The same self-switch can have different helper flags on different target states.
        for k, expected_mean in ((0, F(1)), (1, F(0))):
            state = [[G(int(i == k and j == k)) for j in range(d)] for i in range(d)]
            if family is dense:
                state = mul(mul(rotation, state), adj(rotation))
            pp, pm = flag_probabilities(family[4], family[1], state)
            require(pp - pm == expected_mean, "non-Pauli input-dependent helper mean")
            target_cases += 1
        mixed = scale(eye(d), F(1, d))
        pp, pm = flag_probabilities(family[4], family[1], mixed)
        require(pp - pm == F(1, 2), "maximally-mixed helper mean")
        target_cases += 1
    return {"status": "passed", "unitary_families": 2,
            "orthogonality_cases": gram_cases, "commutator_energy_cases": energy_cases,
            "bilinear_index_cases": index_cases, "threshold_cases": tail_cases,
            "target_dependence_cases": target_cases,
            "scope": ("Exact D4 non-Pauli and dense-frame algebra/flag guards; "
                      "general entropy/coding arguments remain analytic. "
                      "No nonorthogonal-unitary, general-CPTP, native-device "
                      "or query-advantage claim.")}


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True))
