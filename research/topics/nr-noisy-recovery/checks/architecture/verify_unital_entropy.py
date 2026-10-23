"""Exact finite guards for the general Kraus entropy/capacity certificate.

Gaussian rational arithmetic only. The general entropy and coding proofs
remain analytic; this does not infer them from finite numerical spectra.
"""

from fractions import Fraction as F
import json

if not __debug__:
    raise RuntimeError("Run the Kraus entropy guards without -O.")


def require(test, message):
    if not test:
        raise RuntimeError(message)


class C:
    def __init__(self, real=0, imag=0):
        self.r, self.i = F(real), F(imag)

    @staticmethod
    def of(x):
        return x if isinstance(x, C) else C(x)

    def __add__(self, x):
        x = C.of(x)
        return C(self.r + x.r, self.i + x.i)

    __radd__ = __add__

    def __neg__(self):
        return C(-self.r, -self.i)

    def __sub__(self, x):
        return self + -C.of(x)

    def __rsub__(self, x):
        return C.of(x) + -self

    def __mul__(self, x):
        x = C.of(x)
        return C(self.r * x.r - self.i * x.i,
                 self.r * x.i + self.i * x.r)

    __rmul__ = __mul__

    def __truediv__(self, x):
        x = C.of(x)
        z = x.norm2()
        require(z > 0, "complex division domain")
        return self * x.conj() * F(1, z)

    def __eq__(self, x):
        x = C.of(x)
        return self.r == x.r and self.i == x.i

    def conj(self):
        return C(self.r, -self.i)

    def norm2(self):
        return self.r * self.r + self.i * self.i


def zero(d):
    return [[C() for _ in range(d)] for _ in range(d)]


def eye(d):
    return [[C(int(i == j)) for j in range(d)] for i in range(d)]


def diag(values):
    d = len(values)
    return [[C.of(values[i]) if i == j else C()
             for j in range(d)] for i in range(d)]


def adj(a):
    return [[a[j][i].conj() for j in range(len(a))] for i in range(len(a))]


def transpose(a):
    return [[a[j][i] for j in range(len(a))] for i in range(len(a))]


def add(a, b, sign=1):
    return [[x + sign * y for x, y in zip(ar, br)]
            for ar, br in zip(a, b)]


def scale(a, x):
    return [[z * x for z in row] for row in a]


def mul(a, b):
    d = len(a)
    return [[sum((a[i][k] * b[k][j] for k in range(d)), C())
             for j in range(d)] for i in range(d)]


def trace(a):
    return sum((a[i][i] for i in range(len(a))), C())


def frob2(a):
    return sum((x.norm2() for row in a for x in row), F())


def comm(a, b):
    return add(mul(a, b), mul(b, a), -1)


def effects(family):
    d = len(family[0][1])
    a, b = zero(d), zero(d)
    for w, k in family:
        a = add(a, scale(mul(adj(k), k), w))
        b = add(b, scale(mul(k, adj(k)), w))
    return a, b


def choi(family):
    d = len(family[0][1])
    j = zero(d * d)
    for w, k in family:
        v = [x for row in k for x in row]
        for a in range(d * d):
            for b in range(d * d):
                j[a][b] += (w / d) * v[a] * v[b].conj()
    return j


def bias(family):
    d = len(family[0][1])
    z = C()
    for w, k in family:
        for v, l in family:
            z += (w * v / d) * trace(mul(mul(mul(adj(l), adj(k)), l), k))
    return z.r


def energies(family):
    d = len(family[0][1])
    ordinary = mixed = F()
    for w, k in family:
        for v, l in family:
            ordinary += w * v * frob2(comm(k, l)) / (2 * d)
            mixed += w * v * frob2(comm(k, adj(l))) / (2 * d)
    return ordinary, mixed


def centered(family):
    d = len(family[0][1])
    return [(w, add(k, scale(eye(d), trace(k) / d), -1))
            for w, k in family]


def fidelity(family):
    d = len(family[0][1])
    return sum((w * trace(k).norm2() / (d * d)
                for w, k in family), F())


def index_contraction(j, d):
    return d * sum((j[a*d+b][c*d+e] * j[c*d+a][e*d+b]
                    for a in range(d) for b in range(d)
                    for c in range(d) for e in range(d)), C()).r


def outer(v):
    return [[x * y.conj() for y in v] for x in v]


def flag_chois(family):
    d = len(family[0][1])
    plus, minus, composed = [], [], []
    for w, k in family:
        for v, l in family:
            lk, kl = mul(l, k), mul(k, l)
            plus.append((w*v/4, add(lk, kl)))
            minus.append((w*v/4, add(lk, kl, -1)))
            composed.append((w*v, lk))
    return choi(plus), choi(minus), choi(composed)


def wh(d):
    family = []
    for i in range(d):
        for j in range(i + 1, d):
            k = zero(d)
            k[i][j], k[j][i] = C(1), C(-1)
            family.append((F(1, d - 1), k))
    return family


def amplitude(d, c, s):
    k1 = zero(d)
    k1[0][1] = C.of(s)
    return [(F(1), diag([1, c] + [1] * (d - 2))),
            (F(1), k1)]


def common_ground(d, survival_amplitude, jump_amplitude):
    family = [(F(1), diag([1] + [survival_amplitude] * (d - 1)))]
    for j in range(1, d):
        k = zero(d)
        k[0][j] = C.of(jump_amplitude)
        family.append((F(1), k))
    return family


def complement_from_isometry(family):
    """Complementary Kraus operators with the original Kraus label as output."""
    d = len(family[0][1])
    require(len(family) == d and all(w == 1 for w, _ in family),
            "rational common-ground isometry convention")
    return [(F(1), [[family[i][1][a][j] for j in range(d)]
                    for i in range(d)]) for a in range(d)]


def compose(after, before):
    return [(w*v, mul(l, k)) for w, l in after for v, k in before]


def common_ground_degrader(d):
    # delta=7/16; representing jump weights separately avoids irrational sqrt(7).
    family = [(F(1), diag([1] + [F(3, 4)] * (d - 1)))]
    for j in range(1, d):
        k = zero(d)
        k[0][j] = C(1)
        family.append((F(7, 16), k))
    return family


def verify():
    z = C(F(3, 5), F(4, 5))
    wh3, wh5 = wh(3), wh(5)
    # Four diagonal vectors form a valid rank-two Schur correlation channel.
    schur = [(F(1), diag([1, 0, F(3, 5), F(3, 5)])),
             (F(1), diag([0, 1, F(4, 5), C(0, F(4, 5))]))]
    # The diagonal unitary creates genuine Phi/off-Phi Choi coherences.
    wh_mix = [(F(3, 4), diag([1, z, z.conj()]))]
    wh_mix += [(w / 4, k) for w, k in wh3]
    orthogonal = [[F(3, 5), F(-4, 13), F(48, 65)],
                  [F(4, 5), F(3, 13), F(-36, 65)],
                  [F(0), F(12, 13), F(5, 13)]]
    matrix_units = []
    for i in range(3):
        for q in range(3):
            if orthogonal[i][q]:
                k = zero(3)
                k[i][q] = C(orthogonal[i][q])
                matrix_units.append((F(1), k))
    cases = [
        ("identity3", [(F(1), eye(3))], True),
        ("werner_holevo3", wh3, True),
        ("werner_holevo5", wh5, True),
        ("schur4", schur, True),
        ("unitary_wh3", wh_mix, True),
        ("matrix_units3", matrix_units, True),
        ("amplitude3", amplitude(3, F(3, 5), F(4, 5)), False),
        ("complex_amplitude3", amplitude(3, C(F(9, 25), F(12, 25)),
                                          F(4, 5)), False),
        ("common_ground3", common_ground(3, F(3, 5), F(4, 5)), False),
    ]
    contractions = mixed_cases = tail_cases = pinching_cases = 0
    flag_cases = marginal_cases = normalized_cases = 0
    values = {}
    for name, family, is_unital in cases:
        d = len(family[0][1])
        a, b = effects(family)
        require(a == eye(d), name + ": trace preserving")
        require((b == eye(d)) == is_unital, name + ": declared unitality")
        j = choi(family)
        require(trace(j) == 1 and j == adj(j), name + ": normalized Hermitian Choi")
        eta = bias(family)
        e, g = energies(family)
        u = frob2(add(b, eye(d), -1)) / d
        require(e == 1 - eta and g == e + u / 2,
                name + ": TP regular/mixed energies")
        require(index_contraction(j, d) == eta,
                name + ": full Choi bilinear contraction")
        require(abs(eta) <= d * trace(mul(j, j)).r,
                name + ": Choi reshuffle Cauchy")
        contractions += 1
        mixed_cases += 1
        for q in range(d):
            for r in range(d):
                require(sum((j[q*d+i][r*d+i] for i in range(d)), C())
                        == b[q][r] / d, name + ": output marginal")
                require(sum((j[i*d+q][i*d+r] for i in range(d)), C())
                        == a[r][q] / d, name + ": input marginal")
                marginal_cases += 1
        require(trace(mul(b, b)).r / (d*d) == (1 + u) / d,
                name + ": output purity/nonunitality")

        residual = centered(family)
        jl, f = choi(residual), fidelity(family)
        mass = 1 - f
        require(all(trace(k) == 0 for _, k in residual), name + ": traceless residual")
        require(trace(jl) == mass, name + ": residual mass")
        require(energies(residual) == (e, g), name + ": scalar-shift invariance")
        phi_vector = [C(int(i == q)) for i in range(d) for q in range(d)]
        p = scale(outer(phi_vector), F(1, d))
        complement = add(eye(d*d), p, -1)
        pinched = add(mul(mul(p, j), p), mul(mul(complement, j), complement))
        require(pinched == add(scale(p, f), jl), name + ": full Choi pinching")
        require(mul(p, jl) == zero(d*d), name + ": orthogonal residual")
        if mass:
            scaled = [(w / mass, k) for w, k in residual]
            require(trace(choi(scaled)) == 1, name + ": normalized residual")
            require(energies(scaled)[1] == g / (mass*mass),
                    name + ": residual energy scaling")
            normalized_cases += 1
        pinching_cases += 1
        if name == "unitary_wh3":
            require(mul(p, mul(j, complement)) != zero(d*d),
                    "generic Fe is not assumed a Choi eigenvalue")
            ra, rb = effects(residual)
            require(ra == rb and ra != scale(eye(d), mass),
                    "normalized residual is balanced but need not be a channel")
        # Tail algebra holds for every subfamily, without a channel assumption.
        subsets = [family[:i] for i in range(1, len(family) + 1)]
        subsets += [family[::2], family[1::2]]
        if name == "matrix_units3":
            subsets.append([(v, k) for v, k in family
                            if v * frob2(k) <= F(1, 10)])
        for tail in subsets:
            if not tail:
                continue
            ta, tb = effects(tail)
            tj, te = choi(tail), bias(tail)
            w = trace(tj).r
            tg = energies(tail)[1]
            require(tg == (trace(mul(ta, ta)).r + trace(mul(tb, tb)).r)/(2*d) - te,
                    name + ": restricted mixed energy")
            require(w*w - te <= tg <= g,
                    name + ": restricted energy and mass Cauchy")
            require(te == index_contraction(tj, d), name + ": tail index identity")
            require(abs(te) <= d * trace(mul(tj, tj)).r,
                    name + ": tail Choi spectral inequality")
            # Use eigenvalue threshold algebra only on an HS-orthogonal list.
            orthogonal = all(trace(mul(adj(k), l)) == 0
                             for i, (_, k) in enumerate(tail)
                             for _, l in tail[i+1:])
            if orthogonal:
                probs = [v * frob2(k) / d for v, k in tail]
                require(trace(mul(tj, tj)).r == sum((x*x for x in probs), F()),
                        name + ": canonical spectral purity")
                beta = d * max(probs)
                require(w*w - beta*w <= g,
                        name + ": spectral threshold quadratic")
            if name == "amplitude3" and tail == family[1:]:
                require(w*w - te > e,
                        "nonunitality cannot be dropped from the tail inequality")
            if name == "matrix_units3" and tail == subsets[-1]:
                require(ta != tb and w == F(25, 507)
                        and te == F(27, 28561) and tg == F(400, 85683),
                        "canonical threshold tail can be unbalanced in a unital channel")
            tail_cases += 1
        jp, jm, composed = flag_chois(family)
        require(add(jp, jm) == composed, name + ": full flagged Choi sum")
        require(trace(jp).r - trace(jm).r == eta,
                name + ": self-switch target I/D mean")
        flag_cases += 1
        values[name] = {"fidelity": str(f), "eta": str(eta),
                        "ordinary_energy": str(e), "mixed_energy": str(g),
                        "nonunitality": str(u)}
    # An odd-dimensional antisymmetric Choi support has no unitary vector:
    # det(M)=det(M^T)=det(-M)=-det(M) for each skew-symmetric M.
    for d, family in ((3, wh3), (5, wh5)):
        require(d % 2 == 1
                and all(transpose(k) == scale(k, -1) for _, k in family),
                "odd antisymmetric non-mixed-unitary support guard")
    require(values["amplitude3"]["ordinary_energy"] == "64/1875"
            and values["amplitude3"]["nonunitality"] == "512/1875"
            and values["amplitude3"]["fidelity"] == "169/225",
            "nonunital rational amplitude-damping constants")
    rotated = [
        (F(1, 2), add(scale(wh3[0][1], F(3, 5)),
                         scale(wh3[1][1], F(4, 5)))),
        (F(1, 2), add(scale(wh3[0][1], F(-4, 5)),
                         scale(wh3[1][1], F(3, 5)))),
        wh3[2],
    ]
    require(choi(rotated) == choi(wh3) and bias(rotated) == bias(wh3)
            and energies(rotated) == energies(wh3),
            "exact Kraus rotation preserves channel and both energies")
    antidegradable_cases = 0
    for d in (2, 3, 4):
        family = common_ground(d, F(3, 5), F(4, 5))
        complementary = complement_from_isometry(family)
        expected = common_ground(d, F(4, 5), F(3, 5))
        degrading = common_ground_degrader(d)
        require(effects(complementary)[0] == eye(d)
                and effects(degrading)[0] == eye(d),
                "complement and degrading maps are trace preserving")
        require(choi(complementary) == choi(expected),
                "full common-ground complementary Choi matrix")
        require(choi(compose(degrading, complementary)) == choi(family),
                "full Choi antidegrading composition")
        gamma = F(16, 25)
        require(fidelity(family) == (1 + (d - 1)*F(3, 5))**2 / (d*d),
                "common-ground identity fidelity")
        e, g = energies(family)
        u = frob2(add(effects(family)[1], eye(d), -1)) / d
        require(e == F(d-1, d) * gamma * F(2, 5)**2
                and u == gamma*gamma*(d-1) and g == e + u/2,
                "common-ground commutator and nonunitality formulas")
        antidegradable_cases += 1
    n, d = 80, 1 << 80
    gamma, s = F(16, 25), F(3, 5)
    f = (1 + (d-1)*s)**2 / (d*d)
    e = F(d-1, d)*gamma*(1-s)**2
    u = gamma*gamma*(d-1)
    require(f >= F(9, 25) and e <= F(64, 625)
            and (1-F(7, 16))*gamma == 1-gamma,
            "all-D deterministic fidelity/commutator and composition bounds")
    false_certificate = (F(9, 25) - F(8, 25))*n - 1 - 3*F(16, 25)
    require(false_certificate == F(7, 25) and e + u/2 >= 1 >= f*f,
            "omitting nonunitality gives a false positive; corrected root prevents it")
    near_unital_cases = 0
    for d in (3, 4):
        reset = []
        for j in range(d):
            k = zero(d)
            k[0][j] = C(1)
            reset.append((F(1), k))
        for epsilon in (F(0), F(1, 100), F(1, 4), F(1, 2)):
            # (1-epsilon) id + epsilon reset is within half-diamond
            # epsilon of id by convexity and the channel norm bound.
            actual = [(1-epsilon, eye(d))] + [(epsilon*w, k) for w, k in reset]
            f_actual, eta_actual = fidelity(actual), bias(actual)
            require(f_actual == 1-epsilon+epsilon/(d*d)
                    and eta_actual == 1-epsilon*epsilon*F(d-1, d),
                    "near-unital rare-reset exact scalar formulas")
            require(abs(1-f_actual) <= epsilon
                    and abs(1-eta_actual) <= 4*epsilon,
                    "near-unital fidelity and two-slot mean continuity guards")
            a = max(F(0), f_actual-epsilon)
            b = max(F(-1), eta_actual-4*epsilon)
            require(0 <= a <= 1 and -1 <= b <= 1,
                    "clipped unital-model scalar bounds")
            require(epsilon <= F(1, 2)
                    and epsilon <= 1-F(1, d)
                    and epsilon <= 1-F(1, d*d),
                    "Audenaert upper-distance substitution stays in monotone range")
            near_unital_cases += 1
    return {
        "status": "passed", "channel_cases": len(cases),
        "full_choi_contractions": contractions, "mixed_energy_cases": mixed_cases,
        "tail_cases": tail_cases, "pinching_cases": pinching_cases,
        "normalized_residual_cases": normalized_cases,
        "full_flagged_choi_cases": flag_cases, "marginal_entries": marginal_cases,
        "kraus_rotation_cases": 1,
        "antidegrading_composition_cases": antidegradable_cases,
        "near_unital_mixture_cases": near_unital_cases,
        "omitted_nonunitality_counterexample": {
            "n": n, "true_capacity": 0,
            "false_u_omitted_certificate": str(false_certificate),
            "bounds_are_population_not_finite_data": True},
        "exact_values": values,
        "scope": ("Finite exact Gaussian-rational matrix guards, including odd-dimensional "
                  "non-mixed-unitary and nonunital channels. The all-dimension entropy "
                  "and quantum coding proofs remain analytic; no encoder, native-model "
                  "validation or query advantage is established.")
    }


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True))
