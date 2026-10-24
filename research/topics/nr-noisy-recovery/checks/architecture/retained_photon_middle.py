"""Exact, standard-library certificate for the four-mode middle instrument.

This checks algebraic identities and positivity over Q(sqrt(5), i).
It is not a formalization of operator-convex pinching or the analytic
optimization proof in methods/remote-spin-phase.md. No matrix
square-root tower is needed: positive Q_j define their positive square
roots; the checked Gram identities then establish the declared Kraus
construction. Import is quiet, no file is written, and no assert or
floating-point arithmetic is used. Running this file prints one JSON report.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import json


class CertificateFailure(RuntimeError):
    pass


@dataclass(frozen=True)
class K5:
    """a + b sqrt(5) + i(c + d sqrt(5)), with rational coefficients."""

    a: Fraction = Fraction(0)
    b: Fraction = Fraction(0)
    c: Fraction = Fraction(0)
    d: Fraction = Fraction(0)

    def __post_init__(self):
        for name in ("a", "b", "c", "d"):
            object.__setattr__(self, name, Fraction(getattr(self, name)))

    @staticmethod
    def lift(value):
        return value if isinstance(value, K5) else K5(Fraction(value))

    def __add__(self, other):
        other = self.lift(other)
        return K5(self.a + other.a, self.b + other.b,
                  self.c + other.c, self.d + other.d)

    __radd__ = __add__

    def __neg__(self):
        return K5(-self.a, -self.b, -self.c, -self.d)

    def __sub__(self, other):
        return self + (-self.lift(other))

    def __rsub__(self, other):
        return self.lift(other) - self

    def __mul__(self, other):
        other = self.lift(other)
        a, b, c, d = self.a, self.b, self.c, self.d
        e, f, g, h = other.a, other.b, other.c, other.d
        return K5(a*e + 5*b*f - c*g - 5*d*h,
                  a*f + b*e - c*h - d*g,
                  a*g + 5*b*h + c*e + 5*d*f,
                  a*h + b*g + c*f + d*e)

    __rmul__ = __mul__

    def conjugate(self):
        return K5(self.a, self.b, -self.c, -self.d)

    def inverse(self):
        norm = self * self.conjugate()
        if norm.c or norm.d:
            raise CertificateFailure("field conjugation produced a nonreal norm")
        denominator = norm.a*norm.a - 5*norm.b*norm.b
        if not denominator:
            raise ZeroDivisionError("zero in Q(sqrt(5),i)")
        return self.conjugate() * K5(norm.a / denominator, -norm.b / denominator)

    def __truediv__(self, other):
        return self * self.lift(other).inverse()

    def __rtruediv__(self, other):
        return self.lift(other) / self

    def __bool__(self):
        return bool(self.a or self.b or self.c or self.d)

    def sign(self):
        """Exact real sign, selecting the positive root sqrt(5)."""
        if self.c or self.d:
            raise ValueError("ordering is only defined on the real subfield")
        a, b = self.a, self.b
        if not b:
            return (a > 0) - (a < 0)
        if not a:
            return (b > 0) - (b < 0)
        if (a > 0) == (b > 0):
            return 1 if a > 0 else -1
        difference = a*a - 5*b*b
        direction = (difference > 0) - (difference < 0)
        return direction if a > 0 else -direction

    def json_coefficients(self):
        return {name: str(getattr(self, name)) for name in ("a", "b", "c", "d")}


ZERO, ONE = K5(), K5(1)
IMAG, ROOT = K5(0, 0, 1), K5(0, 1)


def matrix(rows):
    return tuple(tuple(K5.lift(v) for v in row) for row in rows)


def identity(n):
    return tuple(tuple(ONE if i == j else ZERO for j in range(n)) for i in range(n))


def zero_matrix(n, m):
    return tuple(tuple(ZERO for _ in range(m)) for _ in range(n))


def ma(a, b):
    return tuple(tuple(x + y for x, y in zip(ar, br)) for ar, br in zip(a, b))


def ms(a, b):
    return ma(a, sm(-1, b))


def sm(c, a):
    c = K5.lift(c)
    return tuple(tuple(c*v for v in row) for row in a)


def mm(a, b):
    if len(a[0]) != len(b):
        raise ValueError("incompatible matrix product")
    out = [[ZERO for _ in b[0]] for _ in a]
    for i, ar in enumerate(a):
        for k, av in enumerate(ar):
            if av:
                for j, bv in enumerate(b[k]):
                    if bv:
                        out[i][j] = out[i][j] + av*bv
    return tuple(tuple(row) for row in out)


def adj(a):
    return tuple(tuple(a[i][j].conjugate() for i in range(len(a)))
                 for j in range(len(a[0])))


def trace(a):
    return sum((a[i][i] for i in range(len(a))), ZERO)


def block2(a, b, c, d):
    return tuple(tuple(ar) + tuple(br) for ar, br in zip(a, b)) + \
           tuple(tuple(cr) + tuple(dr) for cr, dr in zip(c, d))


def diag2(a, b):
    return block2(a, zero_matrix(len(a), len(b[0])),
                  zero_matrix(len(b), len(a[0])), b)


def kron(a, b):
    return tuple(tuple(av*bv for av in ar for bv in br) for ar in a for br in b)


def determinant(a):
    """Exact Gaussian elimination, used only for Sylvester positivity."""
    data = [list(row) for row in a]
    result = ONE
    for j in range(len(data)):
        pivot = next((k for k in range(j, len(data)) if data[k][j]), None)
        if pivot is None:
            return ZERO
        if pivot != j:
            data[j], data[pivot] = data[pivot], data[j]
            result = -result
        value = data[j][j]
        result = result * value
        for k in range(j + 1, len(data)):
            ratio = data[k][j] / value
            for col in range(j + 1, len(data)):
                data[k][col] = data[k][col] - ratio*data[j][col]
            data[k][j] = ZERO
    return result


def sylvester_positive(a):
    if adj(a) != a:
        return False
    return all(determinant(tuple(tuple(row[:n]) for row in a[:n])).sign() > 0
               for n in range(1, len(a) + 1))


def outer_columns(a, i, j):
    return tuple(tuple(ar[i]*br[j].conjugate() for br in a) for ar in a)


# Rational polynomials in c,s. Reduction uses s^2=1-c^2, and is purely
# algebraic; no finite angle samples stand in for the all-beta statements.
def poly(terms):
    return {power: Fraction(value) for power, value in terms.items() if value}


def pa(a, b):
    out = dict(a)
    for power, value in b.items():
        out[power] = out.get(power, Fraction(0)) + value
    return poly(out)


def ps(a, b):
    return pa(a, {power: -value for power, value in b.items()})


def pm(a, b):
    out = {}
    for (i, j), av in a.items():
        for (k, l), bv in b.items():
            power = (i+k, j+l)
            out[power] = out.get(power, Fraction(0)) + av*bv
    return poly(out)


def scale_poly(c, a):
    return poly({power: Fraction(c)*value for power, value in a.items()})


def reduce_circle(a):
    out = {}
    pending = list(a.items())
    while pending:
        (i, j), value = pending.pop()
        if j >= 2:
            pending.extend([((i, j-2), value), ((i+2, j-2), -value)])
        else:
            out[(i, j)] = out.get((i, j), Fraction(0)) + value
    return poly(out)


class Checks:
    def __init__(self):
        self.names = []

    def require(self, name, condition):
        if name in self.names:
            raise CertificateFailure("duplicate check: " + name)
        if not condition:
            raise CertificateFailure("failed exact check: " + name)
        self.names.append(name)


def run_certificate():
    checks = Checks()
    check = checks.require
    I, I4, I8 = identity(2), identity(4), identity(8)
    X = matrix([[0, 1], [1, 0]])
    Y = matrix([[0, -IMAG], [IMAG, 0]])
    Z = matrix([[1, 0], [0, -1]])
    Z2 = zero_matrix(2, 2)
    Xb, Yb, Zb = kron(X, I), kron(Y, I), kron(Z, I)

    check("sqrt5 defining equation", ROOT*ROOT == K5(5))
    check("positive root is greater than two", (ROOT-2).sign() > 0)
    check("positive root is below nine quarters", (K5(Fraction(9, 4))-ROOT).sign() > 0)
    check("positive root is below five halves", (K5(Fraction(5, 2))-ROOT).sign() > 0)
    check("complex field inverse", (ROOT+IMAG)*(ROOT+IMAG).inverse() == ONE)

    P = 3/(3+ROOT)
    gamma = (3-ROOT)/4
    h, t = 1+3*ROOT/5, 2*ROOT/5
    a, b = (h-2*t)/2, h-t
    S0 = (3*h-2*t)/2
    nu2 = 3-6*ROOT/5
    delta = (3*ROOT-5)/10
    check("P rationalized", P == (9-3*ROOT)/4)
    check("P equals three gamma", P == 3*gamma)
    check("P strictly improves nine sixteenths", (P-K5(Fraction(9, 16))).sign() > 0)
    check("P below three fifths", (K5(Fraction(3, 5))-P).sign() > 0)
    check("three fifths below native three quarters", Fraction(3, 5) < Fraction(3, 4))
    check("h t normalization", 3*h-2*t == 3+ROOT)
    check("a closed form", a == (5-ROOT)/10)
    check("b closed form", b == (5+ROOT)/5)

    Q0, Q1 = ma(sm(Fraction(1, 2), I), sm(gamma, X)), ms(sm(Fraction(1, 2), I), sm(gamma, X))
    H0, H1 = ms(sm(h, I), sm(t, X)), ma(sm(h, I), sm(t, X))
    H = diag2(H0, H1)
    check("Q0 plus Q1 identity", ma(Q0, Q1) == I)
    check("Q0 Q1 commute", mm(Q0, Q1) == mm(Q1, Q0))
    check("Q0 positive exactly", sylvester_positive(Q0))
    check("Q1 positive exactly", sylvester_positive(Q1))
    check("Q0 below identity", sylvester_positive(ms(I, Q0)))
    check("Q1 below identity", sylvester_positive(ms(I, Q1)))
    check("Q0 inverse H0", mm(Q0, H0) == I and mm(H0, Q0) == I)
    check("Q1 inverse H1", mm(Q1, H1) == I and mm(H1, Q1) == I)
    determinant_q = (3*ROOT-5)/8
    check("Q determinants", determinant(Q0) == determinant_q == determinant(Q1))
    eig_hi, eig_lo = (5-ROOT)/4, (ROOT-1)/4
    check("Q exact eigenvalues", eig_hi+eig_lo == ONE and eig_hi*eig_lo == determinant_q)
    check("Q eigenvalues strictly between zero and one", all(v.sign() > 0 and (1-v).sign() > 0 for v in (eig_hi, eig_lo)))

    C0 = block2(I, sm(-IMAG, Z), sm(-IMAG, X), Z2)
    Cinv = block2(Z2, sm(IMAG, X), sm(IMAG, Z), sm(IMAG, Y))
    check("target Fourier inverse both orders", mm(C0, Cinv) == I4 and mm(Cinv, C0) == I4)
    Splus, Sminus = ma(I4, sm(IMAG, Xb)), ms(I4, sm(IMAG, Xb))
    check("sqrt2 cleared positive phase", mm(adj(Splus), Splus) == sm(2, I4))
    check("sqrt2 cleared negative phase", mm(adj(Sminus), Sminus) == sm(2, I4))
    Ctilde = [mm(mm(Splus, C0), S) for S in (Splus, Sminus)]
    A = sm(Fraction(1, 2), mm(mm(mm(mm(adj(C0), adj(Splus)), H), Splus), C0))
    expected_A = ma(ma(sm(S0, I4), sm(a, Zb)), sm(b, kron(Y, Z)))
    check("I9 exact Pauli expansion", A == expected_A)
    gram = [mm(mm(adj(C), H), C) for C in Ctilde]
    check("I10 unnormalized Gram sum", ma(*gram) == sm(4*(3+ROOT), I4))
    effects = [sm(P/12, G) for G in gram]
    check("I10 middle instrument complete", ma(*effects) == I4)
    D = ma(sm(-a, Yb), sm(b, kron(Z, Z)))
    check("Pauli terms anticommute", ma(mm(Yb, kron(Z, Z)), mm(kron(Z, Z), Yb)) == zero_matrix(4, 4))
    check("D exact square", mm(D, D) == sm(a*a+b*b, I4))
    check("D norm squared closed form", a*a+b*b == 3*(5+ROOT)/10)
    check("positive effect closed form", effects[0] == sm(1/(3+ROOT), ma(sm(S0, I4), D)))
    check("negative effect closed form", effects[1] == sm(1/(3+ROOT), ms(sm(S0, I4), D)))
    check("weak strength squared", 4*(a*a+b*b)/((3+ROOT)*(3+ROOT)) == nu2)
    check("weak strength strictly positive", nu2.sign() > 0)
    check("weak strength squared below three fifths", (K5(Fraction(3, 5))-nu2).sign() > 0)
    check("weak strength strictly below one", (1-nu2).sign() > 0)
    check("effect product exact positive scalar", mm(*effects) == sm(delta, I4) and delta.sign() > 0)
    for index, effect in enumerate(effects):
        check(f"effect {index} Hermitian", adj(effect) == effect)
        check(f"effect {index} exactly positive", sylvester_positive(effect))
        check(f"effect {index} strictly below identity", sylvester_positive(ms(I4, effect)))
        check(f"effect {index} quadratic polynomial", ma(ms(mm(effect, effect), effect), sm(delta, I4)) == zero_matrix(4, 4))
        check(f"effect {index} trace two", trace(effect) == K5(2))
        check(f"history {index} optimal trace cost one", sm(P/24, matrix([[trace(gram[index])]]))[0][0] == ONE)
        for av in (1, -1):
            Etilde = tuple(I) + tuple(sm(av, I))
            check(f"history {index} A {av} midpoint probability half", mm(mm(adj(Etilde), effect), Etilde) == I)

    # Explicitly retain coherences between all four spin sectors. The
    # actual Kraus is sqrt(P/24) times the matrix checked here; correction
    # phases have denominator two and contain no additional radical.
    N_sectors = []
    for av in (1, -1):
        for bv in (1, -1):
            N = ms(ms(I, sm(IMAG*av, Z)), sm(IMAG*bv, X))
            check(f"target unitary sector {av} {bv}", mm(adj(N), N) == sm(3, I))
            N_sectors.append(N)
    Nfull = diag2(diag2(N_sectors[0], N_sectors[1]), diag2(N_sectors[2], N_sectors[3]))
    check("full target scaled unitary", mm(adj(Nfull), Nfull) == sm(3, I8))
    corrected_full = []
    for index, sign in enumerate((1, -1)):
        corrected_sectors = []
        for av in (1, -1):
            for bv in (1, -1):
                sector = zero_matrix(2, 2)
                for j in range(2):
                    for i in range(2):
                        block = tuple(tuple(Ctilde[index][2*j+u][2*i+v] for v in range(2)) for u in range(2))
                        sector = ma(sector, sm((av**i)*(bv**j), block))
                N = ms(ms(I, sm(IMAG*av, Z)), sm(IMAG*bv, X))
                phase_factor = (1+sign*IMAG*av)*(1+IMAG*bv)
                check(f"history {index} Fourier target sector {av} {bv}", sector == sm(phase_factor, N))
                check(f"history {index} sector effect normalization {av} {bv}", mm(adj(sector), sector) == sm(12, I))
                corrector = (1-sign*IMAG*av)*(1-IMAG*bv)/2
                check(f"history {index} corrector unit modulus {av} {bv}", corrector*corrector.conjugate() == ONE)
                corrected = sm(corrector, sector)
                check(f"history {index} corrected sector {av} {bv}", corrected == sm(2, N))
                corrected_sectors.append(corrected)
        full = diag2(diag2(corrected_sectors[0], corrected_sectors[1]),
                     diag2(corrected_sectors[2], corrected_sectors[3]))
        check(f"history {index} full corrected Kraus identity", full == sm(2, Nfull))
        corrected_full.append(full)
    for i in range(8):
        for j in range(8):
            actual = sm(P/24, ma(*(outer_columns(K, i, j) for K in corrected_full)))
            expected = sm(P/3, outer_columns(Nfull, i, j))
            check(f"full channel matrix unit {i} {j}", actual == expected)

    # All-beta identities in the analytic trace-cost minimization.
    pc, psin, unit = poly({(1, 0): 1}), poly({(0, 1): 1}), poly({(0, 0): 1})
    three = scale_poly(3, unit)
    d = scale_poly(Fraction(1, 4), pa(scale_poly(5, unit), scale_poly(3, pm(pc, pc))))
    for x in (1, -1):
        b0 = pa(scale_poly(Fraction(1, 2), pa(three, pc)), scale_poly(x, psin))
        b1 = ps(scale_poly(Fraction(1, 2), ps(three, pc)), scale_poly(x, psin))
        expected = ps(d, scale_poly(x, pm(pc, psin)))
        check(f"all beta eigenvalue product x {x}", reduce_circle(pm(b0, b1)) == expected)
    det_poly = reduce_circle(ps(pm(d, d), pm(pm(pc, pc), pm(psin, psin))))
    expected_det = poly({(0, 0): Fraction(25, 16), (2, 0): Fraction(14, 16), (4, 0): Fraction(25, 16)})
    check("all beta determinant polynomial", det_poly == expected_det)
    check("d minus five quarters is nonnegative polynomial", ps(d, scale_poly(Fraction(5, 4), unit)) == poly({(2, 0): Fraction(3, 4)}))
    check("determinant lower bound polynomial", ps(det_poly, scale_poly(Fraction(25, 16), unit)) == poly({(2, 0): Fraction(14, 16), (4, 0): Fraction(25, 16)}))
    for sign in (1, -1):
        det_b = poly({(0, 0): Fraction(5, 4), (1, 0): Fraction(3*sign, 2), (2, 0): Fraction(5, 4)})
        completed = pa(scale_poly(Fraction(5, 4), pm(pa(pc, scale_poly(Fraction(3*sign, 5), unit)), pa(pc, scale_poly(Fraction(3*sign, 5), unit)))), scale_poly(Fraction(4, 5), unit))
        check(f"all beta B determinant positive completion {sign}", det_b == completed)
    check("optimal trace constant", (P/3)*(6+2*ROOT) == K5(2))

    return {
        "pass": True,
        "arithmetic": "exact rational coefficients in Q(sqrt(5),i); no floating point",
        "scope": "algebraic construction and displayed optimization identities; analytic pinching proof remains in the method note",
        "checks": len(checks.names),
        "check_names": checks.names,
        "exact_values": {
            "total_success_P": P.json_coefficients(),
            "per_history_success": (P/2).json_coefficients(),
            "weak_strength_squared": nu2.json_coefficients(),
            "positive_effect_product_delta": delta.json_coefficients(),
            "Q_determinant": determinant_q.json_coefficients(),
            "optimal_trace_cost": (6+2*ROOT).json_coefficients(),
        },
        "construction_existence": [
            "Positive commuting Q0,Q1 define their unique positive square roots and the terminal coisometry [sqrt(Q0),sqrt(Q1)].",
            "Declare C_h=sqrt(P/24) Ctilde_h, L=I4/sqrt(2), R=diag(sqrt(Q0),sqrt(Q1)), T_h=R^-1 C_h L^-1.",
            "Exact Gram completeness proves sum_h T_h^dagger T_h=I4 without expanding any square-root tower.",
            "Exact full-channel matrix-unit identities certify the corrected accepted map P Ad_G, including cross-sector coherences.",
        ],
    }


if __name__ == "__main__":
    print(json.dumps(run_certificate(), indent=2))
