"""Validated continuum Gaussian witness for NR-R11's ordinary spin factory.

Standard-library outward interval arithmetic and an analytic-strip bound,
not floating quadrature or an optimizer. The proof and physical scope are
in methods/remote-spin-phase.md. Import is silent; no files are written.
"""
from fractions import Fraction as F
import json

if not __debug__:
    raise SystemExit("Run without -O: validated replay uses assertions.")

Q = 10**28


def ceildiv(a, b):
    return -((-a)//b)


class Interval:
    """Closed rational interval, rounded outward to the grid 1/Q."""
    __slots__ = ("lo", "hi")

    def __init__(self, x=0, hi=None, raw=False):
        if raw:
            self.lo, self.hi = int(x), int(hi)
        else:
            x = F(x)
            self.lo = x.numerator*Q//x.denominator
            self.hi = ceildiv(x.numerator*Q, x.denominator)

    def __add__(self, other):
        other = interval(other)
        return Interval(self.lo+other.lo, self.hi+other.hi, raw=True)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo, raw=True)

    def __sub__(self, other):
        return self+-interval(other)

    def __rsub__(self, other):
        return interval(other)+-self

    def __mul__(self, other):
        other = interval(other)
        products = (self.lo*other.lo, self.lo*other.hi,
                    self.hi*other.lo, self.hi*other.hi)
        return Interval(min(products)//Q, ceildiv(max(products), Q), raw=True)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = interval(other)
        assert not other.lo <= 0 <= other.hi
        reciprocal = Interval(Q*Q//other.hi, ceildiv(Q*Q, other.lo), raw=True)
        return self*reciprocal

    def absupper(self):
        return F(max(abs(self.lo), abs(self.hi)), Q)

    def bounds(self):
        return [str(F(self.lo, Q)), str(F(self.hi, Q))]


def interval(x):
    return x if isinstance(x, Interval) else Interval(x)


class ComplexInterval:
    __slots__ = ("r", "i")

    def __init__(self, r=0, i=0):
        self.r, self.i = interval(r), interval(i)

    def __add__(self, other):
        other = complex_interval(other)
        return ComplexInterval(self.r+other.r, self.i+other.i)

    __radd__ = __add__

    def __neg__(self):
        return ComplexInterval(-self.r, -self.i)

    def __sub__(self, other):
        return self+-complex_interval(other)

    def __mul__(self, other):
        other = complex_interval(other)
        return ComplexInterval(self.r*other.r-self.i*other.i,
                               self.r*other.i+self.i*other.r)

    __rmul__ = __mul__

    def conj(self):
        return ComplexInterval(self.r, -self.i)


def complex_interval(x):
    return x if isinstance(x, ComplexInterval) else ComplexInterval(x)


def widen(a, error):
    a, error = interval(a), interval(error)
    return Interval(a.lo-error.hi, a.hi+error.hi, raw=True)


def sincos(x):
    x = Interval(x)
    x2 = x*x
    ts, tc, ss, sc = x, Interval(1), Interval(), Interval()
    for n in range(40):
        ss += ts if n % 2 == 0 else -ts
        sc += tc if n % 2 == 0 else -tc
        ts = ts*x2/F((2*n+2)*(2*n+3))
        tc = tc*x2/F((2*n+1)*(2*n+2))
    # The alternating tails decrease from these omitted terms onward.
    return widen(ss, ts.absupper()), widen(sc, tc.absupper())


def expminus(a):
    assert 0 <= a < 256
    x, term, total = Interval(a/256), Interval(1), Interval()
    for n in range(40):
        total += term if n % 2 == 0 else -term
        term = term*x/F(n+1)
    total = widen(total, term.absupper())
    for _ in range(8):
        total = total*total
    return total


# All rates/frequencies are ordinary MHz: the common factor 2*pi cancels.
PARAMETERS = ((F(38, 5), F(5, 2), F(23, 10), F(3)),
              (F(38, 5), F(14, 5), F(12, 5), F(3)))
ANGLES = (F(8005482133044127, 10**16), F(7631314280924895, 10**16),
          F(7885503202769666, 10**16), F(31166396848875224, 10**16))
SIGMA = F(11993, 64000)


def reflection(station, bright, nu):
    g, kappa, kappa_r, gamma = PARAMETERS[station]
    g2 = g*g if bright else F(0)
    dr, di = kappa*gamma-nu*nu+g2, -(kappa+gamma)*nu
    denominator = dr*dr+di*di
    nr, ni = 2*kappa_r*gamma, -2*kappa_r*nu
    return ComplexInterval(1-(nr*dr+ni*di)/denominator,
                           -(ni*dr-nr*di)/denominator)


def kernels(nu, rotations):
    (s_a, c_a), (s_b, c_b), (s_f, c_f), (s_u, c_u) = rotations
    prep_a, prep_b = (c_a, s_a), (c_b, s_b)
    state = []
    for a in (0, 1):
        first = (reflection(0, a, nu)*c_f, reflection(0, 0, nu)*s_f)
        middle = (first[0]*c_u+first[1]*s_u,
                  -first[0]*s_u+first[1]*c_u)
        for b in (0, 1):
            rb = (reflection(1, b, nu), reflection(1, 0, nu))
            for pol in (0, 1):
                state.append(rb[pol]*middle[pol]*prep_a[a]*prep_b[b])
    probability = sum((v.conj()*v).r for v in state)
    bloch = []
    for which in range(4):
        transformed = []
        for k in range(8):
            a, b = k//4, (k//2) % 2
            if which == 0:
                transformed.append(state[k]*(-1 if a else 1))
            elif which == 1:
                transformed.append(state[k ^ 4])
            elif which == 2:
                transformed.append(state[k]*(-1 if b else 1))
            else:
                transformed.append(state[k ^ 2])
        bloch.append(sum((state[k].conj()*transformed[k]).r for k in range(8)))
    return probability, bloch


def verify():
    assert F(18, 100) < SIGMA < F(19, 100)
    strip = F(1, 10)
    for g, kappa, kappa_r, gamma in PARAMETERS:
        assert g >= 0 and gamma > strip and kappa > strip
        assert 0 < kappa_r <= kappa
        assert 1+2*kappa_r/(kappa-strip) < 3
    assert 9/(2*SIGMA*SIGMA) > 113
    assert F(601, 10000)/(2*SIGMA*SIGMA) > F(1, 2)
    rotations = tuple(sincos(x) for x in ANGLES)
    h = F(1, 100)
    normalizer, probability = Interval(), Interval()
    bloch = [Interval() for _ in range(4)]
    for k in range(301):
        nu = k*h
        weight = expminus(nu*nu/(2*SIGMA*SIGMA))
        # Real preparation/optics and r(-nu)=conj(r(nu)) make these kernels
        #even. The spin Y kernels are odd and integrate to exactly zero.
        factor = h*weight*(1 if k == 0 else 2)
        p, f = kernels(nu, rotations)
        normalizer += factor
        probability += factor*p
        for j in range(4):
            bloch[j] += factor*f[j]
    # On both edges of |Im nu|<=.1 the Gaussian-weighted analytic kernels
    #have absolute integral <243 each. Infinite trapezoid error is thus
    #<486/(2^60-1); the omitted DISCRETE tail is <2^-100. See the note.
    error = F(486, 2**60-1)+F(1, 2**100)
    normalizer = widen(normalizer, error)
    assert normalizer.lo > Q//3
    probability = widen(probability, error)/normalizer
    bloch = [widen(x, error)/normalizer for x in bloch]
    residual = max(x.absupper() for x in bloch)
    assert residual < F(2, 10**15)
    assert F(probability.lo, Q) > F(36675027396793, 10**14)
    assert F(probability.hi, Q) < F(36675027396795, 10**14)
    # Y=p-max(||r_A||,||r_B||). The l1 bound avoids square-root arithmetic.
    deficit = max(bloch[0].absupper()+bloch[1].absupper(),
                  bloch[2].absupper()+bloch[3].absupper())
    lower = F(probability.lo, Q)-deficit
    assert lower > F(36675027, 10**8)
    return {"status": "passed", "frequency_nodes": 601,
            "exact_sigma_MHz": str(SIGMA),
            "exact_angles_radians": [str(x) for x in ANGLES],
            "reflection_probability_enclosure": probability.bounds(),
            "spin_Bloch_component_abs_upper": str(residual),
            "Bell_yield_strict_lower": "36675027/100000000",
            "scope": "continuum Gaussian integrals for the declared pure one-photon elastic cavity model, with full coherent photon-mode measurement and charged local filters; no native analyzer, router or complete-loss comparison"}


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True))
