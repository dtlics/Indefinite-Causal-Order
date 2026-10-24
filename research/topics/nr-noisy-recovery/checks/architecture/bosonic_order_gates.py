"""Exact finite ingredients for NR-R11 bosonic order-gate qualification.

The method note owns the analytic all-count and recovery proofs.
The two arithmetic engines are separate: ordered Q(sqrt(2)) for the
finite-gain inequalities and Q[b]/(b**4-1/2) for KLM Fock polynomials.
No hardware-rate or arbitrary optical-gadget optimum is certified.
"""
from fractions import Fraction as F
from math import comb, factorial
import json


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


class R:
    def __init__(self, a=0, b=0):
        if isinstance(a, R):
            self.a, self.b = a.a, a.b
        else:
            self.a, self.b = F(a), F(b)

    def __add__(self, other):
        other = R(other)
        return R(self.a+other.a, self.b+other.b)

    __radd__ = __add__

    def __neg__(self):
        return R(-self.a, -self.b)

    def __sub__(self, other):
        return self + -R(other)

    def __rsub__(self, other):
        return R(other) + -self

    def __mul__(self, other):
        other = R(other)
        return R(self.a*other.a+2*self.b*other.b,
                 self.a*other.b+self.b*other.a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = R(other)
        denominator = other.a**2-2*other.b**2
        require(denominator != 0, 'Zero algebraic denominator')
        return self*R(other.a/denominator, -other.b/denominator)

    def __rtruediv__(self, other):
        return R(other)/self

    def __pow__(self, n):
        require(isinstance(n, int), 'Only integral powers are used')
        if n < 0:
            return (1/self)**(-n)
        out = R(1)
        for unused in range(n):
            out = out*self
        return out

    def __eq__(self, other):
        other = R(other)
        return self.a == other.a and self.b == other.b

    def sign(self):
        if self.b == 0:
            return (self.a > 0)-(self.a < 0)
        if self.a == 0:
            return (self.b > 0)-(self.b < 0)
        if self.a > 0 and self.b > 0:
            return 1
        if self.a < 0 and self.b < 0:
            return -1
        difference = self.a*self.a-2*self.b*self.b
        return ((difference > 0)-(difference < 0))*(1 if self.a > 0 else -1)

    def __lt__(self, other):
        return (self-other).sign() < 0

    def __le__(self, other):
        return (self-other).sign() <= 0

    def __gt__(self, other):
        return (self-other).sign() > 0

    def __ge__(self, other):
        return (self-other).sign() >= 0

    def __repr__(self):
        return str(self.a) if self.b == 0 else str(self.a)+' + ('+str(self.b)+') sqrt(2)'


def polynomial_product(a, b):
    out = [R() for unused in range(len(a)+len(b)-1)]
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] = out[i+j]+x*y
    return out


def addition_probability(n, l, x):
    return comb(n+l, l)*x**(n+1)*(1-x)**l


def subtraction_probability(n, k, transmission_squared):
    if k > n:
        return R()
    return comb(n, k)*transmission_squared**(n-k)*(1-transmission_squared)**k


def ordered_probability(n, l, k, x, transmission_squared, addition_first):
    if addition_first:
        return addition_probability(n, l, x)*subtraction_probability(n+l, k, transmission_squared)
    if k > n:
        return R()
    return subtraction_probability(n, k, transmission_squared)*addition_probability(n-k, l, x)


def verify_finite_gain_ns():
    root = R(0, 1)
    q, z, k = root-1, 3-2*root, 2*root-1
    x, transmission_squared = 2-root, 1-root/2
    p_control = root/4
    c0, c1 = p_control, -(1-p_control)
    require(x*transmission_squared == z and q*q == z,
            'The physical gain/tap product is not the NS attenuation')
    require(c1/c0 == -k and c0*c0 == R(F(1, 8)),
            'The normalized control/measurement does not give the optimal row')
    require(0 < x < 1 and 0 < transmission_squared < 1 and 0 < p_control < 1,
            'An alleged optimum is not a physical interior setting')
    require(x*(1-x)*(1-transmission_squared) == z,
            'The finite primitive amplitudes do not have the stated normalization')

    # Direct squared Fock amplitudes from the complete primitive expansions.
    ba, ab = [], []
    for n in range(3):
        ba.append(q*q**n*(n+1))
        ab.append(q*q**(n-1)*n)
        require(ba[n]**2 == ordered_probability(n, 1, 1, x, transmission_squared, True),
                'Addition-then-subtraction amplitude disagrees with the physical heralds')
        require(ab[n]**2 == ordered_probability(n, 1, 1, x, transmission_squared, False),
                'Subtraction-then-addition amplitude disagrees with the physical heralds')
    success = [(-1)**n*(c0*ba[n]+c1*ab[n]) for n in range(3)]
    target = [R(1), R(1), R(-1)]
    amplitude = (2-root)/4
    require(success == [amplitude*s for s in target], 'The selected operator is not exact NS')
    p_ns = amplitude*amplitude
    require(p_ns == z/8, 'The NS probability has the wrong physical prefactor')
    require(R(F(1, 16)) > p_ns,
            'The charged sacrificial-source KLM comparator no longer exceeds this family')
    for i in range(3):
        for j in range(3):
            require(success[i]*success[j] == p_ns*target[i]*target[j],
                    'The selected NS subchannel differs on an input matrix unit')

    # Complete one-variable polynomial identities, rather than a sampled optimum.
    square = polynomial_product([R(1), -(1+k)], [R(1), -(1+k)])
    require(square == [R(1), k*k-1-(1+k)**2, (1+k)**2],
            'The general helper-POVM bound lost its square remainder')
    require((1+k)**2 == 8, 'The optimal parallel-row denominator changed')
    center = (1+z)/2
    square = polynomial_product([-center, R(1)], [-center, R(1)])
    require(square == [2*z, -(1+z), R(1)],
            'The finite-gain maximum lost its square remainder')

    # A second allowed count record must be classified, even though it is worse.
    q2, ratio2, x2 = R(F(1, 3)), R(F(-5, 3)), R(F(1, 2))
    diagonal2 = [q2**n*(comb(n+2, 2)+ratio2*q2**(-2)*(comb(n, 2) if n >= 2 else 0))
                 for n in range(3)]
    require(diagonal2 == target, 'The two-pair/two-subtraction NS branch was omitted or misnormalized')
    p2 = R(F(9, 64))*x2*(1-x2)**2*(1-F(1, 9)/x2)**2
    require(p2 == R(F(49, 4608)), 'The physical two-pair NS witness changed')
    for i in range(3):
        for j in range(3):
            require(p2*diagonal2[i]*diagonal2[j] == p2*target[i]*target[j],
                    'The two-pair witness does not preserve all input coherences')
    require(R(F(1, 48)) < p_ns, 'The global two-pair upper bound no longer lies below one pair')
    # max x(1-x)^2 =4/27: 4/27-x(1-x)^2=(x-1/3)^2(4/3-x).
    require(polynomial_product([R(F(1, 9)), R(F(-2, 3)), R(1)], [R(F(4, 3)), R(-1)])
            == [R(F(4, 27)), R(-1), R(2), R(-1)],
            'The two-pair analytic bound has no exact nonnegative remainder')
    for m in range(3, 9):
        q_m = R(F(1, m+1))
        require(q_m*comb(m+1, m) == 1
                and q_m*q_m*comb(m+2, m) == R(F(m+2, 2*(m+1)))
                and 0 < q_m*q_m*comb(m+2, m),
                'Higher-count rising-factor normalization changed')

    # The retained, common zero-count flag is a genuine data filter.
    zero_effect = [x*q**(2*n) for n in range(3)]
    require(zero_effect[0] != zero_effect[1] and zero_effect[1] != zero_effect[2],
            'The zero-count failure was incorrectly made repeat-safe')
    for i in range(3):
        for j in range(3):
            coefficient = x*q**(i+j)
            require(coefficient*coefficient == zero_effect[i]*zero_effect[j],
                    'The full zero-count CP subchannel lost its input coherences')
    for n in range(3):
        require(zero_effect[n] == ordered_probability(n, 0, 0, x, transmission_squared, True)
                == ordered_probability(n, 0, 0, x, transmission_squared, False),
                'The common failed flag disagrees with the complete primitive expansions')
        retained_11 = p_control*ba[n]**2+(1-p_control)*ab[n]**2
        require(0 <= p_ns <= retained_11 and zero_effect[n]+retained_11 <= 1,
                'Accepted and failed flags do not fit the all-attempt probability ledger')
    require(0 < c0*c0*ordered_probability(0, 2, 1, x, transmission_squared, True)
            and ordered_probability(0, 2, 1, x, transmission_squared, False) == 0,
            'Threshold clicks cannot hide the positive photon-number-changing fine record')
    return {'status': 'PASS', 'arithmetic': 'exact Q(sqrt(2)) and Fraction',
            'qutrit_ns_matrix_units': 9, 'two_pair_ns_matrix_units': 9,
            'zero_count_matrix_units': 9, 'higher_count_finite_checks': 6,
            'one_pair_optimal_probability': str(p_ns),
            'two_pair_witness_probability': str(p2),
            'two_pair_global_bound': '1/48', 'ordinary_klm_probability': '1/4',
            'scope': 'Finite exact physical-herald, selected-map, probability and polynomial-identity ingredients; all-count classification, recovery obstruction, field-mode/router and hardware cost proofs remain analytic.'}


def klm_q(x):
    return (F(x), F(0), F(0), F(0))


def klm_add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def klm_scale(a, s):
    return tuple(x * F(s) for x in a)


def klm_mul(a, b):
    out = [F(0)] * 4
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            k = i + j
            out[k % 4] += x * y * (F(1, 2) if k >= 4 else 1)
    return tuple(out)


klm_ZERO, klm_ONE = klm_q(0), klm_q(1)
klm_B = (F(0), F(1), F(0), F(0))
klm_ROOT2 = klm_scale(klm_mul(klm_B, klm_B), 2)
klm_A = klm_add(klm_ONE, klm_scale(klm_ROOT2, -1))
klm_C = klm_mul(klm_scale(klm_A, -1), klm_B)
klm_U = ((klm_A, klm_B, klm_C),
     (klm_B, klm_q(F(1, 2)), klm_scale(klm_A, F(1, 2))),
     (klm_C, klm_scale(klm_A, F(1, 2)), klm_add(klm_ROOT2, klm_q(F(-1, 2)))))


def klm_linear_product(poly, column):
    out = {}
    for occ, coefficient in poly.items():
        for mode, factor in enumerate(column):
            dest = list(occ)
            dest[mode] += 1
            dest = tuple(dest)
            out[dest] = klm_add(out.get(dest, klm_ZERO), klm_mul(coefficient, factor))
    return {occ: c for occ, c in out.items() if c != klm_ZERO}


def verify_klm_qutrit():
    # A sacrificial vacuum PDC source, independent of the stored unknown data.
    source_x = F(1, 2)
    source_probability = source_x*(1-source_x)
    require(source_probability == F(1, 4)
            and addition_probability(0, 1, R(source_x)) == R(source_probability)
            and source_probability*F(1, 4) == F(1, 16),
            "The paid one-attempt photon-source/gate ledger changed")
    require(polynomial_product([R(F(-1, 2)), R(1)], [R(F(-1, 2)), R(1)])
            == [R(F(1, 4)), R(-1), R(1)],
            "The vacuum PDC single-pair optimum lost its square remainder")
    for i in range(3):
        for j in range(3):
            dot = klm_ZERO
            for row in klm_U:
                dot = klm_add(dot, klm_mul(row[i], row[j]))
            require(dot == klm_q(int(i == j)), "The passive interferometer is not unitary")
    input_columns = []
    for n in range(3):
        poly = {(0, 0, 0): klm_ONE}
        for unused in range(n):
            poly = klm_linear_product(poly, [row[0] for row in klm_U])
        poly = klm_linear_product(poly, [row[1] for row in klm_U])
        require(all(sum(occ) == n + 1 for occ in poly), "Photon number changed")
        input_columns.append(poly)
    # Detector outcomes (r2,r3) are all integer pairs with r2+r3 <= 3.
    records = [(r2, r3) for r2 in range(4) for r3 in range(4-r2)]
    effects = {}
    for record in records:
        values = []
        for n, poly in enumerate(input_columns):
            retained = n + 1 - sum(record)
            if retained < 0:
                values.append(klm_ZERO)
                continue
            occ = (retained, *record)
            coeff = poly.get(occ, klm_ZERO)
            norm = F(factorial(retained)*factorial(record[0])*factorial(record[1]),
                     factorial(n))
            values.append(klm_scale(klm_mul(coeff, coeff), norm))
        effects[record] = values
    accepted_coefficients = [poly.get((n, 1, 0), klm_ZERO)
                             for n, poly in enumerate(input_columns)]
    require(accepted_coefficients == [klm_q(F(1, 2)), klm_q(F(1, 2)), klm_q(F(-1, 2))],
            "Accepted transformation is not half the nonlinear-sign unitary")
    # Every input/reference matrix unit |n><m| has the correct success image.
    for n in range(3):
        for m in range(3):
            expected = F(1 if (n == 2) == (m == 2) else -1, 4)
            require(klm_mul(accepted_coefficients[n], accepted_coefficients[m]) == klm_q(expected),
                    "Accepted reference coherence changed")
    for n in range(3):
        total = klm_ZERO
        failure = klm_ZERO
        for record, values in effects.items():
            total = klm_add(total, values[n])
            if record != (1, 0):
                failure = klm_add(failure, values[n])
        require(total == klm_ONE, "A full Fock failure record was omitted")
        require(failure == klm_q(F(3, 4)), "Failure effect is not three quarters identity")
    require(effects[(3, 0)][0] == effects[(3, 0)][1] == klm_ZERO,
            "Three-count failure should annihilate the vacuum/one-photon sectors")
    require(effects[(3, 0)][2] == klm_q(F(3, 8)),
            "The irreversible failure witness has the wrong amplitude")
    for n, poly in enumerate(input_columns):
        power = klm_ONE
        for unused in range(n):
            power = klm_mul(power, klm_A)
        require(poly.get((n+1, 0, 0), klm_ZERO) == klm_mul(klm_B, power),
                "The zero-count failed output lost its raising/filtering amplitude")
    require((3, 0, 0) in input_columns[2], "Retained |3> failure leakage was truncated")
    require(len(effects) == 10, "Wrong full-record alphabet")
    return {"input_dimension": 3, "retained_fock_levels": 4,
            "detector_records": 10, "success_record": [1, 0],
            "success_probability_all_inputs": "1/4",
            "failure_probability_all_inputs": "3/4",
            "source_single_photon_probability": str(source_probability),
            "source_charged_joint_probability": str(source_probability*F(1, 4)),
            "reference_matrix_units": 9,
            "irreversible_failure_record": [3, 0],
            "field": "Q[b]/(b^4-1/2), positive b=2^(-1/4)",
            "scope": "All ten Fock-record probabilities and nine successful reference matrix units, plus irreversible/leakage failure witnesses; full failed coherence maps have the analytic coefficient formula in the method note. Ideal passive optics, one supplied ancilla photon and ideal number counters."}


def verify():
    return {"status": "PASS",
            "finite_gain_ns": verify_finite_gain_ns(),
            "ordinary_klm": verify_klm_qutrit(),
            "scope": "Finite exact physical-instrument ingredients; analytic all-count classification, helper optimality, recovery obstruction and physical access/cost hypotheses belong to methods/bosonic-order-gates.md."}


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2, sort_keys=True))
