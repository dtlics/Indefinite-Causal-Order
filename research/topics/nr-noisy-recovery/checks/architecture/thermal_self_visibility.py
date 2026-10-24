"""Exact finite checks of the full thermal self-SWITCH visibility formula.

Finite excitation sectors are lifted completely, with their factorial
Gram metric. The infinite thermal generating trace remains analytic;
partial thermal sums have their exact omitted initial-mixture weight.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial
import json

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def mm(a, b):
    return [[sum((x * y for x, y in zip(row, col)), F(0)) for col in zip(*b)] for row in a]

def tr(a):
    return [list(x) for x in zip(*a)]

def eye(d):
    return [[F(i == j) for j in range(d)] for i in range(d)]

def det(a):
    if not a:
        return F(1)
    return sum(((-1) ** j * a[0][j] * det([row[:j] + row[j + 1:] for row in a[1:]]) for j in range(len(a))), F(0))

def occupancy(m):
    return [(a, b, m - a - b) for a in range(m + 1) for b in range(m - a + 1)]

def gram(n):
    return factorial(n[0]) * factorial(n[1]) * factorial(n[2])

def positive_semidefinite(a):
    require(a == tr(a), 'Thermal visibility exact check failed: a == tr(a)')
    b = [row[:] for row in a]
    for i in range(len(b)):
        pivot = b[i][i]
        require(pivot >= 0, 'Thermal visibility exact check failed: pivot >= 0')
        if not pivot:
            require(all((b[i][j] == b[j][i] == 0 for j in range(i + 1, len(b)))), 'Thermal visibility exact check failed: all((b[i][j] == b[j][i] == 0 for j in range(i + 1, len(b))))')
            continue
        for j in range(i + 1, len(b)):
            for k in range(j, len(b)):
                b[j][k] -= b[j][i] * b[i][k] / pivot
                b[k][j] = b[j][k]

@lru_cache(None)
def lift(matrix_tuple, m):
    """Symmetric power in unnormalized monomials; no square-root numerics."""
    u = matrix_tuple
    basis = occupancy(m)
    index = {n: j for j, n in enumerate(basis)}
    result = [[F(0) for _ in basis] for _ in basis]
    for col, n in enumerate(basis):
        polynomial = {(0, 0, 0): F(1)}
        for mode, count in enumerate(n):
            for _ in range(count):
                nxt = {}
                for powers, coefficient in polynomial.items():
                    for outmode in range(3):
                        if not u[outmode][mode]:
                            continue
                        p = list(powers)
                        p[outmode] += 1
                        p = tuple(p)
                        nxt[p] = nxt.get(p, F(0)) + coefficient * u[outmode][mode]
                polynomial = nxt
        for nout, coefficient in polynomial.items():
            result[index[nout]][col] = coefficient
    return result

def tup(a):
    return tuple((tuple(r) for r in a))

def matrices(x, s):
    require(x * x + s * s == 1, 'Thermal visibility exact check failed: x * x + s * s == 1')
    r1 = [[x, s, 0], [-s, x, 0], [0, 0, 1]]
    r2 = [[x, 0, s], [0, 1, 0], [-s, 0, x]]
    u0, u1 = (mm(r2, r1), mm(r1, r2))
    return (u0, u1, mm(tr(u1), u0))

def parameters(x, n):
    c = (1 - x) ** 3 * (1 + x)
    d = 1 + 2 * n * (1 - x) * (1 - x * x) + n * n * (1 - x * x) ** 2
    q = 1 - (2 * n + 1) * c / d
    return (c, d, q)

def multiply_series(a, b, degree):
    return [sum((a[i] * b[k - i] for i in range(k + 1) if i < len(a) and k - i < len(b)), F(0)) for k in range(degree + 1)]

def divide_series(numerator, denominator, degree):
    require(denominator[0], 'Thermal visibility exact check failed: denominator[0]')
    out = []
    for k in range(degree + 1):
        v = numerator[k] if k < len(numerator) else F(0)
        v -= sum((denominator[j] * out[k - j] for j in range(1, min(k, len(denominator) - 1) + 1)), F(0))
        out.append(v / denominator[0])
    return out

def series_power(a, k, degree):
    out = [F(1)] + [F(0)] * degree
    for _ in range(k):
        out = multiply_series(out, a, degree)
    return out

def fock_vector(u, initial):
    m = sum(initial)
    basis = occupancy(m)
    col = basis.index(initial)
    a = lift(tup(u), m)
    return {state: a[row][col] for row, state in enumerate(basis) if a[row][col]}

def reference_fixture(x, s, r, cutoff, signal_levels=(0, 1)):
    """Exact Bell-reference fixture with an unnormalized partial thermal mixture."""
    u0, u1, _ = matrices(x, s)
    require(set(signal_levels) <= {0, 1}, 'Thermal visibility exact check failed: set(signal_levels) <= {0, 1}')
    size = cutoff + max(signal_levels) + 1
    dim = 2 * size
    outputs = {name: [[F(0) for _ in range(dim)] for _ in range(dim)] for name in ('serial0', 'serial1', 'cross01', 'cross10', 'plus', 'minus')}
    for btotal in range(cutoff + 1):
        for b1 in range(btotal + 1):
            b2 = btotal - b1
            weight = (1 - r) ** 2 * r ** btotal / F(2 * factorial(b1) * factorial(b2))
            vectors = {}
            for ref in range(2):
                level = signal_levels[ref]
                a, b = (fock_vector(u0, (level, b1, b2)), fock_vector(u1, (level, b1, b2)))
                vectors[ref] = {'0': a, '1': b, '+': {state: (a.get(state, 0) + b.get(state, 0)) / 2 for state in set(a) | set(b)}, '-': {state: (a.get(state, 0) - b.get(state, 0)) / 2 for state in set(a) | set(b)}}
            choices = {'serial0': ('0', '0'), 'serial1': ('1', '1'), 'cross01': ('0', '1'), 'cross10': ('1', '0'), 'plus': ('+', '+'), 'minus': ('-', '-')}
            for name, (left, right) in choices.items():
                for rr in range(2):
                    for cc in range(2):
                        for (sa, e1, e2), a in vectors[rr][left].items():
                            for (sb, f1, f2), b in vectors[cc][right].items():
                                if (e1, e2) == (f1, f2):
                                    outputs[name][rr * size + sa][cc * size + sb] += weight * a * b * factorial(e1) * factorial(e2)
    require(outputs['serial0'] == outputs['serial1'], "Thermal visibility exact check failed: outputs['serial0'] == outputs['serial1']")
    require(outputs['cross01'] == outputs['cross10'], "Thermal visibility exact check failed: outputs['cross01'] == outputs['cross10']")
    for i in range(dim):
        for j in range(dim):
            serial, cross = (outputs['serial0'][i][j], outputs['cross01'][i][j])
            require(outputs['plus'][i][j] == (serial + cross) / 2, "Thermal visibility exact check failed: outputs['plus'][i][j] == (serial + cross) / 2")
            require(outputs['minus'][i][j] == (serial - cross) / 2, "Thermal visibility exact check failed: outputs['minus'][i][j] == (serial - cross) / 2")
    for name in ('serial0', 'plus', 'minus'):
        positive_semidefinite(outputs[name])
    trace = lambda a: sum((a[i][i] * factorial(i % size) for i in range(dim)), F(0))
    mass = sum(((b + 1) * (1 - r) ** 2 * r ** b for b in range(cutoff + 1)), F(0))
    tail = r ** (cutoff + 1) * (cutoff + 2 - (cutoff + 1) * r)
    require(mass + tail == 1, 'Thermal visibility exact check failed: mass + tail == 1')
    require(trace(outputs['serial0']) == mass, "Thermal visibility exact check failed: trace(outputs['serial0']) == mass")
    pminus = trace(outputs['minus'])
    require(0 <= pminus <= mass, 'Thermal visibility exact check failed: 0 <= pminus <= mass')
    n = r / (1 - r)
    _, d, q = parameters(x, n)
    exact_pminus = (1 - sum((q ** k for k in signal_levels)) / (2 * d)) / 2
    require(pminus <= exact_pminus <= pminus + tail, 'Thermal visibility exact check failed: pminus <= exact_pminus <= pminus + tail')
    a, b = (signal_levels[0], size + signal_levels[1])
    bell = lambda m: (m[a][a] + m[b][b] + m[a][b] + m[b][a]) / 2
    qminus = bell(outputs['minus'])
    require(0 <= qminus <= pminus, 'Thermal visibility exact check failed: 0 <= qminus <= pminus')
    require(bell(outputs['plus']) + qminus == bell(outputs['serial0']), "Thermal visibility exact check failed: bell(outputs['plus']) + qminus == bell(outputs['serial0'])")
    require(trace(outputs['plus']) + pminus == mass, "Thermal visibility exact check failed: trace(outputs['plus']) + pminus == mass")
    return {'initial_bath_total_cutoff': cutoff, 'signal_reference_levels': list(signal_levels), 'kept_thermal_mass': str(mass), 'exact_omitted_initial_mixture_weight': str(tail), 'partial_minus_probability': str(pminus), 'exact_formula_minus': str(exact_pminus), 'bell_good_minus': str(qminus)}

def _verify_ordinary_parity_coin():
    """Exact code/twirl fixtures; the full gain law and CP-norm proof are analytic."""
    cases = moment_cases = matrix_units = 0
    example = None
    for eta in (F(0), F(3, 5), F(99, 100), F(999, 1000), F(1)):
        for nbar in (F(0), F(1), F(3)):
            effective = eta*eta
            g = 1+(1-effective)*nbar
            loss, v = effective/g, g-1
            u, t = 1-loss, eta/g
            require(g*loss == effective, 'Ordinary serial loss/amplifier factorization failed.')
            require(2*g-1-effective == (1-effective)*(2*nbar+1),
                    'Ordinary serial characteristic-function noise failed.')
            require(0 <= t <= 1 and 0 <= u <= 1 and v >= 0,
                    'Ordinary serial parameters leave their physical ranges.')
            beta = u*u+4*u*v+6*v*v
            pt, zt = (1+t*t)**2/(4*g), (1-t*t)**2/(4*g)
            diagonal, reversed_diagonal = (F(1), t*t), (t*t, F(1))
            signs = (F(1), F(-1))
            for i in range(2):
                for j in range(2):
                    actual = (diagonal[i]*diagonal[j]
                              +reversed_diagonal[i]*reversed_diagonal[j])/(2*g)
                    require(actual == pt+zt*signs[i]*signs[j],
                            'Ordinary no-event logical-X twirl matrix unit failed.')
                    matrix_units += 1
            require(pt+zt == (1+t**4)/(2*g), 'Ordinary no-event twirl trace failed.')
            number, logical_x = [[F(0), F(0)], [F(0), F(2)]], [[F(0), F(1)], [F(1), F(0)]]
            flipped_number = mm(mm(logical_x, number), logical_x)
            require([[(number[i][j]+flipped_number[i][j])/2 for j in range(2)]
                     for i in range(2)] == eye(2), 'Ordinary coin-twirled input energy failed.')
            require(eta+(1-eta)*nbar >= 0
                    and effective+(1-effective)*nbar >= 0,
                    'Ordinary contact input/output mean energy failed.')
            for occupation in range(3):
                total_fac2 = loss_mean = F(0)
                ll = lk = kk = F(0)
                for lost in range(occupation+1):
                    probability = F(comb(occupation, lost))*u**lost*loss**(occupation-lost)
                    remaining = occupation-lost
                    gain_mean = v*(remaining+1)
                    gain_fac2 = v*v*(remaining+1)*(remaining+2)
                    ll += probability*lost*(lost-1)/2
                    lk += probability*lost*gain_mean
                    kk += probability*gain_fac2/2
                    total_fac2 += probability*(lost*(lost-1)+2*lost*gain_mean+gain_fac2)
                    loss_mean += probability*lost
                require(loss_mean == occupation*u, 'Ordinary binomial loss mean failed.')
                closed = occupation*(occupation-1)*u*u
                closed += 2*v*(occupation*occupation*u-occupation*(occupation-1)*u*u)
                closed += v*v*(occupation*occupation*loss*loss+occupation*loss*(u+3)+2)
                require(total_fac2 == closed, 'Ordinary full gain/loss factorial moment failed.')
                require(ll <= u*u and lk <= 4*u*v and kk <= 6*v*v,
                        'Ordinary three-term event-moment bounds failed.')
                require(total_fac2/2 == ll+lk+kk <= beta,
                        'Ordinary nonzero even-event probability bound failed.')
                parity = sum((F(comb(occupation, lost))*u**lost*loss**(occupation-lost)
                              *(-1)**lost/(2*g-1)**(occupation-lost+1)
                              for lost in range(occupation+1)), F(0))
                h = loss/(2*g-1)-u
                require(parity == h**occupation/(2*g-1),
                        'Ordinary complete-gain parity generating function failed.')
                moment_cases += 1
            for lost in range(3):
                for gained in range(7):
                    if (gained-lost) % 2 == 0 and (gained or lost):
                        require(gained+lost >= 2, 'Ordinary accepted event count failed.')
            if eta == F(999, 1000) and nbar == 1:
                example = {'eta': str(eta), 'nbar': str(nbar),
                           'identity_coefficient_pT': str(pt),
                           'contaminating_CP_norm_upper': str(beta+zt),
                           'conditional_reference_trace_error_upper': str((beta+zt)/(pt+beta+zt))}
            cases += 1
    return {'parameter_cases': cases, 'twirl_matrix_units': matrix_units,
            'complete_gain_moment_cases': moment_cases,
            'input_code': ['|0>', '|2>'], 'input_maximum_number': 2,
            'coin_averaged_input_energy': 1, 'thermal_output_cutoff': None,
            'example': example,
            'scope': 'Exact finite-code twirl/parity/factorial-moment arithmetic; full infinite gain law, '
                     'reference-stable CP bound and physical controls remain analytic conditional inputs.'}


def verify():
    sector_checks = series_checks = 0
    samples = [(F(0), F(1)), (F(3, 5), F(4, 5)), (F(4, 5), F(3, 5)), (F(99, 101), F(20, 101)), (F(1), F(0))]
    for x, s in samples:
        u0, u1, v = matrices(x, s)
        require(mm(tr(v), v) == eye(3) and det(v) == 1, 'Thermal visibility exact check failed: mm(tr(v), v) == eye(3) and det(v) == 1')
        a, h = (x ** 4 - 2 * x ** 3 + 2 * x, x + x * x - x ** 3)
        block = [row[1:] for row in v[1:]]
        require(v[0][0] == a, 'Thermal visibility exact check failed: v[0][0] == a')
        require(block == [[h, 1 - x * x], [(1 - x * x) * x * (x - 2), h]], 'Thermal visibility exact check failed: block == [[h, 1 - x * x], [(1 - x * x) * x * (x - 2), h]]')
        require(det(block) == a, 'Thermal visibility exact check failed: det(block) == a')
        require(a - h * h == -(1 - x * x) ** 2 * x * (x - 2) >= 0, 'Thermal visibility exact check failed: a - h * h == -(1 - x * x) ** 2 * x * (x - 2) >= 0')
        for n in (F(0), F(1, 3), F(1), F(3)):
            r = n / (n + 1)
            c, d, q = parameters(x, n)
            den, num = (1 - 2 * r * h + r * r * a, a - 2 * r * h + r * r)
            require(den * (n + 1) ** 2 == d, 'Thermal visibility exact check failed: den * (n + 1) ** 2 == d')
            require((den - num) * (n + 1) ** 2 == (2 * n + 1) * c, 'Thermal visibility exact check failed: (den - num) * (n + 1) ** 2 == (2 * n + 1) * c')
            require(q == num / den and 0 <= q <= 1 and (d >= 1), 'Thermal visibility exact check failed: q == num / den and 0 <= q <= 1 and (d >= 1)')
            require(d == (1 + n * (1 - x * x)) ** 2 - 2 * n * (1 - x * x) * x, 'Thermal visibility exact check failed: d == (1 + n * (1 - x * x)) ** 2 - 2 * n * (1 - x * x) * x')
            for z in (F(0), F(1, 5), F(4, 5)):
                vd = [[v[i][j] * (z, r, r)[j] for j in range(3)] for i in range(3)]
                determinant = det([[F(i == j) - vd[i][j] for j in range(3)] for i in range(3)])
                require(determinant == den - z * num, 'Thermal visibility exact check failed: determinant == den - z * num')
        for m in range(5):
            basis = occupancy(m)
            c0, c1, cv = (lift(tup(u0), m), lift(tup(u1), m), lift(tup(v), m))
            g = [[F(gram(basis[i]) if i == j else 0) for j in range(len(basis))] for i in range(len(basis))]
            require(mm(mm(tr(c0), g), c0) == g, 'Thermal visibility exact check failed: mm(mm(tr(c0), g), c0) == g')
            require(mm(mm(tr(c1), g), c1) == g, 'Thermal visibility exact check failed: mm(mm(tr(c1), g), c1) == g')
            c1adj = [[c1[j][i] * F(gram(basis[j]), gram(basis[i])) for j in range(len(basis))] for i in range(len(basis))]
            require(mm(c1adj, c0) == cv, 'Thermal visibility exact check failed: mm(c1adj, c0) == cv')
            for col, initial in enumerate(basis):
                pm = sum(((c0[row][col] - c1[row][col]) ** 2 * F(gram(state), 4 * gram(initial)) for row, state in enumerate(basis)), F(0))
                require(1 - 2 * pm == cv[col][col], 'Thermal visibility exact check failed: 1 - 2 * pm == cv[col][col]')
            sector_checks += 1
        degree = 3
        for k in range(3):
            diagonal_sums = []
            for btotal in range(degree + 1):
                diagonal_sums.append(sum((fock_vector(v, (k, b1, btotal - b1)).get((k, b1, btotal - b1), F(0)) for b1 in range(btotal + 1)), F(0)))
            actual = multiply_series([F(1), F(-2), F(1)], diagonal_sums, degree)
            numerator = multiply_series([F(1), F(-2), F(1)], series_power([a, -2 * h, F(1)], k, degree), degree)
            denominator = series_power([F(1), -2 * h, a], k + 1, degree)
            require(actual == divide_series(numerator, denominator, degree), 'Thermal visibility exact check failed: actual == divide_series(numerator, denominator, degree)')
            series_checks += degree + 1
        for n in (F(0), F(1, 3), F(1)):
            c, d, q = parameters(x, n)
            for energy in (F(0), F(1, 3), F(1), F(5, 2)):
                k = energy.numerator // energy.denominator
                t = energy - k
                sharp = (1 - ((1 - t) * q ** k + t * q ** (k + 1)) / d) / 2
                linear = (d - 1) / (2 * d) + (2 * n + 1) * c * energy / (2 * d * d)
                require((d - 1) / (2 * d) <= sharp <= min(F(1, 2), linear), 'Thermal visibility exact check failed: (d - 1) / (2 * d) <= sharp <= min(F(1, 2), linear)')
                for high in (3, 17, 101, 1001):
                    if high < energy:
                        continue
                    rare = energy / high
                    probability = (1 - (1 - rare + rare * q ** high) / d) / 2
                    require(probability <= sharp, 'Thermal visibility exact check failed: probability <= sharp')
                require((1 - ((1 - t) * q ** k + t * q ** (k + 1)) / d) / 2 == sharp, 'Thermal visibility exact check failed: (1 - ((1 - t) * q ** k + t * q ** (k + 1)) / d) / 2 == sharp')
                if n == 0:
                    require(sharp <= c * energy / 2, 'Thermal visibility exact check failed: sharp <= c * energy / 2')
    fixtures = {'thermal_bell': reference_fixture(F(3, 5), F(4, 5), F(1, 4), 3), 'thermal_vacuum': reference_fixture(F(3, 5), F(4, 5), F(1, 4), 3, (0, 0)), 'pure_loss': reference_fixture(F(3, 5), F(4, 5), F(0), 3), 'identity': reference_fixture(F(1), F(0), F(1, 4), 3), 'zero_transmission_pure_loss': reference_fixture(F(0), F(1), F(0), 2)}
    return {'status': 'passed', 'complete_photon_sectors': sector_checks, 'thermal_series_coefficients': series_checks, 'reference_fixtures': fixtures, 'ordinary_parity_coin': _verify_ordinary_parity_coin(), 'scope': 'Finite rational beam-splitter/Fock lifts, flag/payoff and ordinary parity-coin fixtures; infinite thermal trace, arbitrary normal inputs, sharp energy and complete-gain CP bounds analytic.'}
if __name__ == '__main__':
    print(json.dumps(verify(), sort_keys=True))
