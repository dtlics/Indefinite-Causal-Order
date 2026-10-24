"""Exact actual-response gate budgets for NR-R11 (RS69--77).

Replays a monochromatic ordinary primal, fixed spatial-readout Gaussian
budgets, and a separate exact full-field-POVM Gaussian witness. Universal
moment/phase-cone attainment and resolvent/Taylor bounds are analytic inputs
in methods/remote-spin-phase.md. No optimizer, quadrature or hardware clock.
Import is quiet; active guards are preserved under -O and -OO.
"""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json

from retained_photon_serial import G, add, adj, eye, kron, mm, require, scale


HERE = Path(__file__).resolve().parent


def _transpose(a):
    return list(map(list, zip(*a)))


def _det(a):
    if not a:
        return G(1)
    return sum(((-1)**j*a[0][j]*_det(
        [r[:j]+r[j+1:] for r in a[1:]]) for j in range(len(a))), G())


def _positive_minors(a):
    require(a == adj(a), "Hermitian gate certificate")
    count = 0
    for n in range(1, len(a)+1):
        for ix in combinations(range(len(a)), n):
            value = _det([[a[i][j] for j in ix] for i in ix])
            require(value.i == 0 and value.r > 0, "positive gate principal minor")
            count += 1
    return count


def _partial_transpose(a):
    return [[a[2*x+v][2*u+y] for u in range(2) for v in range(2)]
            for x in range(2) for y in range(2)]


def _reflection(rate, nu):
    g, k, kr, gamma = rate
    za, zc = G(gamma, -nu), G(k, -nu)
    return 1-G(2*kr)/zc, 1-2*kr*za/(zc*za+g*g)


def _response_rows(alpha, delta, beta, epsilon):
    return [[alpha*beta, G(), G(), G()],
            [alpha*beta, G(), alpha*epsilon, G()],
            [alpha*beta, delta*beta, G(), G()],
            [alpha*beta, delta*beta, alpha*epsilon, delta*epsilon]]


def _reverse_covariance(h, t):
    # H features FIRST station B then SECOND station A. Physical spin row
    # order remains 00,01,10,11, so G=T J H^T J T^dagger, also for complex H.
    swap = [0, 2, 1, 3]
    return mm(mm(t, [[h[swap[j]][swap[i]] for j in range(4)]
                     for i in range(4)]), adj(t))


def _data(certificate):
    d = certificate if certificate is not None else json.loads(
        (HERE/"ordinary_spin_gate.json").read_text(encoding="utf-8"))
    require(d["schema"] == "actual-rs44-resonant-ordinary-cz-v1", "gate schema")
    integers = ("rates_denominator", "probe_detuning_MHz", "denominator",
                "p_numerator", "p_denominator", "native_upper_numerator",
                "native_upper_denominator")
    require(all(type(d[k]) is int for k in integers), "integer gate parameters")
    require(all(d[k] > 0 for k in ("rates_denominator", "denominator",
                                  "p_denominator", "native_upper_denominator")),
            "positive gate denominators")
    # Bind the existing RS44 nominal Table S1 tuples; all calculations below
    # consume these shared certificate values rather than new program copies.
    require(d["rates_denominator"] == 10
            and d["rates_A_numerators"] == [76, 25, 23, 30]
            and d["rates_B_numerators"] == [76, 28, 24, 30], "RS44 source rates")
    require(all(type(z) is int for key in ("rates_A_numerators", "rates_B_numerators")
                for z in d[key]), "integer source rates")
    require(d["probe_detuning_MHz"] == 0 and d["word"] == "BA", "center BA word")
    matrices = []
    for key in ("moment_numerators", "phase_numerators"):
        require(len(d[key]) == 4 and all(len(r) == 4 for r in d[key]), "gate matrix shape")
        require(all(type(z) is int for r in d[key] for z in r), "integer gate matrices")
        matrices.append([[G(F(z, d["denominator"])) for z in r] for r in d[key]])
    rates = [tuple(F(z, d["rates_denominator"]) for z in d[key])
             for key in ("rates_A_numerators", "rates_B_numerators")]
    return d, matrices[0], matrices[1], rates


def _center(d, h, omega, rates):
    x, y, c, t = h[0][1], h[0][2], h[0][3], h[1][3]
    require(h == [[G(1), x, y, c], [x, x, c.conj(), t],
                  [y, c, y, c], [c.conj(), t, c.conj(), t]], "full moment equalities")
    q = F(d["p_numerator"], d["p_denominator"])
    require(q == F(177, 500) and all(omega[i][i] == q for i in range(4)),
            "equal center success diagonals")
    require(omega[0][1] == omega[2][3] and omega[0][2] == omega[1][3],
            "complete complex phase equalities")
    (alpha, a1), (beta, b1) = [_reflection(rate, F(0)) for rate in rates]
    require([z.r for z in (alpha, a1, beta, b1)] ==
            [F(-21, 25), F(2573, 3263), F(-5, 7), F(647, 827)]
            and all(z.i == 0 for z in (alpha, a1, beta, b1)), "center responses")
    tmat = _response_rows(alpha, a1-alpha, beta, b1-beta)
    gram = _reverse_covariance(h, tmat)
    signs = [1, 1, 1, -1]
    residual = [[gram[i][j]-signs[i]*omega[i][j]*signs[j] for j in range(4)]
                for i in range(4)]
    matrices = (h, omega, _partial_transpose(omega), residual)
    minors = sum(_positive_minors(m) for m in matrices)
    margin = F(7, 10000)
    shifted = sum(_positive_minors(add(m, scale(eye(4), -margin))) for m in matrices)
    upper = ((alpha*beta).conj()*(alpha*beta)).r
    require(upper == F(d["native_upper_numerator"], d["native_upper_denominator"])
            == F(9, 25) and upper/q == F(60, 59), "center dark-input ceiling")
    return q, {"ordinary_exact_CZ_probability": str(q),
               "positive_principal_minors": minors,
               "shifted_positive_principal_minors": shifted,
               "uniform_PSD_margin": str(margin), "word": "BA",
               "native_exact_input_independent_gate_ceiling": str(upper),
               "native_to_constructive_ordinary_yield_ceiling": str(upper/q)}


def _complex_ordering_guards(rates):
    # Independent literal rank-two contacts catch the transpose and unequal
    # station-role conventions that a real certificate cannot distinguish.
    p = kron([[G(1), G()], [G(), G()]], eye(2))  # first contact B
    u = [[G(F(3, 5)), G(0, F(4, 5))], [G(0, F(4, 5)), G(F(3, 5))]]
    uu = kron(u, eye(2))
    r = mm(mm(uu, p), adj(uu))  # second contact A
    require(mm(p, p) == p and mm(r, r) == r, "literal projector identities")
    phi = [[G(1)], [G(0, 1)], [G(1)], [G(2)]]
    norm = mm(adj(phi), phi)[0][0].r
    features = [phi, mm(p, phi), mm(r, phi), mm(r, mm(p, phi))]
    v = [[features[j][i][0] for j in range(4)] for i in range(4)]
    h = scale(mm(adj(v), v), 1/norm)
    require(h[0][3].i != 0, "genuinely complex moment fixture")
    count = 0
    for nu in (F(0), F(1, 10)):
        (alpha, a1), (beta, b1) = [_reflection(rate, nu) for rate in rates]
        delta, epsilon = a1-alpha, b1-beta
        aa = [scale(eye(4), alpha), add(scale(eye(4), alpha), scale(r, delta))]
        bb = [scale(eye(4), beta), add(scale(eye(4), beta), scale(p, epsilon))]
        columns = [mm(mm(aa[a], bb[b]), phi) for a in range(2) for b in range(2)]
        actual_v = [[columns[j][i][0] for j in range(4)] for i in range(4)]
        actual = _transpose(scale(mm(adj(actual_v), actual_v), 1/norm))
        tmat = _response_rows(alpha, delta, beta, epsilon)
        require(actual == _reverse_covariance(h, tmat), "complex BA covariance")
        require(actual != mm(mm(tmat, _transpose(h)), adj(tmat)), "J omission differs")
        swap = [0, 2, 1, 3]
        wrong_h = [[h[swap[i]][swap[j]] for j in range(4)] for i in range(4)]
        require(actual != mm(mm(tmat, wrong_h), adj(tmat)), "H transpose omission differs")
        count += 16
    return count


def _fixed_spatial_gaussian(q, rates):
    require(all(gamma >= k >= kr > 0 for g, k, kr, gamma in rates), "accretive passive rates")
    ls = [2*kr/k**2 for g, k, kr, gamma in rates]
    hs = [4*kr/k**3 for g, k, kr, gamma in rates]
    first, second = sum(ls), sum(hs)+2*ls[0]*ls[1]
    require(first == F(8258, 6125) and second == F(413174, 214375), "global derivatives")
    l, h, sqrt_q, sigma = F(27, 20), F(193, 100), F(3, 5), F(1, 100)
    require(first < l and second < h and q < sqrt_q**2, "outward derivative envelopes")
    cross, bad = sqrt_q*h*sigma**2, l*l*sigma**2
    delta, lower = cross+bad, q-cross
    require((cross, bad, delta, lower) ==
            (F(579, 5000000), F(729, 4000000), F(5961, 20000000), F(1769421, 5000000)),
            "fixed spatial Gaussian budgets")
    require(delta/lower == F(1987, 2359228) < F(843, 1000000), "conditional reference error")
    coefficient, dark_center = F(0), F(1)
    for g, k, kr, gamma in rates:
        coefficient += 4*kr*(k-kr)/k**4
        dark_center *= (1-2*kr/k)**2
    upper = dark_center+coefficient*sigma**2
    require(coefficient == F(4110886, 37515625) and dark_center == F(9, 25),
            "dark-population second-moment coefficient")
    require(upper == F(67530180443, 187578125000)
            and upper/lower == F(540241443544, 531047477625) < F(509, 500),
            "native uniform-minimum acceptance comparison")
    return {"center_exact_weight": str(q), "sigma_MHz": str(sigma),
            "global_first_derivative": str(first), "global_second_derivative": str(second),
            "cross_budget": str(cross), "target_orthogonal_mass_upper": str(bad),
            "accepted_CP_diamond_error_upper": str(delta),
            "all_input_success_and_good_lower": str(lower),
            "conditional_half_trace_error_upper": str(delta/lower),
            "conditional_target_fidelity_lower": str(1-bad/lower),
            "formal_discard_to_abort_half_diamond_upper": str(delta),
            "native_uniform_all_input_acceptance_upper": str(upper),
            "native_to_constructive_min_success_ratio_upper": str(upper/lower),
            "incident_time_RMS_microseconds": "25/pi",
            "scope": "Fixed spatial POVM tensor identity on frequency; spatial/feedback flags retained and click times coarse-grained. Full Gaussian, approximate all-reference CZ. Native numerator bounds guaranteed minimum acceptance, not average Choi-good. No conversion, intermediate spin encoding, no-click success or finite clock."}


# Exact rational intervals for the separate full-field-POVM Gaussian case.
# Existing continuum factory intervals reject -O; they are not imported or
# modified here. These tuples require no rounding or assertion semantics.
def _interval(a, b=None):
    a, b = F(a), F(a if b is None else b)
    require(a <= b, "interval order")
    return a, b


def _ia(a, b):
    return a[0]+b[0], a[1]+b[1]


def _ineg(a):
    return -a[1], -a[0]


def _im(a, b):
    products = [x*y for x in a for y in b]
    return min(products), max(products)


def _isquare(a):
    return (F(0) if a[0] <= 0 <= a[1] else min(x*x for x in a), max(x*x for x in a))


def _idiv(a, b):
    require(not b[0] <= 0 <= b[1], "interval denominator excludes zero")
    return _im(a, _interval(1/b[1], 1/b[0]))


def _ci(a, b=0):
    return _interval(a), _interval(b)


def _ca(a, b):
    return _ia(a[0], b[0]), _ia(a[1], b[1])


def _cs(a, b):
    return _ca(a, (_ineg(b[0]), _ineg(b[1])))


def _cm(a, b):
    return (_ia(_im(a[0], b[0]), _ineg(_im(a[1], b[1]))),
            _ia(_im(a[0], b[1]), _im(a[1], b[0])))


def _cmod2(a):
    return _ia(_isquare(a[0]), _isquare(a[1]))


def _cd(a, b):
    numerator = _cm(a, (b[0], _ineg(b[1])))
    denominator = _cmod2(b)
    return _idiv(numerator[0], denominator), _idiv(numerator[1], denominator)


def _field_gaussian(rates):
    band, sigma = F(1, 10), F(1, 40)
    darks, lower_factors = [], []
    for g, k, kr, gamma in rates:
        zc, za = (_interval(k), _interval(-band, band)), (_interval(gamma), _interval(-band, band))
        dark = _cs(_ci(1), _cd(_ci(2*kr), zc))
        bright = _cs(_ci(1), _cd(_cm(_ci(2*kr), za), _ca(_cm(zc, za), _ci(g*g))))
        t = _cd(bright, dark)
        a = _cm(_ci(F(1, 2)), _ca(_ci(1), t))
        a_upper = max(abs(x) for x in a[0])+max(abs(x) for x in a[1])
        lower = min(1-a_upper, (1+_cmod2(t)[0])/2-a_upper)
        require(lower > 0, "positive tensor Gershgorin lower")
        darks.append(dark)
        lower_factors.append(lower)
    gram_lower = _cmod2(_cm(*darks))[0]*lower_factors[0]*lower_factors[1]
    require(gram_lower > F(265099, 1000000) > F(53, 200), "full-band Gram lower")
    require(band == 4*sigma, "Gaussian four-sigma band")
    # Two-sided Mills: outside4sigma <=e^-8/(2sqrt(2pi))<1/1024.
    gaussian_lower = F(53, 200)*F(1023, 1024)
    q = F(1, 4)
    require(gaussian_lower == F(54219, 204800) > q, "full Gaussian Gram lower")
    d = [1, 1, 1, -1]
    require(d[0]*d[3] == -d[1]*d[2], "CZ nonlocal phase cross ratio")
    masks = [[1, sb, sa, sa*sb] for sa in (1, -1) for sb in (1, -1)]
    rows = [[d[i]*mask[i] for i in range(4)] for mask in masks]
    covariance = [[sum(q*row[i]*row[j]/4 for row in rows) for j in range(4)] for i in range(4)]
    require(covariance == [[q if i == j else F(0) for j in range(4)] for i in range(4)],
            "CZ-twisted four-phase covariance")
    require(all([mask[i]*row[i] for i in range(4)] == d for mask, row in zip(masks, rows)),
            "each phase flag corrects to CZ")
    return {"sigma_MHz": str(sigma), "interval_half_width_MHz": str(band),
            "pointwise_Gram_lower": "265099/1000000",
            "Gaussian_inband_mass_lower": "1023/1024",
            "Gaussian_Gram_lower": str(gaussian_lower), "exact_CZ_probability": str(q),
            "corrected_phase_flags": 4, "incident_time_RMS_microseconds": "10/pi",
            "scope": "Separate pure Bell-program construction with complete joint spatial/spectral photon POVM. Exact unknown-ABR CZ; all rejects charged. This stronger readout is not a bucket detector or a finite-clock hardware certificate."}


def verify(certificate=None, expected_rates=None):
    d, h, omega, rates = _data(certificate)
    if expected_rates is not None:
        require(tuple(map(tuple, expected_rates)) == tuple(rates), "shared RS44 parameters")
    q, center = _center(d, h, omega, rates)
    return {"status": "passed", "center_primal": center,
            "complex_BA_covariance_entries": _complex_ordering_guards(rates),
            "fixed_spatial_full_Gaussian": _fixed_spatial_gaussian(q, rates),
            "exact_full_field_Gaussian": _field_gaussian(rates),
            "scope": "Nominal RS44 single-photon elastic scalar model and declared four-mode ports. Exact finite arithmetic plus analytic moment/phase, accretive-resolvent, Gaussian CP/Taylor and Mills inputs. No all-detuning optimum, physical failure-state recovery, source uncertainty or hardware-rate claim."}


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True, indent=2))
