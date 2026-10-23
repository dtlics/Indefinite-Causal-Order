"""Exact finite NR-R06 Gaussian readout/noise-port guards; stdlib only.

G1--G5 are proved analytically in architecture-baselines.md. This replay
checks nonnormal cavity feedback, a complete finite-band ordinary network
and thermal/order formulas. It certifies no device fit, full qubit noise
spectrum, global pump-budget optimum, or quantum-switch advantage.
"""
from fractions import Fraction as F
import json

if not __debug__:
    raise RuntimeError("Run exact Gaussian readout guards without -O.")


def eye(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def diag(v):
    return [[x if i == j else F(0) for j in range(len(v))]
            for i, x in enumerate(v)]


def tr(a):
    return [list(row) for row in zip(*a)]


def mm(a, b):
    return [[sum((x*y for x, y in zip(row, col)), F(0))
             for col in zip(*b)] for row in a]


def plus(a, b):
    return [[x+y for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]


def scale(x, a):
    return [[x*y for y in row] for row in a]


def minus(a, b):
    return plus(a, scale(F(-1), b))


def inv2(a):
    v = a[0][0]*a[1][1]-a[0][1]*a[1][0]
    assert v
    b = [[a[1][1]/v, -a[0][1]/v], [-a[1][0]/v, a[0][0]/v]]
    assert mm(a, b) == eye(2) == mm(b, a)
    return b


def psd2(a):
    assert a == tr(a)
    return a[0][0] >= 0 and a[1][1] >= 0 and a[0][0]*a[1][1]-a[0][1]**2 >= 0


def feedback_checks():
    identity = eye(2)
    rotation = [[F(3, 5), F(-4, 5)], [F(4, 5), F(3, 5)]]
    r = mm(rotation, diag([F(3, 5), F(4, 5)]))
    f = mm(rotation, diag([F(4, 5), F(3, 5)]))
    assert mm(r, tr(r)) != mm(tr(r), r)
    assert plus(mm(r, tr(r)), mm(f, tr(f))) == identity
    x = inv2(minus(identity, r))
    y = mm(plus(identity, r), x)
    re_y = scale(F(1, 2), plus(y, tr(y)))
    assert re_y == mm(mm(x, minus(identity, mm(r, tr(r)))), tr(x))
    d = diag([F(1), F(2)])
    l = mm(mm(d, x), f)
    k_eff = mm(mm(d, re_y), d)
    assert k_eff == mm(l, tr(l))
    assert psd2(k_eff)
    nc, na = F(1, 100), F(10)
    q_eff = mm(mm(l, diag([nc, na])), tr(l))
    assert psd2(minus(q_eff, scale(nc, k_eff)))
    q_cold = mm(mm(l, diag([nc, nc])), tr(l))
    assert q_cold == scale(nc, k_eff)
    m_other = diag([F(1, 2), F(1)])
    m_eff = plus(m_other, scale(F(1, 2), mm(mm(d, y), d)))
    chi = inv2(m_eff)
    cavity_noise = mm(mm(chi, q_eff), tr(chi))
    cavity_floor = scale(nc, mm(mm(chi, k_eff), tr(chi)))
    assert psd2(minus(cavity_noise, cavity_floor))
    for reflection, expected in [(F(4, 5), F(9)), (F(-4, 5), F(1, 9))]:
        damping_ratio = (1-reflection**2)/(1-reflection)**2
        assert damping_ratio == expected
        noise_f = (1-reflection**2)*nc
        assert noise_f/(1-reflection**2) == nc
        assert noise_f/(1-reflection)**2 == damping_ratio*nc
    return {"nonnormal_return": True, "noise_damping_identity": True,
            "thermal_floor": True, "scalar_linewidth_ratios": ["9", "1/9"]}


def order_checks():
    a = [[F(0), F(1), F(0)], [F(1), F(0), F(0)], [F(0), F(0), F(1)]]
    b = [[F(1), F(0), F(0)], [F(0), F(0), F(1)], [F(0), F(1), F(0)]]
    ba, ab = mm(b, a), mm(a, b)
    assert ba == [[F(0), F(1), F(0)], [F(0), F(0), F(1)], [F(1), F(0), F(0)]]
    assert ab == [[F(0), F(0), F(1)], [F(1), F(0), F(0)], [F(0), F(1), F(0)]]
    assert mm(ab, tr(ab)) == eye(3) == mm(ba, tr(ba))
    na, nc = F(10), F(1, 100)
    occupations = [F(0), na, nc]
    out_ab = [sum(row[j]**2 * occupations[j] for j in range(3)) for row in ab]
    out_ba = [sum(row[j]**2 * occupations[j] for j in range(3)) for row in ba]
    assert out_ab[0] == nc and out_ba[0] == na
    h = 1/((1+na)*(1+nc))
    pplus, pminus = (1+h)/2, (1-h)/2
    bplus, bminus = (na+nc)/(2*(1+h)), (na+nc)/(2*(1-h))
    switched = (na+nc)/2
    assert h == F(100, 1111)
    assert pplus == F(1211, 2222)
    assert bplus == F(158873, 34600)
    assert pplus*bplus+pminus*bminus == switched == F(1001, 200)
    assert bplus > nc and bminus > nc
    return {"ordinary_circulator_backaction": str(nc),
            "switched_unconditional_backaction": str(switched),
            "helper_x_visibility": str(h), "plus_probability": str(pplus),
            "selected_plus_backaction": str(bplus)}


# Self-contained Gaussian-rational arithmetic for the 3x3 complex inverse.
def g(real=0, imag=0):
    return (F(real), F(imag))


def ga(x, y):
    return (x[0]+y[0], x[1]+y[1])


def gn(x):
    return (-x[0], -x[1])


def gm(x, y):
    return (x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0])


def gc(x):
    return (x[0], -x[1])


def gp(x):
    return x[0]*x[0]+x[1]*x[1]


def gi(x):
    denominator = gp(x)
    assert denominator
    return (x[0]/denominator, -x[1]/denominator)


def ge(n):
    return [[g(int(i == j)) for j in range(n)] for i in range(n)]


def gs(x, a):
    return [[gm(x, y) for y in row] for row in a]


def gad(a):
    return [[gc(x) for x in row] for row in zip(*a)]


def gap(a, b):
    return [[ga(x, y) for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]


def gsum(xs):
    result = g()
    for x in xs:
        result = ga(result, x)
    return result


def gmm(a, b):
    return [[gsum(gm(x, y) for x, y in zip(row, col))
             for col in zip(*b)] for row in a]


def ginv(a):
    n = len(a)
    aug = [list(row)+erow for row, erow in zip(a, ge(n))]
    for j in range(n):
        pivot = next((k for k in range(j, n) if aug[k][j] != g()), None)
        assert pivot is not None
        aug[j], aug[pivot] = aug[pivot], aug[j]
        factor = gi(aug[j][j])
        aug[j] = [gm(factor, x) for x in aug[j]]
        for k in range(n):
            if k != j:
                factor = aug[k][j]
                aug[k] = [ga(x, gn(gm(factor, y)))
                          for x, y in zip(aug[k], aug[j])]
    assert [row[:n] for row in aug] == ge(n)
    result = [row[n:] for row in aug]
    assert gmm(a, result) == ge(n) == gmm(result, a)
    return result


def reservoir_checks():
    d = [[g(1), g(), g()], [g(), g(1), g()], [g(), g(), g(2)]]
    gamma = gmm(d, d)
    h = [[g(), g(0, F(1, 2)), g(1)],
         [g(0, F(-1, 2)), g(), g(1)], [g(1), g(1), g()]]
    assert h == gad(h)

    def scattering(omega):
        m = gap(gap(gs(g(F(1, 2)), gamma), gs(g(0, 1), h)),
                gs(g(0, -omega), ge(3)))
        s = gap(ge(3), gs(g(-1), gmm(gmm(d, ginv(m)), d)))
        assert gmm(gad(s), s) == ge(3)
        return s

    powers0 = [[gp(x) for x in row] for row in scattering(F(0))]
    assert powers0 == [[F(0), F(0), F(1)], [F(1), F(0), F(0)], [F(0), F(1), F(0)]]
    powers = [[gp(x) for x in row] for row in scattering(F(1, 2))]
    expected = [[F(x, 389) for x in row] for row in [[65, 4, 320], [260, 65, 64], [64, 320, 5]]]
    assert powers == expected
    forward, reverse = powers[1][0], powers[0][1]
    assert reverse/forward == F(1, 65)
    na, nc = F(10), F(1, 100)
    backaction = reverse*na+powers[0][2]*nc
    detected_noise = powers[1][1]*na+powers[1][2]*nc
    efficiency = forward/(1+2*detected_noise)
    assert backaction == F(216, 1945)
    assert efficiency == F(6500, 42257)
    return {"on_resonance_cycle": True,
            "finite_band_power_matrix": [[str(x) for x in row] for row in powers],
            "reverse_over_forward": str(reverse/forward),
            "returning_occupation": str(backaction),
            "external_source_homodyne_efficiency": str(efficiency),
            "squared_coupling_ledger": "9/4 (not pump watts)"}


def verify_gaussian_readout_guards():
    return {"status": "passed", "feedback": feedback_checks(),
            "controlled_order": order_checks(), "finite_band_reservoir": reservoir_checks(),
            "scope": "Exact finite rational/complex scattering, feedback, thermal-floor and permutation-formula replay. Universal Gaussian/Fock/information arguments are analytic; no full qubit noise spectrum, hardware optimum or switched gain."}


if __name__ == "__main__":
    print(json.dumps(verify_gaussian_readout_guards(), indent=2))

