"""Exact rational moving-encoding rate and fine-operator guards.

Supplied encoded-H relaxation, copied white rates and d=8 Choi utility.
Finite matrix fixtures do not certify continuous source/device control.
"""
from fractions import Fraction as F
import json

if not __debug__:
    raise RuntimeError("Run exact moving-encoding guards without -O.")


def mul_poly(a, b):
    out = [F(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def verify_rates():
    gamma, big_gamma, gb, lam = F(50, 3849), F(20, 1013)-F(25, 3849), F(1, 80), F(5)
    s = gamma/2+big_gamma
    a, b = lam*gb/2-s, (lam-1)*big_gamma/2
    alpha = 5*a/12-59*b/192
    beta = -3*a/8+111*b/256
    assert beta > 0
    old_bound = F(15, 164224)
    native_over_bare = F(373165517, 1453311455232)
    # Short elementary certificate: sqrt(3)>433/250; pi<22/7 follows
    # from integral_0^1 x^4(1-x)^4/(1+x^2)dx=22/7-pi >0.
    assert F(433, 250)**2 < 3
    simple_lower = alpha+beta*F(3031, 5500)
    assert simple_lower == F(9975181247, 16469532288000)
    assert simple_lower-native_over_bare == F(2091658216283, 5994909752832000) > 0
    assert simple_lower > native_over_bare > old_bound > 0
    assert simple_lower > F(6, 10000)
    quotient = [F(4), F(0), F(-4), F(0), F(5), F(-4), F(1)]
    numerator = mul_poly(quotient, [F(1), F(0), F(1)])
    numerator[0] -= 4
    assert numerator == [F(0)]*4+[F(1), F(-4), F(6), F(-4), F(1)]
    assert sum(q/F(k+1) for k, q in enumerate(quotient)) == F(22, 7)
    # Example explicit total edge measure preserving the comparison.
    m = gamma+2*big_gamma+gb
    edge_measure_over_T = F(1, 1000000)
    penalty = 4*lam*m*edge_measure_over_T
    assert simple_lower-penalty > native_over_bare
    ledger_count = 0
    for r in (F(1, 4), F(1, 2), F(1)):
        for test_lambda in (F(1), F(7, 2), F(5)):
            # Complete measured-flag first-order ledger with helper ON.
            sigma_total, phi_total = gamma*r/2, big_gamma*r
            sigma_gg, phi_gg = gamma*r*r/2, big_gamma*r*r
            sigma_f, phi_f = sigma_total-sigma_gg, phi_total-phi_gg
            n = sigma_total+phi_total
            assert sigma_f >= 0 and phi_f >= 0 and n == s*r
            dt = F(1, 100)
            q0 = p0 = 1-n*dt  # first-order no-jump, not finite-rate exact
            q = q0+phi_gg*dt/2
            p = p0+phi_gg*dt
            bad, reject = p-q, (sigma_total+phi_f)*dt
            assert p+reject == 1 and bad == phi_gg*dt/2
            cost = n+(test_lambda-1)*phi_gg/2
            assert q-test_lambda*bad == 1-cost*dt
            assert cost == s*r+(test_lambda-1)*big_gamma*r*r/2
            b_drop = gb*r/2
            bare_b_cost, flagged_b_cost = (1+test_lambda)*b_drop, b_drop
            assert bare_b_cost-flagged_b_cost == test_lambda*gb*r/2
            ledger_count += 1
    return {"gain_sqrt3_over_pi_affine_coefficients_per_us": [str(alpha), str(beta)],
            "short_gain_lower_per_us": str(simple_lower),
            "short_excess_over_known_native_plus_lower_per_us": str(simple_lower-native_over_bare),
            "known_native_plus_over_bare_per_us": str(native_over_bare),
            "total_smooth_transition_measure_over_T_fixture": str(edge_measure_over_T),
            "full_flag_nojump_ledger_fixtures": ledger_count,
            "scope": "Supplied exact encoded Hamiltonian with unpriced controlled derivative/exchange ports; first-order copied white-rate counterexample only."}


def zeros(n, m):
    return [[F(0) for _ in range(m)] for _ in range(n)]


def eye(n):
    a = zeros(n, n)
    for i in range(n):
        a[i][i] = F(1)
    return a


def trans(a):
    return list(map(list, zip(*a)))


def mm(a, b):
    return [[sum(a[i][k]*b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def kron(a, b):
    return [[a[i//len(b)][j//len(b[0])]*b[i % len(b)][j % len(b[0])]
             for j in range(len(a[0])*len(b[0]))]
            for i in range(len(a)*len(b))]


def norm_on_code(a, rows):
    return sum(a[i][j]**2 for i in rows for j in (0, 1))/2


def verify_fine_operators():
    i2, i3 = eye(2), eye(3)
    sigma = [[F(0), F(1)], [F(0), F(0)]]
    p1 = [[F(0), F(0)], [F(0), F(1)]]
    lb = zeros(3, 3)
    lb[0][1] = F(1)
    u1s = [i2, [[F(0), F(1)], [F(1), F(0)]],
           [[F(3, 5), F(-4, 5)], [F(4, 5), F(3, 5)]]]
    cases = 0
    for c, s in [(F(1), F(0)), (F(3, 5), F(4, 5)), (F(4, 5), F(3, 5))]:
        r = c*c
        v = [[F(1), F(0), F(0)], [F(0), c, -s], [F(0), s, c]]
        vf = kron(i2, v)
        for u1 in u1s:
            assert mm(trans(u1), u1) == i2
            p = u1[1][0]**2
            tag = zeros(6, 6)
            for data in range(3):
                u = u1 if data == 1 else i2
                for dout in range(2):
                    for din in range(2):
                        tag[3*dout+data][3*din+data] = u[dout][din]
            assert mm(trans(tag), tag) == eye(6)
            for jump in (sigma, p1):
                physical = kron(jump, i3)
                actual = mm(mm(trans(vf), mm(mm(trans(tag), physical), tag)), vf)
                # Original input code has helper0 and data dark/hub.
                assert norm_on_code(actual, range(6)) == r*p/2
                # Every jump annihilates initial dark codeword, so all
                # rare/leaked outcomes retain reference B=e support.
                assert all(actual[row][0] == 0 for row in range(6))
                lready = mm(mm(trans(u1), jump), u1)[0][0]
                assert actual[1][1] == r*lready
                assert actual[0][0] == actual[0][1] == actual[1][0] == 0
                p_readygg = norm_on_code(actual, (0, 1))
                q_readygg = (actual[0][0]+actual[1][1])**2/4
                assert p_readygg == r*r*lready*lready/2
                assert q_readygg == p_readygg-q_readygg == r*r*lready*lready/4
                if jump == sigma:
                    assert lready*lready == p*(1-p)
                else:
                    assert lready == p
                cases += 1
            actual_b = mm(mm(trans(vf), mm(mm(trans(tag), kron(i2, lb)), tag)), vf)
            assert norm_on_code(actual_b, range(6)) == r/2
            assert norm_on_code(actual_b, (3, 4, 5)) == r*p/2
            assert all(actual_b[row][0] == 0 for row in range(6))
            # No-jump helper good loss for arbitrary positive weights
            # gamma and 2Gamma: expectation of transformed A is S*r*p.
            gamma, big_gamma = F(2, 7), F(3, 11)
            physical_a = kron([[F(0), F(0)], [F(0), gamma+2*big_gamma]], i3)
            actual_a = mm(mm(trans(vf), mm(mm(trans(tag), physical_a), tag)), vf)
            n = (actual_a[0][0]+actual_a[1][1])/2
            assert n == (gamma/2+big_gamma)*r*p
    return {"full_helper_single_jump_fixtures": cases,
            "full_B_jump_and_nojump_fixtures": cases//2,
            "scope": "Exact rational 6D fine operators including rejected helper/coupler records; supplied encoded-H relaxation only."}


def verify():
    return {"rates_and_ledgers": verify_rates(),
            "fine_operators": verify_fine_operators()}


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
