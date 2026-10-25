"""Exact constants and finite envelope fixtures for the cold GAD cutoff.

The all-parameter proof is analytic in methods/thermal-return-cadence.md. These fixtures
check its coefficient identities and endpoints; sampling is not a proof.
No source temperature, physical check, SWITCH router or clock is fitted.
"""
from fractions import Fraction as F
import json

if not __debug__:
    raise RuntimeError("Run exact cold-GAD cutoff guards without -O.")


def coefficients(x, c):
    b = c*(1-x)**2
    qp = x*x+b*(1+6*x+x*x)/4+b*b/2
    bp = b*(3+14*x+3*x*x)/4
    qm = b*(1+x)**2/4
    bm = 3*b*(1-x)**2/4-b*b/2
    qo = x*x+x*b+b*b
    bo = 3*b*(x+b)
    return b, qp, bp, qm, bm, qo, bo


def verify():
    cmax, tmax = F(1, 8), F(16, 5)
    bracket = 14*cmax-3+14*cmax*cmax*tmax+2*cmax**3*tmax*tmax
    assert bracket == -F(51, 100)
    assert 1-tmax*tmax/32 == F(17, 25)
    assert (-3+14*F(1, 5)-3*F(1, 5)**2)/4 == -F(2, 25)
    count = ratio_count = 0
    for x in (F(0), F(1, 10), F(1, 5), F(1, 3), F(1, 2), F(4, 5), F(1)):
        for c in (F(0), F(1, 64), F(1, 16), F(1, 8)):
            b, qp, bp, qm, bm, qo, bo = coefficients(x, c)
            assert min(b, qp, bp, qm, bm, qo, bo) >= 0
            assert (qo-bo)-(qp-bp) == b*(1+x*x-5*b)/2
            assert bp-bo == b*((3+2*x+3*x*x)/4-3*b)
            assert bp-bo >= 2*b*x
            assert (qo-bo)-(qp-bp+qm-bm) == b*(1-x)**2-3*b*b
            assert bp+bm-bo == b*(3-2*x+3*x*x-7*b)/2
            assert bp+bm-bo >= b*(5+6*x+5*x*x)/8
            assert qo-qm == x*x-b*(1-x)**2/4+b*b
            if b and F(0) < x < F(1):
                assert bm > 0 and bo > 0
                n = 3*b*(x+b)*(1+x)**2-qo*(3*(1-x)**2-2*b)
                expanded = -3*x*x*(1-x)**2+14*b*x*x+14*x*b*b+2*b**3
                assert n == expanded
                if x >= F(1, 5):
                    t = (1-x)**2/x
                    assert t <= tmax
                    assert n == (1-x)**2*x*x*(14*c-3+14*c*c*t+2*c**3*t*t)
                    assert n <= -F(51, 100)*(1-x)**2*x*x
                    assert qo-qm >= F(17, 25)*x*x
                    assert qm/bm < qo/bo
                    ratio_count += 1
            for lam in (F(1), F(3, 2), F(5), F(100)):
                gp, gm, go = qp-lam*bp, qm-lam*bm, qo-lam*bo
                assert go >= gp and go >= gp+gm
                if gm > 0:
                    assert x > F(1, 5) and go >= gm
                native, ordinary = max(F(0), gp)+max(F(0), gm), max(F(0), go)
                assert ordinary >= native
                count += 1
    # Warm case deliberately outside the sufficient cutoff: no universal
    # midpoint dominance is being asserted.
    b, qp, bp, qm, bm, qo, bo = coefficients(F(1, 2), F(1, 4))
    assert qp-3*bp < 0 and qo-3*bo < 0
    assert qm-3*bm == F(3, 512) > 0
    return {"cold_envelope_fixtures": count,
            "cold_positive_denominator_ratio_fixtures": ratio_count,
            "critical_bracket_upper": str(bracket),
            "warm_counterexample_native_utility": str(qm-3*bm),
            "scope": "Analytic all-lambda>=1 dominance for u(1-u)<=1/8; exact constants and finite coefficient fixtures only. No source fit or hardware claim."}


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
