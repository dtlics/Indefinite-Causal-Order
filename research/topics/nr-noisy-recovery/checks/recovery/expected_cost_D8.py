"""Exact independent audit of the variable-query bound and recovery payoff.

Replays the finite D8 source certificate, then uses only rational arithmetic
to verify the LP-dual coefficients and the actual one-shot payoff optimum.
"""
from __future__ import annotations
if not __debug__:
    raise RuntimeError('Exact proof replay requires Python without -O.')
from pathlib import Path
from fractions import Fraction as F
import json
import sys

HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'algebra'
sys.path.insert(0,str(BASE))


def main():
    from brauer_gate_product_exact_check import verify_file
    path=BASE/'brauer_exact_certificate_D8_g1_10_heralded.json'
    source=verify_file(path)
    data=json.loads(path.read_text())
    lam=F(data['witness']['Lambda']);a=8*F(data['witness']['T'])
    assert lam==F(158531,200000) and a==F(54081027,2560000000)
    k=1-lam;b=3*lam+a-2;delta0=F(1,63);beta=F(1,32)
    assert k>0 and a<=k and 2*lam>=1+beta and b>=delta0
    assert b==F(1021671427,2560000000)
    # After subtracting k*c and using r1>=p1+p2+pT, the p2 and
    # tail coefficients coincide with b; p0,p1 coefficients are smaller.
    assert lam-k+a-k==b and 1-2*k+a-k==b
    assert beta+a-k<=b
    pS=F(11583,12800);qS=F(10405,12800);cS=F(2)
    FS=qS/pS;CS=cS/pS;conditional_bound=b+k*CS
    m=2*k;intersection=m/(1-b)
    assert 0<intersection<1
    # Full vertices of the relaxed (p,q) polygon for c<=2.
    vertices=[(F(0),F(0)),(F(1),F(0)),(F(1),min(F(1),b+m)),
              (intersection,intersection)]
    rewards=[]
    for name,A,B in (('Bell pass/fail',F(2),F(1)),
                     ('private2design state recovery',F(16,9),F(7,9))):
        assert A-B==1 and B/A>=b
        upper=max(A*q-B*p for p,q in vertices)
        assert upper==intersection
        value=A*qS-B*pS
        rewards.append(dict(game=name,A=str(A),B=str(B),ordinary_upper=str(upper),
            ordinary_upper_decimal=float(upper),switch_payoff=str(value),
            switch_payoff_decimal=float(value),strict_gap=str(value-upper),
            strict_gap_decimal=float(value-upper)))
    assert rewards[1]['switch_payoff']=='85399/115200'
    assert rewards[1]['strict_gap']=='43838959061/856113292800'
    pass_probability=(8*qS+pS)/9
    fail_probability=pS-pass_probability
    reject_probability=1-pS
    assert pass_probability+fail_probability+reject_probability==1
    assert pass_probability-fail_probability==F(85399,115200)
    out=dict(status='passed',source_certificate_replayed=source['status'],source_certificate=source,
        arithmetic='Python stdlib exact Fractions',lambda_value=str(lam),intercept_a=str(a),
        resource_slope_k=str(k),resource_intercept_b=str(b),
        LP_coefficient_slacks={'first_query_effect':str(k-a),
            'one_query':str(2*lam-1-beta),'zero_query':str(b-delta0)},
        conditional_bound_at_switch_cost=str(conditional_bound),
        conditional_gap=str(FS-conditional_bound),
        unconditional_expected_query_budget='2',rewards=rewards,
        switch_state_game={'pass':str(pass_probability),'accepted_fail':str(fail_probability),
            'reject':str(reject_probability)},
        hypotheses=['single private unknown data input','private2design state label',
            'no free hidden-frame-correlated advice','all within-instance oracle calls charged',
            'classical ordinary oracle selection','independent memoryless full replacement noise'],
        scope='one-shot expected-payoff bound; no yield floor and no worst-case query cap')
    (HERE/'query_cost_recovery_numeric_review.json').write_text(json.dumps(out,indent=2))
    print(json.dumps(out,indent=2))


if __name__=='__main__':main()
