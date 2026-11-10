#!/usr/bin/env python3
"""Reproduce a finite, conditional quantum-network workload comparison.

No third-party packages are needed. Exact Fraction arithmetic checks the
probability ledgers, elementary switch error algebra, the five-qubit code,
and conservative entropy bounds. Decimal logarithms provide labeled
numerical estimates, not the analytic proof of the LOCC converse.

This does NOT verify a physical coherent-order device or a universal
advantage over all causally ordered circuits with extra quantum paths.
"""
from __future__ import annotations

from decimal import Decimal, localcontext, ROUND_CEILING
from fractions import Fraction as F
from itertools import product
from math import comb
import json
from pathlib import Path


def as_decimal(x: F) -> Decimal:
    return Decimal(x.numerator) / Decimal(x.denominator)


def h2(x: Decimal) -> Decimal:
    if x in (Decimal(0), Decimal(1)):
        return Decimal(0)
    return -(x*x.ln() + (1-x)*(1-x).ln()) / Decimal(2).ln()


def log_interval(x: F, terms: int = 80) -> tuple[F, F]:
    """Rational interval for ln(x), x>=1, from the atanh series."""
    assert x >= 1 and terms > 0
    z = (x-1)/(x+1)
    low = 2*sum((z**(2*k+1)/F(2*k+1) for k in range(terms)), F(0))
    rem = 2*z**(2*terms+1)/(F(2*terms+1)*(1-z*z))
    return low, low+rem


def mul_pauli(a: str, b: str) -> str:
    """Pauli multiplication modulo its physically irrelevant phase."""
    assert len(a) == len(b)
    table = {('X','Y'):'Z', ('Y','X'):'Z',
             ('X','Z'):'Y', ('Z','X'):'Y',
             ('Y','Z'):'X', ('Z','Y'):'X'}
    return ''.join(y if x == 'I' else x if y == 'I' else 'I' if x == y
                   else table[(x,y)] for x,y in zip(a,b))


def anti(a: str, b: str) -> int:
    return sum(x != 'I' and y != 'I' and x != y for x,y in zip(a,b)) % 2


def verify_code() -> dict:
    generators = ['XZZXI', 'IXZZX', 'XIXZZ', 'ZXIXZ']
    assert all(anti(a,b) == 0 for a in generators for b in generators)
    stabilizers = set()
    for bits in product([0,1], repeat=4):
        s = 'IIIII'
        for bit,g in zip(bits,generators):
            if bit: s = mul_pauli(s,g)
        stabilizers.add(s)
    assert len(stabilizers) == 16
    syndrome = lambda e: tuple(anti(e,g) for g in generators)
    corrector = {syndrome('IIIII'):'IIIII'}
    for site in range(5):
        for p in 'XYZ':
            e = 'I'*site+p+'I'*(4-site)
            sy = syndrome(e)
            assert sy not in corrector
            corrector[sy] = e
    assert len(corrector) == 16
    by_weight = {w: {'total':0, 'logical_success':0} for w in range(6)}
    for tup in product('IXYZ',repeat=5):
        e = ''.join(tup)
        w = sum(p != 'I' for p in e)
        residual = mul_pauli(corrector[syndrome(e)], e)
        assert syndrome(residual) == (0,0,0,0)
        ok = residual in stabilizers
        by_weight[w]['total'] += 1
        by_weight[w]['logical_success'] += int(ok)
        if w <= 1: assert ok
    return {'stabilizer_generators':generators,
            'tested_Pauli_errors':4**5, 'corrected_weight_0_and_1':16,
            'enumeration':by_weight}


def switch_pauli_check(ca: F, cb: F, flag_error: F) -> dict:
    # A and B may have different bias parameters: correction still works.
    wa = {'X':(1+ca)/2,'Y':(1-ca)/2}
    wb = {'X':(1+cb)/2,'Y':(1-cb)/2}
    corrected = {p:F(0) for p in 'IXYZ'}
    plus = F(0)
    for a,pa in wa.items():
        for b,pb in wb.items():
            minus = anti(a,b)
            plus += pa*pb*(1-minus)
            target = mul_pauli(b,a)
            for flip,prob in [(0,1-flag_error),(1,flag_error)]:
                reported_minus = minus ^ flip
                correction = 'Z' if reported_minus else 'I'
                corrected[mul_pauli(correction,target)] += pa*pb*prob
    assert corrected == {'I':1-flag_error,'X':F(0),'Y':F(0),'Z':flag_error}
    assert plus == (1+ca*cb)/2
    return {'plus_probability':float(plus),
            'corrected_Pauli_law':{p:float(v) for p,v in corrected.items()}}


def failure_probability(attempts: int, needed: int, survival: F) -> F:
    return sum((F(comb(attempts,j))*survival**j*(1-survival)**(attempts-j)
                for j in range(needed)),F(0))


def local_noise_countercheck() -> dict:
    # Product-local hidden-axis dephasing vs equally strong local depolarization.
    n,p,k = 32,F(1,100),280
    b = (1-F(2,3)*p)**k
    flag = F(3,16)*(1-b)**2
    miss = (1-flag)**n
    assert miss < F(1,100)
    # 3(ordinary shots) suffices to match one switch shot, all n and k:
    # (1-t)^3 <= 1-2t on 0<=t<=3/16; Jensen then gives
    # (1-t)^(3n) <= (1+(1-4t)^n)/2.
    return {'n':n,'per_qubit_dephasing_probability':float(p),
            'block_length':k,'ordinary_full_register_calls':2*k,
            'false_negative_probability':float(miss),
            'false_positive_probability':0}


def main() -> None:
    with localcontext() as ctx:
        ctx.prec = 70
        c,eta,xi,beta = F(1,1000),F(1,100),F(1,1000),F(1,200)
        raw = eta+2*xi
        purified = 1-(1-raw)**5-5*raw*(1-raw)**4
        delivered_error = purified+beta
        miss = failure_probability(10,5,F(9,10))
        survival=F(9,10)
        expected_trials=sum(sum(F(comb(j,k))*survival**k*(1-survival)**(j-k)
                                for k in range(min(j,4)+1)) for j in range(10))
        assert delivered_error < F(1,100)
        assert miss < F(1,100)
        ln2lo,ln2hi=log_interval(F(2),100)
        ln10lo,ln10hi=log_interval(F(10),100)
        # Rational upper bound on h2(.01):
        # h2(x) <= [x ln(1/x)+x]/ln 2, since -(1-x)ln(1-x)<=x.
        entropy_upper = (F(1,100)*2*ln10hi+F(1,100))/ln2lo
        assert entropy_upper < F(81,1000)
        # g(c) = [sum_{k>=1} c^(2k)/(2k(2k-1))]/ln2
        # <= c^2/[2 ln2 (1-c^2)].
        flux_upper = c*c/(2*ln2lo*(1-c*c))
        conservative_calls = F(99,100)*(1-entropy_upper)/flux_upper
        assert conservative_calls > 1_250_000
        # Tight rational certificate of the displayed integer call bound.
        la_lo,la_hi=log_interval(F(100,99),40)
        target_h_hi=(F(99,100)*la_hi+F(1,100)*2*ln10hi)/ln2lo
        J=6
        series=sum((c**(2*k)/F(2*k*(2*k-1)) for k in range(1,J+1)),F(0))
        remainder=c**(2*J+2)/(F((2*J+2)*(2*J+1))*(1-c*c))
        tight_flux_hi=(series+remainder)/ln2lo
        tight_q_lo=F(99,100)*(1-target_h_hi)/tight_flux_hi
        assert F(1261548) < tight_q_lo < F(1261549)
        cd = as_decimal(c)
        flux = 1-h2((1-cd)/2)
        target_ent = Decimal('.99')*(1-h2(Decimal('.99')))
        q_estimate = target_ent/flux
        sensitivity=[]
        for value in ['0.1','0.03','0.01','0.003','0.001','0.0001']:
            cv=Decimal(value)
            qv=target_ent/(1-h2((1-cv)/2))
            sensitivity.append({'c':value,'ordinary_bound_numeric':str(qv),
                                'integer_ceiling_numeric':int(qv.to_integral_value(rounding=ROUND_CEILING))})
        result={
            'scope':'conditional standard-network vs native-switch resource comparison; not a universal local-query separation',
            'inputs':{'c':str(c),'order_bit_error':str(eta),
                      'postprocessing_half_diamond_each':str(xi),
                      'whole_local_processing_error':str(beta),
                      'independent_heralded_survival':'.9'},
            'switch':{'max_trials':10,'max_elementary_calls':20,'raw_error_bound':float(raw),
                      'code_error_bound_exact':str(purified),'code_error_bound':float(purified),
                      'delivered_infidelity_bound':float(delivered_error),
                      'delivered_fidelity_lower':float(1-delivered_error),
                      'abort_probability_exact':str(miss),'delivery_probability':float(1-miss),
                      'expected_elementary_calls_upper':str(F(10)/F(9,10)),
                      'expected_elementary_calls_exact':str(2*expected_trials),
                      'expected_elementary_calls':float(2*expected_trials)},
            'ordinary':{'flux_ebits_per_call_numeric':str(flux),
                        'call_lower_bound_numeric':str(q_estimate),
                        'integer_ceiling_numeric':int(q_estimate.to_integral_value(rounding=ROUND_CEILING)),
                        'rationally_certified_lower_bound':float(conservative_calls),
                        'certified_more_than_1250000':True,
                        'sharp_rational_lower_bound':float(tight_q_lo),
                        'integer_minimum_certified':1261549,
                        'delivery_probability_upper_at_20_calls_F99_numeric':str(Decimal(20)*flux/(1-h2(Decimal('.99'))))},
            'Pauli_switch':switch_pauli_check(c,c,eta),
            'unequal_parameter_check':switch_pauli_check(c,-F(7,10000),eta),
            'code':verify_code(),
            'sensitivity':sensitivity,
            'local_product_noise_baseline':local_noise_countercheck(),
            'not_verified':['physical coherent-order interface','noiseless-bypass exclusion for a specific apparatus',
                            'measured channel/noise parameters','full resource equivalence to arbitrary coherent-path optical circuits',
                            'independent external proof review']
        }
        out=Path(__file__).with_name('verification.json')
        out.write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps({k:result[k] for k in ['switch','ordinary','Pauli_switch','local_product_noise_baseline']},indent=2))
        print('PASS: exact probability bounds, rational entropy bounds, and all 1024 code errors checked.')
        print('These checks do not establish the listed physical assumptions.')

if __name__ == '__main__':
    main()
