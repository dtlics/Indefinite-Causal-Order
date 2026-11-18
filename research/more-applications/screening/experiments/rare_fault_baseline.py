"""Ordinary error-sector filtering can outperform weak-noise switch sampling.
This is a classical decision task, not per-run correction of a live payload.
"""
from core import *
from pathlib import Path
import json,math
from scipy.stats import binom
ROOT=Path(__file__).resolve().parent
r=.01;failure=.01
# Known Pauli models: H=(1-r)id+r X, L=(1-r)id+r(X+Z)/2.
p_switch=r*r/2
switch_trials=math.ceil(math.log(failure)/math.log1p(-p_switch))
ordinary_calls=math.ceil(math.log(failure)/math.log1p(-r/2))
# Unknown fixed unitary Pauli axis versus isotropic nonidentity Pauli error.
# Coarse Choi Bell-return filtering accepts each error with rate r.
# Conditional error state is pure versus I_3/3; 2-copy antisymmetric effect:
# probability 0 versus 1/3.
pairs=12;needed=2*pairs
# allocate acquisition failure .002; remaining model failure (2/3)^12<.008.
N=needed
while binom.cdf(needed-1,N,r)>.002:N+=1
# Verify two-error-sector formula for random arbitrary qubit pairs.
rng=np.random.default_rng(1732);Phi=np.outer(np.eye(2).reshape(-1,order='F'),np.eye(2).reshape(-1,order='F'))/2
Q=np.eye(4)-Phi
mx=0;count=0
for _ in range(50):
    A=random_channel(2,4,rng);B=random_channel(2,4,rng)
    JA=choi(A);JB=choi(B)
    ea=float(np.trace(Q@JA).real);eb=float(np.trace(Q@JB).real)
    SA=Q@JA@Q/ea;SB=Q@JB@Q/eb
    predicted=ea*eb*(1-float(np.trace(SA@SB).real))
    actual=metrics(A,B)['p_minus'];mx=max(mx,abs(predicted-actual));count+=1
out={'known_Pauli_example':{'r':r,'required_error':failure,'native_switch_trials':switch_trials,'native_switch_calls':2*switch_trials,'ordinary_single_call_Bell_tests':ordinary_calls,'scope':'these explicit tests, not optimal switched/ordinary complexities'},
'unknown_axis_example':{'fault_rate':r,'retained_error_copies':needed,'mean_calls_to_collect':needed/r,'hard_cap_calls':N,'acquisition_failure':float(binom.cdf(needed-1,N,r)),'conditional_model_miss':(2/3)**pairs,'total_error_upper_bound':float(binom.cdf(needed-1,N,r))+(2/3)**pairs,'switch_minus_model':2*r*r/3,'switch_trials_for_1pct':math.ceil(math.log(.01)/math.log1p(-2*r*r/3))},
'general_error_sector_identity_trials':count,'max_formula_error':float(mx)}
ROOT.joinpath('rare_fault_baseline.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
