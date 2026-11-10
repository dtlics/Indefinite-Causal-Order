"""Exact success and conservative error ledgers for logical-qubit packaging."""
from fractions import Fraction as F
from math import comb
import json
from pathlib import Path

def tail(N,k,p):
    a,b=p.numerator,p.denominator
    num=sum(comb(N,j)*a**j*(b-a)**(N-j) for j in range(k))
    return F(num,b**N)

def min_trials(k,p,delta):
    lo=k;hi=max(k,int(2*k/float(p)))
    while tail(hi,k,p)>delta:hi*=2
    while lo<hi:
        mid=(lo+hi)//2
        if tail(mid,k,p)<=delta:hi=mid
        else:lo=mid+1
    return lo

def accepted(eta):
    A=[F(x,64) for x in [3,-2,1,-2,1,-2,3,-2]]
    B=[F(x,64) for x in [16,8,8,8,8,8,0,8]]
    a=b=F(0)
    for j in range(8):
        h=(j^6).bit_count();w=eta**h*(1-eta)**(3-h)
        a+=w*A[j];b+=w*B[j]
    p=a+b;Fbell=(a+b/4)/p
    return p,1-Fbell

def fivecode(e):return 1-(1-e)**5-5*e*(1-e)**4
if __name__=='__main__':
    out={}
    for k in (1,32,100):
        p=F(3,64);N=min_trials(k,p,F(1,100))
        out[f'ideal_{k}_pairs']={'success_probability':str(p),'max_trials':N,'max_contacts':4*N,'abort_probability':float(tail(N,k,p)),'mean_contacts':float(4*k/p)}
    eta=3*F(1,100)**2*F(99,100)+F(1,100)**3
    p,e=accepted(eta);enew=fivecode(e)
    N=min_trials(160,p,F(1,100))
    out['32_purified_pairs']={'raw_readout_error':0.01,'majority_error':str(eta),'acceptance':float(p),'raw_infidelity':float(e),'per_pair_post_code_infidelity_bound':float(enew),'joint_32_infidelity_bound':float(32*enew),'joint_plus_local_budget_005':float(32*enew+F(5,1000)),'max_trials':N,'max_contacts':4*N,'abort_probability':float(tail(N,160,p)),'mean_contacts':float(4*160/p),'assumptions':['three independent classical readout errors per flag, nondemolition repetition','no uncharged coherent controller phase error','ideal four-slot logical switch and ideal output Pauli frames','each slot is a fixed CP qubit channel across its two histories','five-pair one-way error correction plus common local-processing error budget','no loss in this ledger']}
    Path(__file__).with_name('modular_numbers.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
