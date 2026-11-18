"""Verify the exact self-switch instrument and code-aware flag-gain bounds."""
import json
import numpy as np
from core import *
from nonpauli_qec import code_ad4,product_noise
from retraction_tests import switch

def trace_distance(a,b):return float(np.sum(abs(np.linalg.eigvalsh((a-b+(a-b).conj().T)/2)))/2)

def main():
 rng=np.random.default_rng(41836);rows=[]
 plusc=np.array([1,1])/np.sqrt(2)
 for d in [2,3,4]:
  for r in [2,3,4]:
   for rep in range(6):
    A=random_channel(d,r,rng);plus,minus=switch_branches(A,A)
    decomposed=[np.kron(I2,k) for k in plus]+[np.kron(Z,k) for k in minus]
    residual=np.linalg.norm(choi(switch(A,A))-choi(decomposed))
    E=effect(minus);w,V=np.linalg.eigh(E);phi=np.kron(plusc,V[:,-1]);rho=np.outer(phi,phi.conj())
    true=apply(switch(A,A),rho);ordinary=apply([np.kron(I2,k) for k in compose(A,A)],rho)
    attained=trace_distance(true,ordinary)
    assert abs(attained-w[-1])<1e-11 and residual<1e-11
    rows.append({'d':d,'rank':r,'decomposition_residual':float(residual),'pmax':float(w[-1]),'attained_distance':attained})
 ad=[];V=code_ad4()
 for gamma in [.001,.003,.01,.03,.1]:
  A=product_noise(amplitude(gamma),4);minus=switch_branches(A,A)[1]
  E=effect(minus);p=float(np.trace(V.conj().T@E@V).real/2)
  f=1-gamma*(1-np.sqrt(1-gamma))**2
  exact=(1-(1+f**4)/4-f**2/2)/2
  assert abs(exact-p)<1e-12
  ad.append({'gamma':gamma,'flag_probability_Bell':p,'formula':float(exact),'leading_gamma3_over4':gamma**3/4})
 opt=json.load(open('decoder_optimized_results.json'))
 baselines=[]
 for row in opt:
  g=row['g']
  simple=1-g+g*g/4 if row['family']=='cool_heat' else (2-g+2*(1-g)**1.5)/4
  assert simple>row['switch_coherent']['upper']
  baselines.append({'g':g,'family':row['family'],'ordinary_one_physical_qubit_fidelity':simple,'best_fixed_dualrail_switch_upper':row['switch_coherent']['upper']})
 open('self_switch_bound_results.json','w').write(json.dumps({'random_cases':rows,'AD_code_cases':ad,'encoding_checks':baselines},indent=2))
 print('PASS',len(rows),'full-instrument identities; AD polynomial; eight ordinary encoding comparisons')
if __name__=='__main__':main()
