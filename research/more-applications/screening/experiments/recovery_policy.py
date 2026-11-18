"""Two ideal syndrome-recovery policies have the same scalar signal.
They may act differently on syndromes, but both map into and fix one code.
"""
from core import *
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
rng=np.random.default_rng(18176)
gens=[pauli_string('ZZI'),pauli_string('IZZ')]
sectors=code_projectors(gens);P=sectors[0][1];Lx=pauli_string('XXX')
R=[];S=[]
for bits,proj in sectors:
    c={'00':'III','01':'IIX','10':'XII','11':'IXI'}[''.join(map(str,bits))]
    K=pauli_string(c)@proj;R.append(K)
    S.append(K if bits==(0,0) else Lx@K)
mx=0
for _ in range(30):
    M=rng.normal(size=(8,8))+1j*rng.normal(size=(8,8));rho=M@M.conj().T;rho/=np.trace(rho)
    actual=metrics(R,S,rho)['p_minus'];prediction=(1-np.trace(P@rho).real)/2
    mx=max(mx,abs(actual-prediction))
assert mx<1e-12
out={'trials':30,'max_error':mx,'p_minus_on_code':metrics(R,S,P/2)['p_minus'],'p_minus_maximally_mixed':metrics(R,S)['p_minus'],'different_decoder_verified':bool(np.linalg.norm(choi(R)-choi(S))>0.1),'formula':'p_minus(rho)=(1-Tr(P_code rho))/2, independent of the correction unitaries in the two ideal policies'}
ROOT.joinpath('recovery_policy.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
