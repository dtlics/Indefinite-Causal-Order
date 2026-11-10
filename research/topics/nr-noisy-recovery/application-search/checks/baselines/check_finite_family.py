"""Check the finite-family Choi-filter identities on fixed random bases.
This does not reprove the published threshold-search theorem.
"""
import numpy as np
from pathlib import Path
import json
rng=np.random.default_rng(1406)
rows=[]
for d in [2,4,8]:
    v=np.eye(d).reshape(-1)/np.sqrt(d)
    phi=np.outer(v,v)
    eye=np.eye(d*d)
    Q=eye-phi
    for trial in range(3):
        U,R=np.linalg.qr(rng.normal(size=(d,d))+1j*rng.normal(size=(d,d)))
        P=[np.outer(U[:,i],U[:,i].conj()) for i in range(d)]
        Pi=sum((np.kron(x.T,x) for x in P),np.zeros((d*d,d*d),complex))
        A=Pi-phi
        assert np.linalg.norm(Pi@Pi-Pi)<1e-10
        assert np.linalg.norm(Pi@phi-phi)<1e-10
        assert np.linalg.norm(A@A-A)<1e-10
        sigma_H=A/(d-1)
        sigma_M=Q/(d*d-1)
        assert abs(np.trace(A@sigma_H)-1)<1e-10
        assert abs(np.trace(A@sigma_M)-1/(d+1))<1e-10
        for p in [.001,.1,1.]:
            JH=(1-p)*phi+p*Pi/d
            JM=(1-p)*phi+p*(phi+eye/d)/(d+1)
            r=p*(1-1/d)
            assert abs(np.trace(Q@JH)-r)<1e-10
            assert abs(np.trace(Q@JM)-r)<1e-10
            assert np.linalg.norm(Q@JH@Q/r-sigma_H)<1e-9
            assert np.linalg.norm(Q@JM@Q/r-sigma_M)<1e-9
        rows.append({'d':d,'trial':trial,'matching_projector_acceptance':float(np.trace(A@sigma_H).real),'model_acceptance':float(np.trace(A@sigma_M).real)})
path=Path(__file__).with_name('finite_family_checks.json')
path.write_text(json.dumps(rows,indent=2))
print('All fixed-basis Choi filtering and candidate-projector identities passed.')
