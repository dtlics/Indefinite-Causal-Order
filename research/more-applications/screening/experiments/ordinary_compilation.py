"""An orthogonal known-unitary mixture in one arm suffices for 1+1 ordinary simulation.
A Bell probe samples the unknown mixing probabilities exactly. Conditional on
its result, known coherent unitary control around the other actual box supplies
the switch. This is query-efficient; synthesis/control cost is separate.
"""
from core import *
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
rng=np.random.default_rng(9181)
rows=[]
for n in [1,2,3]:
    d=2**n
    max_choi=max_sampler=0.
    for _ in range(10):
        Ps=[pauli_string(''.join(s)) for s in itertools.product('IXYZ',repeat=n)]
        p=rng.dirichlet(np.ones(len(Ps)))
        # Known arbitrary unitary after the Pauli: still orthogonal Choi vectors.
        U,_=np.linalg.qr(rng.normal(size=(d,d))+1j*rng.normal(size=(d,d)))
        ops=[U@P for P in Ps]
        A=[np.sqrt(q)*P for q,P in zip(p,ops)]
        B=random_channel(d,3,rng)
        JA=choi(A)
        measured=np.array([np.vdot(vec(P)/np.sqrt(d),JA@(vec(P)/np.sqrt(d))).real for P in ops])
        max_sampler=max(max_sampler,np.max(abs(measured-p)))
        W=[];L=[]
        for q,P in zip(p,ops):
            C0=np.block([[P,np.zeros_like(P)],[np.zeros_like(P),np.eye(d)]])
            C1=np.block([[np.eye(d),np.zeros_like(P)],[np.zeros_like(P),P]])
            for b in B:
                W.append(np.sqrt(q)*np.block([[b@P,np.zeros_like(P)],[np.zeros_like(P),P@b]]))
                L.append(np.sqrt(q)*C1@np.kron(I2,b)@C0)
        max_choi=max(max_choi,np.linalg.norm(choi(W)-choi(L)))
    rows.append({'n':n,'dimension':d,'pairs':10,'max_Bell_sampling_error':float(max_sampler),'max_full_switch_Choi_error':float(max_choi)})
    assert max_choi<1e-12 and max_sampler<1e-12
ROOT.joinpath('ordinary_compilation.json').write_text(json.dumps({'claim':'one known orthogonal-unitary-mixture arm, unknown weights, other arm arbitrary unknown CPTP: one ordinary query to each suffices for exact ideal-circuit full-switch simulation','checks':rows,'scope':'Independent memoryless channel uses; entangled probes and known controls allowed. Full output channel simulated, not just scalar. Physical mandatory-noise or resource-restricted architectures need separate access/cost accounting.'},indent=2))
print(json.dumps(rows,indent=2))
