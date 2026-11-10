"""Reproduce algebraic sanity checks used in the application audit.

This checks finite numerical identities and an ordinary local-noise test.
It does not verify the repository's adaptive Haar lower bound or any
microscopic physical implementation of a quantum switch.
Requires numpy. Run: python check_identities.py
"""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np


def run() -> dict:
    rng = np.random.default_rng(20261104)
    checked = []
    for d in (2, 4, 8, 16):
        raw = rng.normal(size=(d,d)) + 1j*rng.normal(size=(d,d))
        U, R = np.linalg.qr(raw)
        U = U @ np.diag(np.exp(-1j*np.angle(np.diag(R))))
        projectors = [np.outer(U[:,i], U[:,i].conj()) for i in range(d)]
        def dephase(rho):
            return sum((P@rho@P for P in projectors), np.zeros_like(rho))
        def model(rho):
            return (rho + np.trace(rho)*np.eye(d))/(d+1)
        rho = projectors[0]
        fe = sum(abs(np.trace(P))**2 for P in projectors)/d**2
        ret_H = float(np.trace(rho@dephase(rho)).real)
        ret_M = float(np.trace(rho@model(rho)).real)
        witness_distance = float(np.linalg.svd(dephase(rho)-model(rho),compute_uv=False).sum()/2)
        assert abs(fe-1/d)<1e-12
        assert abs(ret_H-1)<1e-12
        assert abs(ret_M-2/(d+1))<1e-12
        assert abs(witness_distance-(d-1)/(d+1))<1e-12
        checked.append({'dimension':d,'entanglement_fidelity':float(fe),
                        'known_eigenstate_return_H':ret_H,
                        'known_eigenstate_return_model':ret_M,
                        'trace_distance_witness':witness_distance})
    for d in (2,4,32,1024):
        for p in (.001,.01,.2,1.):
            for m in (1,2,10,100,1000):
                r=(1-p)**m
                a=(1-p*d/(d+1))**m
                gap=(1+d*r*r)/(d+1)-a*a
                assert -1e-12 <= gap <= 1/(d+1)+1e-12
    n,p,k=32,.01,280
    b=(1-2*p/3)**k
    event=3*(1-b)**2/16
    miss=(1-event)**n
    assert miss<.01
    return {'fixed_basis_checks':checked,
            'local_noise_ordinary_test':{'qubits':n,'noise_strength':p,
                  'block_length':k,'total_calls':2*k,'miss_probability':miss},
            'scope':'Numerical identity checks, not a hardness or physical-implementation proof.'}

if __name__=='__main__':
    data=run()
    path=Path(__file__).with_name('reproducible_checks.json')
    path.write_text(json.dumps(data,indent=2))
    print(json.dumps(data,indent=2))
