"""Ordinary serial CAPS Bell factory, retained atoms and both photon ports.

Supplemental NumPy reflection-sector calculation; not a device rate or
complete lost-photon/reset map. Model and conventions are in
../methods/moving-caps.md. Photon detection is legitimate for this
known-input Bell factory. Every final oscillator basis state is traced.
"""
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
NUMERICS = Path(__file__).resolve().parent
EXPECTED = "f2ddea3c287c081b22bd0eccee01b070262dd96e0f8caf14569fcd51cb4da34a"
if hashlib.sha256((NUMERICS/"moving_caps_packet.py").read_bytes()).hexdigest()!=EXPECTED:
    raise ValueError("source kernel changed")
sys.path.insert(0,str(NUMERICS))
import numpy as np
from moving_caps_packet import Nodes


def encode(matrix):
    return [[dict(real=float(z.real),imag=float(z.imag)) for z in row]
            for row in matrix]


def port_score(rho, odd=False):
    perm = (1,0,3,2) if odd else (0,1,2,3)
    corrected = rho[np.ix_(perm,perm)]
    p = float(np.trace(rho).real)
    g_pauli = float((corrected[0,0]+corrected[3,3]
                    +2*corrected[0,3].real).real/2)
    # Optional calibrated local R_z after the known port's Pauli correction.
    phase = float(np.angle(corrected[0,3]))
    g_rz = float((corrected[0,0]+corrected[3,3]
                 +2*abs(corrected[0,3])).real/2)
    if (np.max(abs(rho-rho.conj().T))>1e-12
            or np.min(np.linalg.eigvalsh(rho)) < -1e-12
            or not (-1e-12 <= g_pauli <= g_rz+1e-12 <= p+2e-12)):
        raise ValueError("invalid retained atomic state/score")
    return dict(p=p,g_pauli=g_pauli,g_calibrated_rz=g_rz,
        F_pauli=g_pauli/p if p else None,
        F_calibrated_rz=g_rz/p if p else None,
        Rz_phase_after_Pauli=phase,
        unnormalized_atomic_density=encode(rho))


def run(nout=12,steps=240,sigma=0.01):
    nodes = Nodes(nout,1)
    a = float((nodes.dark(0)**2).real)
    choices = {
        "balanced_H_reference_equal_polarization": dict(
            h=a,alpha=1/math.sqrt(2),beta=1/math.sqrt(2)),
        "unit_H_reference_biased_known_polarization": dict(
            h=1.0,alpha=a/math.sqrt(1+a*a),beta=1/math.sqrt(1+a*a)),
    }
    rho = {key:[np.zeros((4,4),complex),np.zeros((4,4),complex)]
           for key in choices}
    ws = np.linspace(-8.5*sigma,8.5*sigma,steps+1)
    dw = ws[1]-ws[0]
    density_norm = math.erf(8.5/math.sqrt(2))
    vac = np.zeros(nout*nout)
    vac[0] = 1
    p_v = 0.0
    mass = 0.0
    for iw,w in enumerate(ws):
        wt = dw*(.5 if iw in (0,steps) else 1)
        wt *= math.exp(-w*w/(2*sigma*sigma))/(
            math.sqrt(2*math.pi*sigma*sigma)*density_norm)
        ab,_ = nodes.orders(w)
        t = ab[:,0,0,:,:].reshape(4,-1).T
        p_v += wt*float(np.sum(abs(t)**2))/4
        mass += wt
        for key,params in choices.items():
            href = params["alpha"]*params["h"]*vac[:,None]
            vt = params["beta"]*t
            for ip,sign in enumerate((1,-1)):
                amplitudes = (href+sign*vt)/(2*math.sqrt(2))
                rho[key][ip] += wt*(amplitudes.T @ amplitudes.conj())
    rows = {}
    for key,params in choices.items():
        plus = port_score(rho[key][0])
        minus = port_score(rho[key][1],odd=True)
        p = plus["p"]+minus["p"]
        expected_p = params["alpha"]**2*params["h"]**2*mass+params["beta"]**2*p_v
        if abs(p-expected_p)>1e-12:
            raise ValueError("both-port probability completion failed")
        g = plus["g_pauli"]+minus["g_pauli"]
        grz = plus["g_calibrated_rz"]+minus["g_calibrated_rz"]
        rows[key] = dict(configuration=params,plus_port=plus,minus_port=minus,
            total_p=p,total_g_pauli=g,total_g_calibrated_rz=grz,
            total_F_pauli=g/p,total_F_calibrated_rz=grz/p,
            unreflected_or_H_rejected_probability=1-p,
            ideal_motionless_total_p=(2*a*a/(1+a*a) if params["h"]==1 else a*a),
            probability_completion_residual=abs(p-expected_p))
    return dict(nout=nout,steps=steps,sigma=sigma,
        input="known atoms++, ground motion00, one compact normalized Gaussian photon; no coherent motional preparation",
        compact_support=[-8.5*sigma,8.5*sigma],
        density_grid_mass=mass,source_kernel_sha256=EXPECTED,
        target="retained atomic Phi+ after identity/X_B conditioned on the two detected photon X ports",
        scope="source-model reflection sector; all final motion and detected photon frequency traced, all two detector ports counted; no full loss/reset/false-click or clock certificate",
        rows=rows)


if __name__=="__main__":
    print(json.dumps(dict(cases=[run(12,160),run(20,240),run(20,480)]),
                     indent=2,sort_keys=True))
