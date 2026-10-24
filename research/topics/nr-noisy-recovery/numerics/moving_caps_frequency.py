"""Optional finite-resolution ordinary carrier readout witnesses.

Two finite virtual-motion cutoffs and sampled packet integrals are not an
oscillator-tail, detector-resolution, hardware-confidence or clock certificate.
The numerical witness uses only the pinned sibling scattering kernel.
Import is quiet and functions write no files.
"""
import hashlib
import json
import math
from pathlib import Path

import numpy as np

KERNEL_SHA256 = "f2ddea3c287c081b22bd0eccee01b070262dd96e0f8caf14569fcd51cb4da34a"


def require(test, message):
    if not test:
        raise ValueError(message)


require(hashlib.sha256(Path(__file__).with_name("moving_caps_packet.py").read_bytes()).hexdigest()
        == KERNEL_SHA256, "pinned sibling source kernel")
from moving_caps_packet import Nodes


def source_witness(nout=12, steps=640, sigma=.01):
    nodes = Nodes(nout, 1)
    width = 8.5*sigma
    require(width < nodes.mu, "exact final carrier isolation under source ground/parity assumptions")
    ws = np.linspace(-width, width, steps+1)
    dw = ws[1]-ws[0]
    weights = np.exp(-ws*ws/(2*sigma*sigma))*dw/(math.sqrt(2*math.pi)*sigma)
    weights /= math.erf(width/(math.sqrt(2)*sigma))
    weights[[0, -1]] /= 2
    r0 = np.array([nodes.dark(w) for w in ws])
    r1 = np.array([nodes.matrices(w)[0][-nodes.ks[0], 0, 0] for w in ws])
    a = float((nodes.dark(0)**2).real)

    def raw_at(w):
        d = nodes.dark(w)
        b = nodes.matrices(w)[0][-nodes.ks[0], 0, 0]
        return np.array(((d*d, d*b), (d*b, b*b)))

    def unitary_correction(m):
        left, _, right = np.linalg.svd(m)
        return right.conj().T @ left.conj().T

    def design(field, q):
        c0, b, c1 = field[0, 0], field[0, 1], field[1, 1]
        x, y = c0-b, c1-b
        dif = x-y
        u = ((abs(y)**2-abs(x)**2)/(2*np.conj(dif))) if abs(dif)>1e-30 else 0j
        gamma = u-b
        denom = 1+abs(gamma/q)**2
        center = (gamma*np.ones((2, 2))+field)/math.sqrt(denom)
        require(np.linalg.norm(center@center.conj().T-np.eye(2)*np.linalg.norm(center)**2/2)<1e-12,
                "pointwise source Bell design")
        return gamma, denom, unitary_correction(center)

    out = []
    for name, alpha, beta, h in [
        ("balanced_masked_H",1/math.sqrt(2),1/math.sqrt(2),a),
        ("known_bias_unit_H",a/math.sqrt(1+a*a),1/math.sqrt(1+a*a),1.)]:
        q = alpha*h
        field = beta*np.array(((r0*r0,r0*r1),(r0*r1,r1*r1))).transpose(2,0,1)
        gamma_fixed, denom_fixed, _ = design(beta*raw_at(0),q)
        configs = []
        for bins in [1,2,4,8,16,32]:
            edges = np.linspace(-width,width,bins+1)
            labels = np.minimum(np.searchsorted(edges,ws,side="right")-1,bins-1)
            for adapt_polar in [False,True]:
                p = g = error_bound = lipschitz_bound = F0 = 0.
                for j in range(bins):
                    centerw = float(np.sum(ws[labels==j]*weights[labels==j])/np.sum(weights[labels==j]))
                    centerfield = beta*raw_at(centerw)
                    if adapt_polar:
                        gamma,denom,correction = design(centerfield,q)
                    else:
                        gamma,denom = gamma_fixed,denom_fixed
                        correction = unitary_correction((gamma*np.ones((2,2))+centerfield)/math.sqrt(denom))
                    ms = (gamma*np.ones((2,2))[None,:,:]+field[labels==j])/math.sqrt(denom)
                    corrected = np.einsum("ij,kjl->kil",correction,ms)
                    wj = weights[labels==j]
                    norm2 = np.sum(abs(ms)**2,axis=(1,2))
                    traces = np.trace(corrected,axis1=1,axis2=2)
                    p += float(np.sum(wj*norm2/4))
                    g += float(np.sum(wj*abs(traces)**2/8))
                    targetcenter = (gamma*np.ones((2,2))+centerfield)/math.sqrt(denom)
                    center_bad = np.linalg.norm(correction@targetcenter-np.eye(2)*np.trace(correction@targetcenter)/2)
                    delta = ms-targetcenter
                    # A true center Bell design yields the exact finite-bin bound;
                    # the fixed-polarization construction has additional Schmidt error.
                    delta_norm = np.linalg.norm(delta,axis=(1,2))
                    error_bound += float(np.sum(wj*(center_bad+delta_norm)**2/4))
                    l0=2*nodes.kex/nodes.kappa**2
                    l1=2*nodes.kex/min(nodes.kappa,nodes.gamma)**2
                    derivative_square=beta*beta*(4*l0*l0+2*(l0+l1)**2+4*l1*l1)/denom
                    lipschitz_bound+=float(np.sum(wj*(center_bad+math.sqrt(derivative_square)*abs(ws[labels==j]-centerw))**2/4))
                    F0 = max(F0,center_bad)
                require(g <= p+1e-13 and p-g <= error_bound+1e-13,"actual finite-bin residual bound")
                require(p-g <= lipschitz_bound+1e-13,"all-cutoff Lipschitz envelope on finite source witness")
                configs.append({"bins":bins,"bin_width_kHz":2*width*1000/bins,
                    "per_bin_polarization":adapt_polar,"probability":p,"conditional_Bell_fidelity":g/p,
                    "bad_mass":p-g,"finite_bin_residual_bound":error_bound,
                    "all_cutoff_Lipschitz_bad_mass_bound":lipschitz_bound,
                    "conditional_F_lower_from_measured_p":max(0.,1-lipschitz_bound/p),
                    "center_non_Bell_amplitude_max":F0})
        fixed_ms=(gamma_fixed*np.ones((2,2))[None,:,:]+field)/math.sqrt(denom_fixed)
        fixed_norm2=np.sum(abs(fixed_ms)**2,axis=(1,2))
        fixed_det=np.linalg.det(fixed_ms)
        perfect_frequency_local_only_p=float(np.sum(weights*fixed_norm2/4))
        perfect_frequency_local_only_g=float(np.sum(weights*(fixed_norm2+2*abs(fixed_det))/8))
        # Two fixed ordinary polarization ports, each read frequency and use a
        # center-bin local Procrustes frame. Both outputs count separately.
        both = []
        for bins in [1,4,16]:
            edges = np.linspace(-width,width,bins+1)
            labels = np.minimum(np.searchsorted(edges,ws,side="right")-1,bins-1)
            p=g=0.
            for j in range(bins):
                wj=weights[labels==j]
                centerw=float(np.sum(ws[labels==j]*wj)/np.sum(wj))
                centerfield=beta*raw_at(centerw)
                for sign in [-1,1]:
                    ms=(q*np.ones((2,2))[None,:,:]+sign*field[labels==j])/math.sqrt(2)
                    correction=unitary_correction((q*np.ones((2,2))+sign*centerfield)/math.sqrt(2))
                    corrected=np.einsum("ij,kjl->kil",correction,ms)
                    p+=float(np.sum(wj*np.sum(abs(ms)**2,axis=(1,2))/4))
                    g+=float(np.sum(wj*abs(np.trace(corrected,axis1=1,axis2=2))**2/8))
            both.append({"bins":bins,"probability_both_ports":p,"conditional_Bell_fidelity":g/p})
        out.append({"configuration":name,"alpha":alpha,"beta":beta,"h":h,
                    "single_port":configs,"fixed_polarization_both_ports":both,
                    "fixed_polarization_perfect_frequency_local_unitary_limit":{
                        "p":perfect_frequency_local_only_p,
                        "F":perfect_frequency_local_only_g/perfect_frequency_local_only_p}})
    return {"nout":nout,"steps":steps,"sigma_2pi_MHz":sigma,"packet_mass":float(sum(weights)),
            "cases":out,"scope":"Finite virtual-motion cutoff and sampled packet integrals only. MR2 analytically supplies the all-cutoff Lipschitz constant, but source design/correction values, quadrature moments and accepted p here are finite witnesses, not a hardware confidence/tail/measurement-resolution/time certificate."}


def main():
    print(json.dumps({
        "status": "passed",
        "source_kernel_sha256": KERNEL_SHA256,
        "cases": [source_witness(12), source_witness(16)],
        "scope": (
            "Finite virtual-motion cutoffs 12/16 with 640 packet intervals. "
            "All-cutoff Lipschitz constants follow analytically from MR2, but "
            "center coefficients, packet moments and accepted probabilities "
            "are empirical witnesses. No continuum quadrature, virtual-tail, "
            "physical frequency-bin, insertion-loss or deadline certificate."
        ),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
