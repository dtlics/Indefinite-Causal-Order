"""Exploratory ordinary carrier Bell-analyzer source witnesses.

The two finite virtual-motion cutoffs are not oscillator-tail or physical
filter/analyzer certificates. This source-only main uses the pinned sibling
moving_caps_packet kernel; exact rational checks live in a separate helper.
Import is quiet, and no function writes files.
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


def source_witness(nout=12, steps=160, sigma=.01):
    nodes = Nodes(nout, 1)
    width = 8.5 * sigma
    require(width < nodes.mu, "carrier rejects every nonzero standing-wave final motion")
    ws = np.linspace(-width, width, steps + 1)
    dw = ws[1] - ws[0]
    weights = np.exp(-ws * ws / (2 * sigma * sigma)) / (math.sqrt(2 * math.pi) * sigma)
    weights *= dw / math.erf(width / (math.sqrt(2) * sigma))
    weights[[0, -1]] /= 2
    r0 = np.array([nodes.dark(w) for w in ws])
    r1 = np.array([nodes.matrices(w)[0][-nodes.ks[0], 0, 0] for w in ws])
    a = float((nodes.dark(0) ** 2).real)
    out = []
    for name, alpha, beta, h in [
            ("balanced_photon_masked_H", 1 / math.sqrt(2), 1 / math.sqrt(2), a),
            ("known_photon_unit_H", a / math.sqrt(1 + a * a), 1 / math.sqrt(1 + a * a), 1.0)]:
        fields = np.array((beta * r0 ** 2, beta * r0 * r1, beta * r1 ** 2))
        c0, b, c1 = fields @ weights
        x, y = c0 - b, c1 - b
        d = x - y
        if abs(d) > 1e-30:
            e = d / abs(d)
            u = -e * np.real((x + y) * np.conj(e)) / 2
        else:
            u = 0j
        gamma = u - b
        h0 = abs(alpha * h) ** 2 * np.sum(weights)
        analyzer_norm = 1 + abs(gamma) ** 2 / h0
        matrix = np.array(((u + x, u), (u, u + y)))
        gram = matrix @ matrix.conj().T
        defect = float(np.linalg.norm(gram - np.eye(2) * np.trace(gram) / 2))
        probability = float(np.trace(gram).real / (4 * analyzer_norm))
        require(defect < 1e-13 and probability > 0, "source pure Bell witness")
        # Direct even-parity constraint: dfield=V00-V11, a=V00-V01.
        dfield, afield, bfield = fields[0] - fields[2], fields[0] - fields[1], fields[1]
        inner = lambda p, q: np.sum(weights * np.conj(p) * q)
        dd = inner(dfield, dfield).real
        av = afield - dfield * inner(dfield, afield) / dd if dd > 1e-30 else afield
        bv = bfield - dfield * inner(dfield, bfield) / dd if dd > 1e-30 else bfield
        even_q = inner(av, av).real - abs(inner(bv, av)) ** 2 / (h0 + inner(bv, bv).real)
        out.append({"configuration": name, "alpha": alpha, "beta": beta, "H_amplitude": h,
                    "one_mode_probability": probability, "MMdagger_defect": defect,
                    "analyzer_norm_before_scaling": float(analyzer_norm),
                    "u": [float(u.real), float(u.imag)], "gamma": [float(gamma.real), float(gamma.imag)],
                    "direct_even_Gram_probability": float(max(0, even_q / 2))})
    return {"nout": nout, "steps": steps, "sigma": sigma, "input_packet_mass": float(np.sum(weights)),
            "r1_zero": [float(nodes.matrices(0)[0][-nodes.ks[0], 0, 0].real),
                        float(nodes.matrices(0)[0][-nodes.ks[0], 0, 0].imag)],
            "configurations": out,
            "scope": "Finite virtual-motion cutoff and quadrature witness only. Exact carrier isolation is analytic under ground/standing-wave/compact-band assumptions; physical filter/analyzer/cooling/calibration costs are unprovided."}


def main():
    print(json.dumps({
        "status": "passed",
        "source_kernel_sha256": KERNEL_SHA256,
        "cases": [source_witness(12), source_witness(16)],
        "scope": (
            "Two finite virtual-motion cutoff witnesses at 160 packet intervals. "
            "Final carrier isolation is analytic under the stated ground, parity "
            "and compact-band hypotheses. Refinement and Gram residuals are "
            "empirical, not output-tail, device, hardware-fidelity or clock bounds."
        ),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
