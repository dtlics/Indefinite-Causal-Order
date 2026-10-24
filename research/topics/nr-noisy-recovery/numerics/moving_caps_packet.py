"""Finite-packet, thermal, retained-output CAPS reflection-sector screen.

Exploratory NumPy quadrature; not a complete physical loss/false-herald map.
Model and conventions: ../methods/moving-caps.md. The primary source is
arXiv:2606.26542v1, Eqs. (3)--(6),(12). Both nodes have identical parameters.
"""
import argparse
import json
import numpy as np


class Nodes:
    def __init__(self, nout, ninit, eta=0.17, mu=0.138,
                 g=7.6, kin=0.2, gamma=3.0):
        self.nout, self.ninit = nout, ninit
        self.eta, self.mu, self.g = eta, mu, g
        self.kin, self.gamma = kin, gamma
        self.kex = kin*np.sqrt(1+g*g/(kin*gamma))
        self.kappa = kin+self.kex
        self.ks = np.arange(-(nout-1), ninit)
        self.es = np.arange(-(nout-1), 2*ninit-1)
        b = np.diag(np.sqrt(np.arange(1, nout)), 1)
        vals, vecs = np.linalg.eigh(b+b.T)
        self.d = (vecs*np.cos(eta*vals)) @ vecs.T
        na = np.arange(ninit)[:, None, None, None]
        nb = np.arange(ninit)[None, :, None, None]
        ma = np.arange(nout)[None, None, :, None]
        mb = np.arange(nout)[None, None, None, :]
        self.ka = na-ma-self.ks[0]
        self.kb = nb-mb-self.ks[0]
        self.nb, self.na, self.ma, self.mb = nb, na, ma, mb
        self.da, self.db = (ma == na), (mb == nb)
        self.same = self.da*self.db
        self.energy = ((ma-na)+(mb-nb))*mu

    def dark(self, w):
        return 1-2*self.kex/(self.kappa-1j*w)

    def matrices(self, w):
        """All required incident-frequency shifts and initial columns."""
        e = w+self.es*self.mu
        number = np.arange(self.nout)
        c = 1/(e[:, None]+1j*self.kappa-self.mu*number)
        a = 1/(e[:, None]+1j*self.gamma-self.mu*number)
        middle = self.d.T[None, :, :] @ (a[:, :, None]*self.d[None, :, :])
        r = np.linalg.inv(np.eye(self.nout)[None, :, :]
                          - self.g*self.g*c[:, :, None]*middle)
        cols = np.empty((len(self.ks), self.nout, self.ninit), complex)
        for ni in range(self.ninit):
            cols[:, :, ni] = r[self.ks+ni-self.es[0], :, ni]
        wshift = w+self.ks*self.mu
        s = -2*self.kex/(self.kappa-1j*wshift[:, None, None])*cols
        s += np.eye(self.nout, self.ninit)[None, :, :]
        return s, self.dark(wshift)

    def orders(self, w):
        s, darks = self.matrices(w)
        first = s[-self.ks[0], :, :].T
        a1 = first[:, None, :, None]
        b1 = first[None, :, None, :]
        a0 = self.dark(w)*self.da
        b0 = self.dark(w)*self.db
        bs1 = s[self.ka, self.mb, self.nb]
        ass1 = s[self.kb, self.ma, self.na]
        bs0 = darks[self.ka]*self.db
        ass0 = darks[self.kb]*self.da
        # Spin order: 00,01,10,11. Shape after stacking is 4,niA,niB,mA,mB.
        ab = np.stack((a0*bs0, a0*bs1, a1*bs0, a1*bs1))
        ba = np.stack((b0*ass0, b1*ass0, b0*ass1, b1*ass1))
        return ab, ba


def evaluate(nout=16, ninit=10, sigma=0.1, steps=160,
             temperatures=(0.0, 0.1, 0.25), tau_factors=(0.5, 1.0, 2.0)):
    nodes = Nodes(nout, ninit)
    # Common 2*pi MHz unit; physical tau0=1/(4*mu) microseconds.
    tau0 = np.pi/(2*nodes.mu)
    ids = ["ordinary_AB", "ordinary_BA", "native_plus", "native_minus"]
    for t in tau_factors:
        ids += ["ordinary_AB_filter_"+str(t),
                "ordinary_AB_filter_"+str(t)+"_other_port"]
    shape = (ninit, ninit, nout, nout)
    amps = np.zeros((len(ids),)+shape, complex)
    pv = np.zeros((len(ids), ninit, ninit))
    pv_exchange = np.zeros_like(pv)
    exchange = np.isclose(nodes.energy, 0.0, atol=1e-14) & ~nodes.same
    h_overlap = np.zeros(len(ids))
    h_prob = np.zeros(len(ids))
    ws = np.linspace(-8.5*sigma, 8.5*sigma, steps+1)
    dw = ws[1]-ws[0]
    normalization = 1/np.sqrt(2*np.pi*sigma*sigma)
    parity = np.array((1,-1,-1,1))[:, None, None, None, None]
    max_carrier_diff = 0.0
    mass_quad = 0.0
    for iw, w in enumerate(ws):
        weight = dw*(0.5 if iw in (0, len(ws)-1) else 1.0)
        density = normalization*np.exp(-w*w/(2*sigma*sigma))
        # Input-variable integral: output frequency nu=w-DeltaE.
        overlap = normalization*np.exp(
            -(w*w+(w-nodes.energy)**2)/(4*sigma*sigma))
        ab, ba = nodes.orders(w)
        plus, minus = (ab+ba)/2, (ab-ba)/2
        traces = [np.sum(parity*t, axis=0) for t in (ab,ba,plus,minus)]
        norms = [np.sum(abs(t)**2, axis=0) for t in (ab,ba,plus,minus)]
        for i in range(4):
            amps[i] += weight*overlap*traces[i]
            pv[i] += weight*density*np.sum(norms[i], axis=(-2,-1))/8
            pv_exchange[i] += weight*density*np.sum(norms[i]*exchange,
                                                    axis=(-2,-1))/8
            if i != 3:
                h_overlap[i] += weight*density
                h_prob[i] += weight*density
        for jf, factor in enumerate(tau_factors):
            # G=exp(-i nu tau/2)F after a COMMON mean-arrival change of frame.
            # The corresponding actual delay/cost must be supplied to both.
            for port, trig in enumerate((np.cos, np.sin)):
                it = 4+2*jf+port
                filt = trig((w-nodes.energy)*tau0*factor/2)
                h_filt = trig(w*tau0*factor/2)
                amps[it] += weight*overlap*traces[0]*filt
                pv[it] += weight*density*np.sum(norms[0]*filt*filt,
                                                axis=(-2,-1))/8
                pv_exchange[it] += weight*density*np.sum(
                    norms[0]*filt*filt*exchange, axis=(-2,-1))/8
                h_overlap[it] += weight*density*h_filt
                h_prob[it] += weight*density*h_filt*h_filt
        max_carrier_diff = max(max_carrier_diff,
                               float(np.max(abs((ab-ba)*nodes.same))))
        mass_quad += weight*density
    # Identical resonant nodes: known empty-carrier product sets the paid H-arm
    # amplitude/phase. It is held fixed for every strategy and temperature.
    h = float((nodes.dark(0.0)**2).real)
    if h < 0 or h > 1:
        raise ValueError("invalid passive reference attenuation")
    g_init, p_init, gx_init, px_init, h_arrays, v_arrays = {}, {}, {}, {}, {}, {}
    for i, name in enumerate(ids):
        h_arrays[name] = 4*h*h_overlap[i]*nodes.same
        v_arrays[name] = amps[i]
        amplitude = v_arrays[name] + h_arrays[name]
        g_init[name] = np.sum(abs(amplitude)**2, axis=(-2,-1))/64
        p_init[name] = pv[i]+0.5*h*h*h_prob[i]
        gx_init[name] = np.sum(abs(amps[i])**2*exchange, axis=(-2,-1))/64
        px_init[name] = pv_exchange[i]
    g_init["ordinary_random"] = (g_init[ids[0]]+g_init[ids[1]])/2
    p_init["ordinary_random"] = (p_init[ids[0]]+p_init[ids[1]])/2
    gx_init["ordinary_random"] = (gx_init[ids[0]]+gx_init[ids[1]])/2
    px_init["ordinary_random"] = (px_init[ids[0]]+px_init[ids[1]])/2
    # Exact algebraic completion identities hold before thermal averaging.
    g_guard = float(np.max(abs(g_init["native_plus"]
                       + g_init["native_minus"]-g_init["ordinary_random"])))
    p_guard = float(np.max(abs(p_init["native_plus"]
                       + p_init["native_minus"]-p_init["ordinary_random"])))
    if max(g_guard,p_guard,max_carrier_diff) > 1e-11:
        raise ValueError("order completion/carrier guard failed")
    p_port_guard = 0.0
    ideal_packet_guard = 0.0
    for jf, factor in enumerate(tau_factors):
        port1, port2 = ids[4+2*jf], ids[5+2*jf]
        p_port_guard = max(p_port_guard, float(np.max(abs(
            p_init[port1]+p_init[port2]-p_init["ordinary_AB"]))))
        z = sigma*sigma*(tau0*factor)**2
        ideal_packet_guard = max(ideal_packet_guard,
            abs(h_overlap[4+2*jf]**2-np.exp(-z/4)),
            abs(h_overlap[5+2*jf]),
            abs(h_prob[4+2*jf]-(1+np.exp(-z/2))/2))
    if max(p_port_guard, ideal_packet_guard) > 1e-11:
        raise ValueError("ordinary filter packet/port guard failed")
    results = []
    for nbar in temperatures:
        q = nbar/(1+nbar)
        weights = (1-q)*q**np.arange(ninit)
        weights = weights[:, None]*weights[None, :]
        accepted_thermal_mass = float(np.sum(weights))
        rows = {}
        for name in g_init:
            g = float(np.sum(weights*g_init[name]))
            p = float(np.sum(weights*p_init[name]))
            if g < -1e-13 or g > p+1e-11 or p > accepted_thermal_mass+1e-11:
                raise ValueError("nonphysical finite reflection score")
            # A static polarization phase plate in each accepted output port
            # is a paid, cheap calibrated ordinary/native decoder. It does not
            # change the fixed temporal target or correct motional records.
            if name == "ordinary_random":
                choices = ("ordinary_AB", "ordinary_BA")
            else:
                choices = (name,)
            aa = bb = 0.0
            cc = 0.0j
            for choice in choices:
                avec, bvec = h_arrays[choice], v_arrays[choice]
                wt = weights[:, :, None, None]/len(choices)
                aa += float(np.sum(wt*abs(avec)**2))
                bb += float(np.sum(wt*abs(bvec)**2))
                cc += complex(np.sum(wt*np.conj(avec)*bvec))
            g_opt = (aa+bb+2*abs(cc))/64
            if g_opt > p+1e-11:
                raise ValueError("phase optimized score exceeds accepted mass")
            rows[name] = dict(g=g, p=p, conditional_error=(1-g/p if p else None),
                              g_net_zero_exchange=float(np.sum(weights*gx_init[name])),
                              p_net_zero_exchange=float(np.sum(weights*px_init[name])),
                              g_phase_optimized=float(g_opt),
                              conditional_error_phase_optimized=(1-g_opt/p if p else None),
                              V_output_phase_radians=float(-np.angle(cc)))
        if rows["native_plus"]["g_phase_optimized"] > rows["ordinary_random"]["g_phase_optimized"]+1e-11:
            raise ValueError("phase-optimized completion inequality failed")
        for factor in tau_factors:
            prefix = "ordinary_AB_filter_"+str(factor)
            r1, r2 = rows[prefix], rows[prefix+"_other_port"]
            p = r1["p"]+r2["p"]
            g = r1["g"]+r2["g"]
            g_opt = r1["g_phase_optimized"]+r2["g_phase_optimized"]
            rows[prefix+"_both_ports"] = dict(
                p=p, g=g, g_phase_optimized=g_opt,
                g_net_zero_exchange=r1["g_net_zero_exchange"]+r2["g_net_zero_exchange"],
                p_net_zero_exchange=r1["p_net_zero_exchange"]+r2["p_net_zero_exchange"],
                conditional_error=1-g/p if p else None,
                conditional_error_phase_optimized=1-g_opt/p if p else None,
                interpretation="both output ports retained; static polarization phase calibrated per port")
        results.append(dict(nbar=nbar,
                            omitted_initial_thermal_mass=1-accepted_thermal_mass,
                            rows=rows))
    return dict(scope="reflection sector only; finite oscillator and empirical packet quadrature",
                nout=nout, ninit=ninit, sigma_2pi_MHz=sigma,
                steps=steps, ground_carrier_h_amplitude=h,
                shared_H_arm_rejection_probability=1-h*h,
                tau0_microseconds=1/(4*nodes.mu),
                gaussian_probability_grid_mass=float(mass_quad),
                guards=dict(completion_g=g_guard, completion_p=p_guard,
                            no_motion_change_order_difference=max_carrier_diff,
                            filter_port_probability=p_port_guard,
                            ideal_gaussian_filter=ideal_packet_guard),
                temperatures=results)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--nout", type=int, default=16)
    ap.add_argument("--ninit", type=int, default=10)
    ap.add_argument("--steps", type=int, default=160)
    ap.add_argument("--sigma", type=float, default=0.1)
    args = ap.parse_args()
    print(json.dumps(evaluate(args.nout,args.ninit,args.sigma,args.steps),
                     indent=2, sort_keys=True))
