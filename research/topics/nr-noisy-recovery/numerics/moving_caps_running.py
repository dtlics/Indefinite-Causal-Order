"""Bounded source-geometry comparison; see ../methods/moving-caps.md.

Running-wave d=exp(i eta Q), arXiv:2606.26542v1 Eqs. (9)--(11).
The nominal numbers come from a standing-wave apparatus; this is the
source-style theoretical geometry comparison, not a measured running node.
No independent eta/mu tuning, changed coupling/loss fit or reverse-route
identification is claimed. A reversed wave generally changes d to d^dagger.
"""
import argparse
import json
import numpy as np
import moving_caps_packet as standing


class RunningNodes(standing.Nodes):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        b = np.diag(np.sqrt(np.arange(1, self.nout)), 1)
        vals, vecs = np.linalg.eigh(b+b.T)
        self.d = (vecs*np.exp(1j*self.eta*vals)) @ vecs.T

    def matrices(self, w):
        # The sole kernel difference beyond d is the true complex adjoint.
        e = w+self.es*self.mu
        number = np.arange(self.nout)
        c = 1/(e[:, None]+1j*self.kappa-self.mu*number)
        a = 1/(e[:, None]+1j*self.gamma-self.mu*number)
        middle = self.d.conj().T[None, :, :] @ (
            a[:, :, None]*self.d[None, :, :])
        r = np.linalg.inv(np.eye(self.nout)[None, :, :]
                          - self.g*self.g*c[:, :, None]*middle)
        cols = np.empty((len(self.ks), self.nout, self.ninit), complex)
        for ni in range(self.ninit):
            cols[:, :, ni] = r[self.ks+ni-self.es[0], :, ni]
        wshift = w+self.ks*self.mu
        s = -2*self.kex/(self.kappa-1j*wshift[:, None, None])*cols
        s += np.eye(self.nout, self.ninit)[None, :, :]
        return s, self.dark(wshift)


def evaluate(nout=20, ninit=12, sigma=0.01, steps=240):
    original = standing.Nodes
    try:
        standing.Nodes = RunningNodes
        result = standing.evaluate(nout,ninit,sigma,steps,
                                   tau_factors=(1.0,2.0,4.0))
    finally:
        standing.Nodes = original
    result["geometry"] = "running-wave theoretical comparison at fixed source nominal parameters"
    result["tau0_microseconds"] *= 2
    result["physical_filter_delays"] = "labels are factors of running first-sideband delay pi/mu"
    for temperature in result["temperatures"]:
        rows = {}
        for name, row in temperature["rows"].items():
            if name.startswith("ordinary_AB_filter_"):
                prefix, rest = name.rsplit("filter_",1)
                number, sep, suffix = rest.partition("_")
                name = prefix+"filter_"+str(float(number)/2)+(sep+suffix if sep else "")
            rows[name] = row
        temperature["rows"] = rows
    return result


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--nout",type=int,default=20)
    ap.add_argument("--ninit",type=int,default=12)
    ap.add_argument("--sigma",type=float,default=0.01)
    ap.add_argument("--steps",type=int,default=240)
    args = ap.parse_args()
    print(json.dumps(evaluate(args.nout,args.ninit,args.sigma,args.steps),
                     indent=2,sort_keys=True))
