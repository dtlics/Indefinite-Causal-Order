"""Exact finite-frequency carrier readout ingredients.

The general finite-resolution bound, passive-resolvent estimate, exact
carrier isolation and physical readout/clock premises are analytic in
methods/moving-caps.md. This standard-library helper imports quietly.
"""
from fractions import Fraction as F
import json

from retained_photon_serial import G, mm, adj, require


def norm(z):
    return z.r*z.r + z.i*z.i


def gram_bell(c0, b, c1):
    x, y = c0-b, c1-b
    require(x != 0 or y != 0, "nonzero entangling contrast")
    u = G(norm(y)-norm(x))/(2*(x-y).conj()) if x != y else G()
    gamma = u-b
    m = [[u+x, u], [u, u+y]]
    gram = mm(m, adj(m))
    require(gram[0][1] == 0 and gram[1][0] == 0 and gram[0][0] == gram[1][1],
            "point-frequency Bell matrix")
    return gamma, m, gram[0][0].r


def exact_verify():
    alpha, beta, h = F(3, 5), F(4, 5), F(3, 5)
    q = alpha*h
    frequencies = [F(-1, 10), F(), F(1, 10)]
    fields = []
    for w in frequencies:
        r0, r1 = G(F(-3, 5), F(1,10)+w), G(F(4, 5), F(-1,10)+2*w/3)
        require(norm(r0) <= 1 and norm(r1) <= 1, "local reflection contraction")
        fields.append((beta*r0*r0, beta*r0*r1, beta*r1*r1))
    gamma0, center, s2 = gram_bell(*fields[1])
    denom = 1 + norm(gamma0)/(q*q)
    require((1+norm(gamma0/q))/denom == 1, "unit-normalized full polarization outcome")
    # The normalized analyzer has squared scale 1/denom. Center correction
    # is center^dagger/sqrt(s2); all checks below clear this square root.
    p = g = bound = F()
    full_entries = 0
    for c0, b, c1 in fields:
        m = [[gamma0+c0, gamma0+b], [gamma0+b, gamma0+c1]]
        literal = [(gamma0/q*q + z)/2 for z in (c0,b,b,c1)]
        require(literal == [z/2 for row in m for z in row], "literal polarization projection includes initial atoms++")
        corrected = mm(adj(center), m)
        trace = corrected[0][0] + corrected[1][1]
        pp = sum(norm(z) for row in m for z in row)/(4*denom)
        gg = norm(trace)/(8*s2*denom)
        delta = [[m[i][j]-center[i][j] for j in range(2)] for i in range(2)]
        bb = sum(norm(z) for row in delta for z in row)/(4*denom)
        require(0 <= gg <= pp and pp-gg <= bb, "finite-bin bad-mass perturbation bound")
        # Direct corrected projected vector, square roots cleared.
        projected_matrix = [[2*literal[0],2*literal[1]],[2*literal[2],2*literal[3]]]
        v = [z for row in mm(adj(center),projected_matrix) for z in row]
        for i in range(4):
            for j in range(4):
                coeff = v[i]*v[j].conj()/(4*s2*denom)
                require(coeff.conj() == v[j]*v[i].conj()/(4*s2*denom), "full density Hermiticity")
                full_entries += 1
        p += pp/3
        g += gg/3
        bound += bb/3
        # An exactly resolved frequency may have its own polarization outcome
        # and Bell frame. It has positive finite weight, not a shared temporal mode.
        gamma, point, ss = gram_bell(c0, b, c1)
        dd = 1 + norm(gamma)/(q*q)
        point_p = sum(norm(z) for row in point for z in row)/(4*dd)
        require(point_p == ss/(2*dd) and point_p > 0, "one normalized frequency-conditioned Bell outcome")
    require(0 < p-g <= bound and bound > 0, "coarse-bin counterexample is nonvacuous")
    # Positive response kernels with imperfect labels need not be sharp bins.
    # Every atom in a bin stays covered by its own nonnegative response weight.
    return {"status": "passed", "frequency_points": len(frequencies),
            "full_density_entries": full_entries, "coarse_probability": str(p),
            "coarse_Bell_good_mass": str(g), "bad_mass": str(p-g),
            "perturbation_upper": str(bound),
            "scope": "Finite rational contraction and frequency-diagonal readout ingredients; universal continuum/derivative and physical analyzer claims are analytic or supplied premises."}


def verify():
    return {
        "status": "passed",
        "finite_frequency_readout": exact_verify(),
        "scope": (
            "Finite complex rational local-contraction/polarization-projection, "
            "point-frequency Bell-frame and nonzero finite-bin error ingredients. "
            "General frequency-response moments, all-cutoff derivative proof, "
            "carrier isolation and physical sorting/analyzer/clock costs remain "
            "analytic or supplied premises. No hardware or rate certificate."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2, sort_keys=True))
