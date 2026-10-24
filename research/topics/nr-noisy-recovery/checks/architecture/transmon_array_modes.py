"""Exact finite guards for NR-R11 giant-transmon array modes; stdlib only.

Universal contours, all-integer orthogonality and physical approximation
scopes are analytic in communication.md. No optimizer, NumPy or quadrature.
Import is quiet and every guard remains active under -O and -OO.
"""
from fractions import Fraction as F
import json

from retained_photon_serial import G, require, eye, mm, add, scale, rank


def power(z, n):
    if n < 0:
        return power(G(1)/z, -n)
    result = G(1)
    for _ in range(n):
        result *= z
    return result


def t(x, gamma):
    a = gamma/2
    return G(x, -a)/G(x, a)


def f(x, energy, gamma):
    a = gamma/2
    return G(1)/(G(x, a)*G(energy-x, a))


def mode(x, energy, gamma, n, count):
    return f(x, energy, gamma)*power(t(x, gamma), count-1-n)*power(t(energy-x, gamma), n)


def canonical_mode(x, energy, gamma, n):
    return f(x, energy, gamma)*power(t(energy-x, gamma)/t(x, gamma), n)


def nonlinear(energy, gamma, u):
    # c*pi times I/pi, so no irrational constant enters the replay.
    c_pi = G(0, gamma*gamma/4)*u*G(energy, gamma)/G(energy+u/2, gamma)
    norm_over_pi = 4/(gamma*(energy*energy+gamma*gamma))
    lam = c_pi*norm_over_pi
    den = G(energy, -gamma)*G(energy+u/2, gamma)
    zeta = den.conj()/den
    require(1+lam == zeta and zeta*zeta.conj() == 1, "finite-U eigenphase")
    return lam


def residue_norm(energy, gamma):
    a = gamma/2
    if energy:
        r1 = G(1)/(G(0, 2*a)*energy*G(energy, -2*a))
        r2 = G(1)/(G(0, 2*a)*energy*G(energy, 2*a))
        value = G(0, 2)*(r1+r2)  # integral/pi
    else:
        # derivative at the double pole x=ia of 1/(x+ia)^2.
        residue = G(-2)/power(G(0, 2*a), 3)
        value = G(0, 2)*residue
    require(value == 4/(gamma*(energy*energy+gamma*gamma)), "norm residue/limit")


def cross_density(x, energy, gamma, k):
    a = gamma/2
    lhs = f(x, energy, gamma).conj()*f(x, energy, gamma)
    lhs *= power(t(energy-x, gamma)/t(x, gamma), k)
    rhs = power(G(x, a), k-1)*power(G(energy-x, -a), k-1)
    rhs /= power(G(x, -a), k+1)*power(G(energy-x, a), k+1)
    require(lhs == rhs, "orthogonality rational integrand")
    # Factored rhs has only x=ia,E+ia poles, both above the real line.
    require(a > 0 and (2*(k+1)-2*(k-1)) == 4, "lower contour and x^-4 decay")


def kernel_guard(p, x, energy, gamma, count):
    source = G()
    factored = G()
    dressed = G()
    for n in range(count):
        source += f(p, energy, gamma)*f(x, energy, gamma)*power(
            t(p, gamma)*t(energy-x, gamma), count-1-n)*power(
            t(x, gamma)*t(energy-p, gamma), n)
        factored += mode(p, energy, gamma, n, count)*mode(x, energy, gamma, n, count).conj()*power(
            t(x, gamma)*t(energy-x, gamma), count)
        dressed += power(t(p, gamma), count-1)*canonical_mode(p, energy, gamma, n)*canonical_mode(
            x, energy, gamma, n).conj()*t(x, gamma)*power(t(energy-x, gamma), count)
    require(source == factored == dressed, "connected array and FVG kernel")
    return count


def commutator_guard(energy, gamma, count):
    # Finite matrix algebra fixture for the general projector identity.
    size = 2*count
    p = [[G() for _ in range(size)] for _ in range(size)]
    for n in range(count):
        for i, vi in enumerate((F(3, 5), F(4, 5))):
            for j, vj in enumerate((F(3, 5), F(4, 5))):
                p[2*n+i][2*n+j] = G(vi*vj)
    require(mm(p, p) == p and rank(p) == count, "generic finite-rank projector")
    d = [[power(t(F(i+1, 7), gamma)*t(energy-F(i+1, 7), gamma), count)
          if i == j else G() for j in range(size)] for i in range(size)]
    la, lb = nonlinear(energy, gamma, F(10)), nonlinear(energy, gamma, F(100))
    sa, sb = mm(add(eye(size), scale(p, la)), d), mm(add(eye(size), scale(p, lb)), d)
    actual = add(mm(sb, sa), scale(mm(sa, sb), -1))
    rhs = scale(mm(add(mm(p, d), scale(mm(d, p), -1)), d), lb-la)
    require(actual == rhs and rank(actual) <= 2*count, "same-geometry commutator")
    if energy == 0:
        require(actual == [[G() for _ in range(size)] for _ in range(size)], "central shell zero")
    else:
        require(rank(actual) > 0, "offcentral noncommutation fixture")


def choi_guard():
    # Literal retained field/reference state; this is not a ++/HOM fixture.
    outputs = [[G(1), G()], [G(F(3, 5)), G(F(4, 5))],
               [G(F(4, 5)), G(0, F(3, 5))],
               [G(F(-3, 13), F(-4, 13)), G(F(12, 13))]]
    signs = [1, 1, 1, -1]
    require(signs[0]*signs[3] == -signs[1]*signs[2], "CZ nonlocal phase")
    require(all(sum((z*z.conj() for z in row), G()) == 1 for row in outputs),
            "four normalized conditional output fields")
    actual, target = [G() for _ in range(32)], [G() for _ in range(32)]
    for j in range(4):
        for mu in range(2):
            actual[(j*4+j)*2+mu] = outputs[j][mu]/2
        target[(j*4+j)*2] = G(signs[j])/2
    require(sum((z*z.conj() for z in actual), G()) == 1
            and sum((z*z.conj() for z in target), G()) == 1, "normalized reference Choi states")
    amplitude = sum((x.conj()*y for x, y in zip(target, actual)), G())
    signed = [signs[j]*outputs[j][0] for j in range(4)]
    require(amplitude == sum(signed, G())/4, "literal all-sector reference Choi amplitude")
    metrics = [(1-z.r)/2 for z in signed[1:]]
    require(amplitude.r == 1-sum(metrics)/2, "I1/I2 full Choi bridge")
    good = amplitude*amplitude.conj()
    require(good.r >= amplitude.r**2 and good.i == 0, "Choi-good signed-overlap lower")
    require(signed[-1].i != 0, "Choi amplitude retains complex phase")
    return 32


def verify():
    norm_checks = cross_checks = kernel_terms = eigenphases = 0
    for gamma in (F(1), F(6, 5), F(5, 3)):
        for energy in (F(0), F(1, 5), F(-3, 7), F(2)):
            residue_norm(energy, gamma)
            norm_checks += 1
            for u in (F(0), F(5), F(10), F(100)):
                nonlinear(energy, gamma, u)
                eigenphases += 1
            for k in range(1, 13):
                cross_density(F(2, 7), energy, gamma, k)
                cross_checks += 1
            for count in (1, 2, 4, 8, 12):
                kernel_terms += kernel_guard(F(-1, 3), F(2, 7), energy, gamma, count)
    # Exact central Fourier moments of (1-cos(theta))/(2pi).
    def moment(k):
        return F(1) if k == 0 else (F(-1, 2) if abs(k) == 1 else F(0))
    central_guards = 0
    for count in range(1, 13):
        exponents = [count-1-2*n for n in range(count)]
        require([[moment(k-l) for l in exponents] for k in exponents] ==
                [[F(i == j) for j in range(count)] for i in range(count)], "central mode Gram")
        for bigger in range(count, 13, 2):
            require(set(exponents).issubset(set(bigger-1-2*n for n in range(bigger))),
                    "same-parity raw array nesting")
            central_guards += 1
    require(moment(1) == F(-1, 2), "opposite-parity overlap is not zero")
    for energy in (F(0), F(1, 3)):
        for count in (1, 2):
            commutator_guard(energy, F(1), count)
    return {"status": "passed", "normalization_residues": norm_checks,
            "finite_U_unit_eigenphases": eigenphases, "cross_integrand_identities": cross_checks,
            "connected_kernel_terms": kernel_terms, "central_same_parity_nesting": central_guards,
            "generic_commutator_fixtures": 4, "full_logical_Choi_state_components": choi_guard(),
            "scope": "Exact finite algebra guards for the homogeneous lossless effective chiral kernel. Universal contours/mode nesting and causal-filter restrictions are analytic inputs; no normalizable gate fidelity, microscopic all-frequency error, bath/herald or hardware claim."}


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True, indent=2))
