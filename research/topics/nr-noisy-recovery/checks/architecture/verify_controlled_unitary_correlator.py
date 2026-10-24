"""Exact finite replay of NR-R20's controlled-unitary correlation pilot.

Only the Python standard library is used. The implemented meters use two
forward controlled-F calls, with a measured/reset helper between them;
adjoints below occur only in exact matrix algebra, not oracle access.
Full finite matrix units check signed and nonselective instruments.
General concentration, projection, access and physical-cost arguments
remain analytic. No files are written.
"""

from fractions import Fraction as F
from itertools import product
import json
import sys


if not __debug__:
    raise RuntimeError("Run exact controlled-unitary correlator checks without -O.")
sys.dont_write_bytecode = True

from verify_fault_simulation import (
    ZERO, ONE, require, gaussian, add, multiply, conjugate, times,
    zeros, identity, adjoint, matmul, tensor, vectorize, inner, pauli_basis,
)


def scale(x, a):
    return [[times(z, a) for z in row] for row in x]


def complex_scale(x, a):
    return [[multiply(z, a) for z in row] for row in x]


def plus(x, y):
    return [[add(a, b) for a, b in zip(rx, ry)] for rx, ry in zip(x, y)]


def trace(x):
    out = ZERO
    for j in range(len(x)):
        out = add(out, x[j][j])
    return out


def matrix_unit(d, a, b):
    out = zeros(d, d)
    out[a][b] = ONE
    return out


def norm_squared(x):
    value = inner(vectorize(x), vectorize(x))
    require(value[1] == 0, "Hilbert-Schmidt norm has an imaginary part.")
    return value[0]


def evolved(k, x):
    return matmul(matmul(k, x), adjoint(k))


def channel(family, x):
    out = zeros(len(x), len(x))
    for weight, k in family:
        out = plus(out, scale(evolved(k, x), weight))
    return out


def require_tp(family, d):
    total = zeros(d, d)
    for weight, k in family:
        total = plus(total, scale(matmul(adjoint(k), k), weight))
    require(total == identity(d), "Noise fixture is not trace preserving.")


def pincher(basis):
    d = len(basis)
    return [(F(1), matmul(matmul(basis, matrix_unit(d, j, j)), adjoint(basis)))
            for j in range(d)]


def memory_channels(basis, t):
    d = len(basis)
    high = [(1-t, identity(d))]+[(t, p) for _, p in pincher(basis)]
    low = [(1-t, identity(d))]+[(t/d, matrix_unit(d, u, v))
                               for u, v in product(range(d), repeat=2)]
    require_tp(high, d)
    require_tp(low, d)
    return high, low


def projected_forward_meter(unitary, alpha):
    """Actual H--controlled(alpha F)--H circuit, from helper input |0>.

    H is stored without its 1/sqrt(2); its two appearances give the
    overall 1/2. The only controlled unitary here is alpha F forward.
    """
    d = len(unitary)
    controlled = zeros(2*d, 2*d)
    for u, v in product(range(d), repeat=2):
        controlled[u][v] = ONE if u == v else ZERO
        controlled[d+u][d+v] = multiply(alpha, unitary[u][v])
    require(matmul(adjoint(controlled), controlled) == identity(2*d),
            "Controlled forward meter is not unitary.")
    h = [[ONE, ONE], [ONE, gaussian(-1)]]
    full = scale(matmul(matmul(tensor(h, identity(d)), controlled),
                        tensor(h, identity(d))), F(1, 2))
    ks = [[[full[z*d+u][v] for v in range(d)] for u in range(d)]
          for z in range(2)]
    for z, k in enumerate(ks):
        expected = scale(plus(identity(d),
            complex_scale(unitary, times(alpha, (-1)**z))), F(1, 2))
        require(k == expected, "Actual projected meter disagrees with its Kraus formula.")
    require_tp([(F(1), k) for k in ks], d)
    return ks


def signed_meter(x, unitary, alpha):
    return scale(plus(complex_scale(matmul(unitary, x), alpha),
                      complex_scale(matmul(x, adjoint(unitary)), conjugate(alpha))), F(1, 2))


def nonselective_meter(x, unitary):
    return scale(plus(x, evolved(unitary, x)), F(1, 2))


def two_readout(family, x, first_meter, second_meter):
    branches = {}
    nonselective = signed = zeros(len(x), len(x))
    for z, y in product(range(2), repeat=2):
        out = evolved(second_meter[y], channel(family, evolved(first_meter[z], x)))
        branches[z, y] = out
        nonselective = plus(nonselective, out)
        signed = plus(signed, scale(out, (-1)**(z+y)))
    return branches, nonselective, signed


def fixtures():
    i2 = identity(2)
    rotation = [[gaussian(F(3, 5)), gaussian(F(-4, 5))],
                [gaussian(F(4, 5)), gaussian(F(3, 5))]]
    diag = [[ONE, ZERO], [ZERO, gaussian(0, 1)]]
    fixed2 = evolved(rotation, diag)
    x, z = pauli_basis(1)[1], pauli_basis(1)[3]
    approximate = plus(scale(i2, F(3, 5)),
                       complex_scale(plus(scale(z, F(12, 25)), scale(x, F(16, 25))),
                                     gaussian(0, -1)))
    cnot = zeros(4, 4)
    for a, b in product(range(2), repeat=2):
        cnot[2*a+(b ^ a)][2*a+b] = ONE
    basis4 = matmul(cnot, tensor(rotation, rotation))
    diag4 = zeros(4, 4)
    degenerate4 = zeros(4, 4)
    for j, value in enumerate((ONE, gaussian(-1), gaussian(0, 1), gaussian(0, -1))):
        diag4[j][j] = value
        degenerate4[j][j] = ONE if j < 2 else gaussian(-1)
    return [
        ("fixed_complex_d2", fixed2, rotation, True),
        ("approximate_d2", approximate, i2, False),
        ("scalar_projection_d2", complex_scale(x, gaussian(0, -1)), i2, False),
        ("fixed_complex_d4", evolved(basis4, diag4), basis4, True),
        ("fixed_degenerate_d4", evolved(basis4, degenerate4), basis4, True),
    ]


def replay():
    alphas = (ONE, gaussian(0, -1))
    phases = (ONE, gaussian(0, 1), gaussian(F(3, 5), F(4, 5)))
    instrument_entries = phase_cancel_entries = fixed_defect_identities = 0
    mean_identities = marginal_entries = conditional_correlations = 0
    static_phase_identities = drift_identities = 0
    reference_entries = 0
    for name, unitary, basis, is_fixed in fixtures():
        d = len(unitary)
        require(matmul(adjoint(unitary), unitary) == identity(d),
                "Correlator fixture is not unitary.")
        delta = channel(pincher(basis), unitary)
        defect = norm_squared(plus(unitary, scale(delta, -1)))/d
        projected_norm = norm_squared(delta)/d
        require(defect == 1-projected_norm, "Pincher defect/Pythagorean identity failed.")
        require(channel(pincher(basis), delta) == delta, "Pincher is not idempotent.")
        require((defect == 0) == is_fixed, "Fixed/nonfixed fixture qualification failed.")
        tau = times(trace(unitary), F(1, d))
        tau_squared = multiply(tau, conjugate(tau))[0]
        centered = plus(delta, complex_scale(identity(d), times(tau, -1)))
        require(projected_norm-tau_squared == norm_squared(centered)/d,
                "Centered fixed-component variance identity failed.")
        fixed_defect_identities += 4
        meters = [projected_forward_meter(unitary, alpha) for alpha in alphas]
        mixed = scale(identity(d), F(1, d))
        for alpha, meter in zip(alphas, meters):
            first = [evolved(k, mixed) for k in meter]
            h = scale(plus(complex_scale(unitary, alpha),
                           complex_scale(adjoint(unitary), conjugate(alpha))), F(1, 2))
            require(plus(first[0], first[1]) == mixed,
                    "First-meter unconditional target marginal changed.")
            require(plus(first[0], scale(first[1], -1)) == scale(h, F(1, d)),
                    "First-meter signed conditional preparation failed.")
            for sign, sigma in zip((1, -1), first):
                require(sigma == scale(plus(identity(d), scale(h, sign)), F(1, 2*d)),
                        "Actual conditional preparation disagrees with OF1.")
                p_sigma = trace(sigma)
                require(p_sigma[1] == 0 and p_sigma[0] >= 0,
                        "Conditional source branch has invalid probability.")
                if sigma != scale(mixed, p_sigma[0]):
                    conditional_correlations += 1
            marginal_entries += 3*d*d
        for t in (F(0), F(2, 5), F(1)):
            families = memory_channels(basis, t)
            means = []
            for hypothesis, family in enumerate(families):
                for u, v in product(range(d), repeat=2):
                    input_unit = matrix_unit(d, u, v)
                    averaged_signed = zeros(d, d)
                    for alpha, meter in zip(alphas, meters):
                        _, actual_nonselective, actual_signed = two_readout(
                            family, input_unit, meter, meter)
                        expected_nonselective = nonselective_meter(
                            channel(family, nonselective_meter(input_unit, unitary)), unitary)
                        expected_signed = signed_meter(
                            channel(family, signed_meter(input_unit, unitary, alpha)), unitary, alpha)
                        require(actual_nonselective == expected_nonselective,
                                "Full two-readout nonselective matrix-unit map failed.")
                        require(actual_signed == expected_signed,
                                "Full two-readout signed matrix-unit map failed.")
                        averaged_signed = plus(averaged_signed, scale(actual_signed, F(1, 2)))
                        instrument_entries += 2*d*d
                    cross_only = scale(plus(
                        matmul(unitary, channel(family, matmul(input_unit, adjoint(unitary)))),
                        matmul(channel(family, matmul(unitary, input_unit)), adjoint(unitary))), F(1, 4))
                    require(averaged_signed == cross_only,
                            "Two-quadrature full signed map did not cancel equal-phase terms.")
                    phase_cancel_entries += d*d
                phase_means = []
                for alpha, meter in zip(alphas, meters):
                    branches, total, signed = two_readout(family, mixed, meter, meter)
                    require(total == mixed, "Unital memory changed the unconditional target marginal.")
                    require(channel(family, mixed) == mixed, "Unital fixture does not fix I/D.")
                    require(sum(trace(v)[0] for v in branches.values()) == 1,
                            "Full readout probabilities are not normalized.")
                    phase_means.append(trace(signed)[0])
                    marginal_entries += d*d
                mean = sum(phase_means)/2
                raw_inner = trace(matmul(adjoint(unitary), channel(family, unitary)))
                require(mean == raw_inner[0]/(2*d), "Two-phase correlation identity failed.")
                expected = ((1-t*defect)/2 if hypothesis == 0
                            else (1-t+t*tau_squared)/2)
                require(mean == expected, "Fixed/approximate memory mean failed.")
                means.append(mean)
                mean_identities += 2
                for phase in phases:
                    phased = complex_scale(unitary, phase)
                    phase_mean = F(0)
                    for alpha in alphas:
                        meter = projected_forward_meter(phased, alpha)
                        phase_mean += trace(two_readout(family, mixed, meter, meter)[2])[0]/2
                    require(phase_mean == mean, "Consistent unknown global phase did not cancel.")
                    static_phase_identities += 1
                for drift in (gaussian(0, 1), gaussian(-1), gaussian(F(3, 5), F(4, 5))):
                    second = complex_scale(unitary, drift)
                    measured = F(0)
                    for alpha, first_meter in zip(alphas, meters):
                        second_meter = projected_forward_meter(second, alpha)
                        measured += trace(two_readout(family, mixed, first_meter, second_meter)[2])[0]/2
                    require(raw_inner[1] == 0 and measured == drift[0]*mean,
                            "Self-adjoint promise channel relative-phase drift formula failed.")
                    drift_identities += 1
            require(means[0]-means[1] == t*(1-tau_squared-defect)/2,
                    "Same-t approximate promise mean gap failed.")
            require(means[0]-means[1] == t*norm_squared(centered)/(2*d),
                    "Same-t centered projection gap failed.")
            fixed_defect_identities += 2
        if name == "approximate_d2":
            require(defect == F(256, 625) and tau_squared == F(9, 25),
                    "Approximate fixed-point example changed.")
            # Explicit target-reference matrix units, applying only target
            # Kraus operators. This also detects tensor-order mistakes.
            family = memory_channels(basis, F(2, 5))[0]
            extended_family = [(weight, tensor(k, identity(2))) for weight, k in family]
            extended_unitary = tensor(unitary, identity(2))
            for u, v in product(range(4), repeat=2):
                input_unit = matrix_unit(4, u, v)
                for alpha, meter in zip(alphas, meters):
                    extended_meter = [tensor(k, identity(2)) for k in meter]
                    _, total, signed = two_readout(extended_family, input_unit,
                                                   extended_meter, extended_meter)
                    require(total == nonselective_meter(channel(extended_family,
                            nonselective_meter(input_unit, extended_unitary)), extended_unitary),
                            "Passive-reference full nonselective map failed.")
                    require(signed == signed_meter(channel(extended_family,
                            signed_meter(input_unit, extended_unitary, alpha)), extended_unitary, alpha),
                            "Passive-reference full signed map failed.")
                    reference_entries += 2*16
    # Nonunital CPTP map: general correlation still holds, but I/D need not
    # remain fixed. Relative drift cannot generally be replaced by cos(delta).
    d = 2
    unitary = [[ONE, ZERO], [ZERO, gaussian(0, 1)]]
    mixed = scale(identity(d), F(1, d))
    damping = [(F(1), [[ONE, ZERO], [ZERO, gaussian(F(3, 5))]]),
               (F(1), [[ZERO, gaussian(F(4, 5))], [ZERO, ZERO]])]
    require_tp(damping, d)
    require(channel(damping, mixed) != mixed, "Nonunital counterexample became unital.")
    nonunital_entries = 0
    for u, v in product(range(d), repeat=2):
        x = matrix_unit(d, u, v)
        for alpha in alphas:
            meter = projected_forward_meter(unitary, alpha)
            _, total, signed = two_readout(damping, x, meter, meter)
            require(total == nonselective_meter(channel(damping,
                    nonselective_meter(x, unitary)), unitary), "Nonunital nonselective map failed.")
            require(signed == signed_meter(channel(damping,
                    signed_meter(x, unitary, alpha)), unitary, alpha), "Nonunital signed map failed.")
            nonunital_entries += 2*d*d
    inner_value = trace(matmul(adjoint(unitary), channel(damping, unitary)))
    require(inner_value == gaussian(F(34, 25), F(16, 25)),
            "Nonunital complex correlation fixture changed.")
    for drift in (ONE, gaussian(0, 1), gaussian(F(3, 5), F(4, 5))):
        actual = F(0)
        for alpha in alphas:
            first = projected_forward_meter(unitary, alpha)
            second = projected_forward_meter(complex_scale(unitary, drift), alpha)
            actual += trace(two_readout(damping, mixed, first, second)[2])[0]/2
        expected = multiply(conjugate(drift), inner_value)[0]/(2*d)
        require(actual == expected, "General complex relative-phase correlation formula failed.")
        if drift == gaussian(0, 1):
            require(actual == F(4, 25) and actual != drift[0]*inner_value[0]/(2*d),
                    "Nonunital phase-drift counterexample failed.")
        drift_identities += 1
    require(conditional_correlations > 0, "No source record-target correlation was tested.")
    return dict(status="passed", arithmetic="standard-library exact Gaussian fractions",
                full_two_readout_matrix_unit_entries=instrument_entries,
                two_phase_signed_map_cancellation_entries=phase_cancel_entries,
                fixed_and_approximate_projection_identities=fixed_defect_identities,
                all_outcome_mean_identities=mean_identities,
                unital_and_source_marginal_entries=marginal_entries,
                nonproduct_source_record_branches=conditional_correlations,
                static_global_phase_identities=static_phase_identities,
                relative_phase_drift_identities=drift_identities,
                passive_reference_matrix_unit_entries=reference_entries,
                nonunital_instrument_matrix_unit_entries=nonunital_entries,
                nonunital_relative_phase_counterexample="mu(delta=pi/2)=4/25, not zero",
                approximate_fixed_point_defect_squared="256/625",
                scope="Finite actual forward controlled-unitary meters, complete signed/nonselective instruments, pinching defects, marginal/conditional distinctions and phase guards. No inverse oracle is invoked. General concentration, approximate-promise thresholds, access qualification, reset and physical resource costs remain analytic; no generic uncontrolled-F or native advantage claim.")


def main():
    print(json.dumps(replay(), sort_keys=True))


if __name__ == "__main__":
    main()
