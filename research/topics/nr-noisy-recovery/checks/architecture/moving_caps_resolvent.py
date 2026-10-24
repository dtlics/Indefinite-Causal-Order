"""Exact finite passive-resolvent and unwrapped energy-fiber replay.

This is a three-motion-level fixture, not an oscillator/tail theorem or a
hardware certificate.  It reuses the canonical Gaussian-rational engine.
All guards survive -O; import and verify() are quiet; no files are written.
Use a caller-side -B as well as the bytecode guard below.
"""
import sys

sys.dont_write_bytecode = True

from fractions import Fraction as F
from functools import lru_cache
import hashlib
import importlib.util
from itertools import combinations, permutations, product
import json
from pathlib import Path


ENGINE = Path(__file__).resolve().with_name("retained_photon_serial.py")
_spec = importlib.util.spec_from_file_location("_retained_photon_serial_bound", ENGINE)
if _spec is None or _spec.loader is None:
    raise ValueError("canonical exact engine import specification")
_engine = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_engine)
G, require = _engine.G, _engine.require
eye, zeros, mm, adj = _engine.eye, _engine.zeros, _engine.mm, _engine.adj
add, scale, blockdiag = _engine.add, _engine.scale, _engine.blockdiag

I = G(0, 1)
MU = F(1, 4)
KAPPA, KEX, KIN, GAMMA, COUPLING = F(2), F(3, 2), F(1, 2), F(3), F(2)
DELTA = min(KAPPA, GAMMA)
LIPSCHITZ = 2*KEX/(DELTA*DELTA)


def inverse(a):
    """Exact Gauss-Jordan inverse; the imported engine has no inverse."""
    n = len(a)
    require(n > 0 and all(len(row) == n for row in a), "inverse square matrix")
    work = [list(row)+ident for row, ident in zip(a, eye(n))]
    for col in range(n):
        pivot = next((r for r in range(col, n) if work[r][col] != 0), None)
        require(pivot is not None, "resolvent invertibility")
        work[col], work[pivot] = work[pivot], work[col]
        denominator = work[col][col]
        work[col] = [value/denominator for value in work[col]]
        for row in range(n):
            if row != col and work[row][col] != 0:
                factor = work[row][col]
                work[row] = [x-factor*y for x, y in zip(work[row], work[col])]
    require([row[:n] for row in work] == eye(n), "Gauss-Jordan reduced identity")
    return [row[n:] for row in work]


def diagonal(entries):
    return [[G(x) if r == c else G() for c in range(len(entries))]
            for r, x in enumerate(entries)]


def real(value, message):
    require(value.i == 0, message)
    return value.r


def norm2(values):
    return sum((real(value.conj()*value, "squared modulus real")
                for value in values), F())


def determinant(a):
    """Leibniz determinants only for the at-most-three-dimensional minors."""
    n = len(a)
    require(0 < n <= 3, "minor determinant dimension")
    total = G()
    for perm in permutations(range(n)):
        sign = (-1)**sum(perm[i] > perm[j]
                         for i in range(n) for j in range(i+1, n))
        value = G(sign)
        for row, col in enumerate(perm):
            value *= a[row][col]
        total += value
    return total


def psd3(a, message):
    """Hermitian PSD iff all seven principal minors are nonnegative."""
    require(len(a) == 3 and all(len(row) == 3 for row in a), message+" dimension")
    require(a == adj(a), message+" Hermitian")
    minors = []
    for size in (1, 2, 3):
        for indices in combinations(range(3), size):
            minor = [[a[r][c] for c in indices] for r in indices]
            value = real(determinant(minor), message+" real principal minor")
            require(value >= 0, message+" nonnegative principal minor")
            minors.append(value)
    return minors


D_A = [[G(F(3, 5)), G(), G(F(4, 5))],
       [G(), G(1), G()],
       [G(F(4, 5)), G(), G(F(-3, 5))]]
D_B = [[G(F(4, 5)), G(), G(F(3, 5))],
       [G(), G(1), G()],
       [G(F(3, 5)), G(), G(F(-4, 5))]]


def hamiltonian(node, elastic=False):
    d = eye(3) if elastic else (D_A if node == "A" else D_B)
    excited = ([F(), F(2, 3), F(7, 5)] if node == "A" else
               [F(1, 5), F(4, 7), F(9, 5)])
    cavity = diagonal([n*MU for n in range(3)])
    h0 = zeros(6)
    for r, c in product(range(3), repeat=2):
        h0[r][c] = cavity[r][c]
        h0[r+3][c+3] = diagonal(excited)[r][c]
        h0[r][c+3] = COUPLING*d[r][c]
        h0[r+3][c] = COUPLING*adj(d)[r][c]
    require(d == adj(d) and mm(adj(d), d) == eye(3), "bounded Hermitian unitary d")
    require(h0 == adj(h0), "H0 Hermitian")
    return add(h0, scale(diagonal([KAPPA]*3+[GAMMA]*3), -I))


@lru_cache(maxsize=None)
def resolvent(node, energy, elastic=False):
    matrix = add(scale(eye(6), energy), scale(hamiltonian(node, elastic), -1))
    result = inverse(matrix)
    require(mm(matrix, result) == eye(6) and mm(result, matrix) == eye(6),
            "both resolvent inverse identities")
    return result


@lru_cache(maxsize=None)
def scattering(node, energy, elastic=False):
    resol = resolvent(node, energy, elastic)
    return add(eye(3), scale([row[:3] for row in resol[:3]], -2*I*KEX))


def contraction(node, energy):
    resol = resolvent(node, energy)
    selected = scattering(node, energy)
    incoming_cavity = [row[:3] for row in resol]
    loss_rate = diagonal([KIN]*3+[GAMMA]*3)
    gram = scale(mm(adj(incoming_cavity), mm(loss_rate, incoming_cavity)), 4*KEX)
    deficit = add(eye(3), scale(mm(adj(selected), selected), -1))
    require(deficit == gram, "I-SdagS equals full intrinsic/emission Gram")
    require(KIN > 0 and GAMMA > 0, "Gram weights positive")
    psd3(gram, "selected scattering contraction")


def three_port_flux_unitarity(node, energy):
    """Rational weighted basis, exactly equivalent to normalized Sfull9.

    Physical channel factors contain square roots of the rates.  With
    W=diag(kex I, kin I, gamma I), physical S=W^(1/2) T W^(-1/2).
    Thus Tdag W T=W is exactly physical Sdag S=I, without adding an
    irrational arithmetic engine.  No port is omitted.
    """
    embed = zeros(6, 9)
    for n in range(3):
        embed[n][n] = embed[n][n+3] = G(1)
        embed[n+3][n+6] = G(1)
    weight = diagonal([KEX]*3+[KIN]*3+[GAMMA]*3)
    inverse_weight = diagonal([1/KEX]*3+[1/KIN]*3+[1/GAMMA]*3)
    require(mm(embed, mm(weight, adj(embed))) == diagonal([KAPPA]*3+[GAMMA]*3),
            "all three ports exhaust passive damping")
    transfer = add(eye(9), scale(mm(adj(embed), mm(resolvent(node, energy),
                                                mm(embed, weight))), -2*I))
    require(mm(adj(transfer), mm(weight, transfer)) == weight,
            "full nine-channel weighted unitarity")
    require(mm(transfer, mm(inverse_weight, adj(transfer))) == inverse_weight,
            "full nine-channel inverse weighted unitarity")
    require([row[:3] for row in transfer[:3]] == scattering(node, energy),
            "external selected block equals S")


def lipschitz(node, energy, shift):
    difference = add(scattering(node, energy+shift), scale(scattering(node, energy), -1))
    margin = add(scale(eye(3), LIPSCHITZ*LIPSCHITZ*shift*shift),
                 scale(mm(adj(difference), difference), -1))
    psd3(margin, "finite-shift Lipschitz inequality")
    return any(value != 0 for row in difference for value in row)


def local_amplitude(node, frequency, incoming, outgoing, elastic=False):
    """Literal fiber: s_mn(w)=S(w+n mu)_mn."""
    return scattering(node, frequency+incoming*MU, elastic)[outgoing][incoming]


def word_amplitude(frequency, n_a, n_b, a_first, elastic=False):
    """Keep unwrapped rational photon frequency and both output motions."""
    out = {}
    for m_a, m_b in product(range(3), repeat=2):
        shift_a, shift_b = (m_a-n_a)*MU, (m_b-n_b)*MU
        if a_first:
            amplitude = (local_amplitude("A", frequency, n_a, m_a, elastic) *
                         local_amplitude("B", frequency-shift_a, n_b, m_b, elastic))
        else:
            amplitude = (local_amplitude("B", frequency, n_b, m_b, elastic) *
                         local_amplitude("A", frequency-shift_b, n_a, m_a, elastic))
        key = (frequency-shift_a-shift_b, m_a, m_b)
        total_energy = frequency+(n_a+n_b)*MU
        require(key[0]+(m_a+m_b)*MU == total_energy,
                "literal output conserves total photon-plus-motion energy")
        # Independent fixed-total-energy rewrite: the spectator's current
        # trap energy, rather than a copied signed photon shift, selects
        # each local resolvent fiber.
        if a_first:
            expected = (scattering("A", total_energy-n_b*MU, elastic)[m_a][n_a] *
                        scattering("B", total_energy-m_a*MU, elastic)[m_b][n_b])
        else:
            expected = (scattering("B", total_energy-n_a*MU, elastic)[m_b][n_b] *
                        scattering("A", total_energy-m_b*MU, elastic)[m_a][n_a])
        require(amplitude == expected, "independent total-energy coefficient oracle")
        if amplitude != 0:
            out[key] = amplitude
    return out


def second_moment(node, frequency, incoming, elastic=False):
    return sum((((outgoing-incoming)*MU)**2 *
                norm2([local_amplitude(node, frequency, incoming, outgoing, elastic)])
                for outgoing in range(3)), F())


def subtract_maps(left, right, right_phase=G(1)):
    return {key: left.get(key, G())-right_phase*right.get(key, G())
            for key in left.keys() | right.keys()}


def serial_guard(frequency, n_a, n_b):
    ab = word_amplitude(frequency, n_a, n_b, True)
    ba = word_amplitude(frequency, n_a, n_b, False)
    pminus = norm2(subtract_maps(ab, ba).values())/4
    m2_a = second_moment("A", frequency, n_a)
    m2_b = second_moment("B", frequency, n_b)
    bound = (LIPSCHITZ*LIPSCHITZ*(m2_a+m2_b))/2
    require(pminus <= bound, "literal two-word minus probability energy-transfer bound")
    require(norm2(ab.values()) <= 1 and norm2(ba.values()) <= 1,
            "both complete retained word amplitudes contract")
    # Freeze energies in the *second* contact to expose the actual two
    # differences used in the triangle bound, on the same full output basis.
    frozen = {}
    for m_a, m_b in product(range(3), repeat=2):
        key = (frequency-(m_a-n_a+m_b-n_b)*MU, m_a, m_b)
        frozen[key] = (local_amplitude("A", frequency, n_a, m_a) *
                       local_amplitude("B", frequency, n_b, m_b))
    left_error = norm2(subtract_maps(ab, frozen).values())
    right_error = norm2(subtract_maps(ba, frozen).values())
    require(left_error <= LIPSCHITZ*LIPSCHITZ*m2_a,
            "A-first frozen-frequency difference bounded by A transfer moment")
    require(right_error <= LIPSCHITZ*LIPSCHITZ*m2_b,
            "B-first frozen-frequency difference bounded by B transfer moment")
    require(4*pminus <= 2*(left_error+right_error), "squared triangle step")
    return pminus, bound, m2_a, m2_b


def unit_power(value, exponent):
    require(exponent.denominator == 1, "energy phase lies on integer grid")
    count = int(exponent)
    if count < 0:
        value, count = value.conj(), -count
    result = G(1)
    for _ in range(count):
        result *= value
    return result


def coherent_input_guard():
    # Rational normalized superposition across distinct *unwrapped* energy
    # fibers; amplitudes are retained, with no dephasing/trace between them.
    inputs = [(F(), 0, 0, F(3, 5)), (F(1, 3), 0, 0, F(4, 5))]
    ab, ba = {}, {}
    bound = F()
    for frequency, n_a, n_b, coefficient in inputs:
        for destination, first in ((ab, True), (ba, False)):
            for key, amplitude in word_amplitude(frequency, n_a, n_b, first).items():
                destination[key] = destination.get(key, G())+coefficient*amplitude
        bound += coefficient*coefficient*LIPSCHITZ*LIPSCHITZ*(
            second_moment("A", frequency, n_a)+second_moment("B", frequency, n_b))/2
    require(sum((entry[3]**2 for entry in inputs), F()) == 1,
            "coherent frequency input normalized")
    pminus = norm2(subtract_maps(ab, ba).values())/4
    require(0 < pminus <= bound, "full coherent-frequency minus map bound")
    # Certify a nonzero cross-energy output coefficient, rather than merely
    # comparing the classical mixture of the two fibers.
    nonzero = [key for key, value in ab.items() if value != 0]
    cross = next(((x, y) for x in nonzero for y in nonzero
                  if x[0]+(x[1]+x[2])*MU != y[0]+(y[1]+y[2])*MU), None)
    require(cross is not None and ab[cross[0]]*ab[cross[1]].conj() != 0,
            "coherent cross-frequency matrix coefficient retained")
    return pminus, bound, len(ab), len(ba)


def phase_guards():
    phase = G(F(3, 5), F(4, 5))
    require(phase.conj()*phase == 1, "rational phase unit modulus")
    grid, finish = F(1, 12), 5
    entries = 0
    for frequency, n_a, n_b in product((F(), F(1, 3)), range(3), range(3)):
        total = frequency+(n_a+n_b)*MU
        for first in (False, True):
            for key, amplitude in word_amplitude(frequency, n_a, n_b, first).items():
                output_total = key[0]+(key[1]+key[2])*MU
                require(output_total == total, "same-clock output total-energy equality")
                # Contact at the start or after two common free-time steps,
                # followed by the same finish time, gives the identical map.
                early = unit_power(phase, total/grid*finish)*amplitude
                late = (unit_power(phase, output_total/grid*(finish-2))*amplitude *
                        unit_power(phase, total/grid*2))
                require(early == late, "early/late contacts with common free finish")
                require(unit_power(phase, output_total/grid)*amplitude ==
                        amplitude*unit_power(phase, total/grid),
                        "stationary contact commutes with full common free evolution")
                entries += 1
    elastic_ab = word_amplitude(F(), 0, 0, True, elastic=True)
    elastic_ba = word_amplitude(F(), 0, 0, False, elastic=True)
    require(elastic_ab == elastic_ba, "elastic diagonal contacts commute without path phase")
    require(second_moment("A", F(), 0, True) ==
            second_moment("B", F(), 0, True) == 0, "elastic transfer moments vanish")
    phase_minus = norm2(subtract_maps(elastic_ab, elastic_ba, G(-1)).values())/4
    require(phase_minus > 0, "relative minus path phase violates zero-moment inference")
    return entries, phase_minus


def verify_resolvent_and_order():
    resolvent.cache_clear()
    scattering.cache_clear()
    require(KAPPA == KEX+KIN and DELTA == 2 and LIPSCHITZ == F(3, 4),
            "declared passive rates and Lipschitz constant")
    require(D_A[0][2] != 0 and D_B[0][2] != 0 and D_A != D_B,
            "distinct nontrivial bounded motion couplers")
    energies = (F(-1, 2), F(), F(1, 3), F(7, 4))
    shifts = (F(-1, 2), F(-1, 4), F(1, 7), F(1, 4), F(1, 2))
    lipschitz_checks = 0
    for node, energy in product(("A", "B"), energies):
        contraction(node, energy)
        for shift in shifts:
            require(lipschitz(node, energy, shift), "nonzero finite energy-shift difference")
            lipschitz_checks += 1
    for node in ("A", "B"):
        three_port_flux_unitarity(node, F())
    serial = [serial_guard(frequency, n_a, n_b)
              for frequency, n_a, n_b in product((F(), F(1, 3)), range(3), range(3))]
    require(any(pminus > 0 for pminus, _, _, _ in serial), "nonzero retained-word commutator")
    require(any(m2a > 0 and m2b > 0 for _, _, m2a, m2b in serial),
            "both nodes have nonzero inelastic transfer")
    coherent = coherent_input_guard()
    phase_entries, false_minus = phase_guards()
    witness = serial[0]
    return {
        "status": "passed",
        "arithmetic": "standard-library Gaussian rationals; imported retained_photon_serial engine",
        "motion_levels": 3,
        "effective_hamiltonian_dimension": 6,
        "mu": str(MU),
        "rates": {"kappa": str(KAPPA), "kappa_ex": str(KEX), "kappa_in": str(KIN),
                  "gamma": str(GAMMA), "g": str(COUPLING)},
        "delta": str(DELTA),
        "lipschitz_constant": str(LIPSCHITZ),
        "two_sided_inverse_checks": 2*resolvent.cache_info().currsize,
        "contraction_gram_checks": 8,
        "full_three_port_channels": 9,
        "full_three_port_flux_unitarity_checks": 2,
        "full_three_port_representation": "Tdag W T=W and T W^-1 Tdag=W^-1; exactly flux-normalized Sfull9 unitarity",
        "lipschitz_matrix_checks": lipschitz_checks,
        "lipschitz_principal_minors": 7*lipschitz_checks,
        "unwrapped_serial_input_basis_cases": len(serial),
        "nonzero_serial_commutator_cases": sum(pminus > 0 for pminus, _, _, _ in serial),
        "w0_nA0_nB0": {"pminus": str(witness[0]), "upper_bound": str(witness[1]),
                        "M2_A": str(witness[2]), "M2_B": str(witness[3])},
        "coherent_two_frequency": {"pminus": str(coherent[0]), "upper_bound": str(coherent[1]),
                                   "AB_output_amplitudes": coherent[2], "BA_output_amplitudes": coherent[3],
                                   "cross_frequency_coherence_retained": True},
        "same_clock_phase_amplitude_checks": phase_entries,
        "elastic_relative_minus_path_phase_counterexample": {"M2_A": "0", "M2_B": "0",
                                                               "pminus": str(false_minus)},
        "engine_sha256": hashlib.sha256(ENGINE.read_bytes()).hexdigest(),
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope": "Finite exact mot3 fixtures only. Retained photon/motion amplitudes use literal unwrapped energy fibers and both word histories. Includes passive resolvent, complete three-port flux unitarity, finite-shift PSD, nonzero inelastic commutator, relative-path-phase counterexample and common-total-energy clock guards. Does not prove an infinite-oscillator/tail bound, a general theorem, a complete timed bath/router instrument, or hardware performance."
    }


def verify():
    """Quiet exact finite replay, including rank, factory and readout guards."""
    own = verify_resolvent_and_order()
    rank_path = Path(__file__).resolve().with_name("moving_caps_rank.py")
    rank_spec = importlib.util.spec_from_file_location("_moving_caps_rank_resolvent", rank_path)
    require(rank_spec is not None and rank_spec.loader is not None,
            "rank-budget helper import specification")
    rank = importlib.util.module_from_spec(rank_spec)
    rank_spec.loader.exec_module(rank)
    budget = rank.verify()
    factory_path = Path(__file__).resolve().with_name("moving_caps_factory.py")
    factory_spec = importlib.util.spec_from_file_location("_moving_caps_factory_resolvent", factory_path)
    require(factory_spec is not None and factory_spec.loader is not None,
            "factory helper import specification")
    factory = importlib.util.module_from_spec(factory_spec)
    factory_spec.loader.exec_module(factory)
    factory_budget = factory.verify()
    analyzer_path = Path(__file__).resolve().with_name("moving_caps_analyzer.py")
    analyzer_spec = importlib.util.spec_from_file_location("_moving_caps_analyzer_resolvent", analyzer_path)
    require(analyzer_spec is not None and analyzer_spec.loader is not None,
            "coherent analyzer helper import specification")
    analyzer = importlib.util.module_from_spec(analyzer_spec)
    analyzer_spec.loader.exec_module(analyzer)
    analyzer_budget = analyzer.verify()
    frequency_path = Path(__file__).resolve().with_name("moving_caps_frequency.py")
    frequency_spec = importlib.util.spec_from_file_location("_moving_caps_frequency_resolvent", frequency_path)
    require(frequency_spec is not None and frequency_spec.loader is not None,
            "frequency readout helper import specification")
    frequency = importlib.util.module_from_spec(frequency_spec)
    frequency_spec.loader.exec_module(frequency)
    frequency_budget = frequency.verify()
    require(own["status"] == budget["status"] == factory_budget["status"] ==
            analyzer_budget["status"] == frequency_budget["status"] == "passed",
            "all five exact fixture families passed")
    return {"status": "passed", "resolvent_and_order": own,
            "rank_budget": budget, "blue_band_factory": factory_budget,
            "coherent_carrier_analyzer": analyzer_budget,
            "finite_frequency_readout": frequency_budget}


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True))
