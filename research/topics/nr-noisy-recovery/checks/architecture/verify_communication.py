"""Exact finite communication identities; analytic scope is communication.md.

Uses Gaussian rationals from the existing exact matrix engine. All reports go
to stdout. This does not replay the all-history entropy/capacity argument.
Random-receiver examples also use exact Pauli-phase exponents and normalized
measurement-branch coefficients; physical controller graphs remain analytic.
"""
from fractions import Fraction as F
from itertools import product
from math import isqrt
import json

from verify_fault_simulation import (
    ZERO, ONE, gaussian, add, multiply, conjugate, times, zeros, identity,
    adjoint, matmul, tensor, diagonal_blocks, vectorize, add_outer, pauli_basis,
    rational_rotation, require,
)

from raman_baselines import verify_raman_stronger_baselines
from raman_multimode_helper import verify_raman_multimode_helper
from verify_raman_phase_covariance import verify_raman_phase_covariance
from verify_raman_reciprocal_ports import verify_reciprocal_raman_ports
from verify_raman_route_and_echo_phases import verify_raman_route_and_echo_phases
from raman_port_routes import verify_raman_port_routes
from raman_direct_temporal import verify_raman_direct_temporal
from raman_timed_controls import verify_raman_timed_controls
from raman_temporal_tail import verify_raman_temporal_tail

if not __debug__:
    raise RuntimeError("Exact communication checks require assertions; do not use -O.")


def scale(a, value):
    return [[times(x, value) for x in row] for row in a]


def matrix_sum(matrices, d):
    out = zeros(d, d)
    for a in matrices:
        for i in range(d):
            for j in range(d):
                out[i][j] = add(out[i][j], a[i][j])
    return out


def choi(operators, input_dimension, weights=None):
    outdim = len(operators[0])
    out = zeros(input_dimension * outdim, input_dimension * outdim)
    weights = weights or [F(1)] * len(operators)
    for k, weight in zip(operators, weights):
        add_outer(out, vectorize(k), weight / input_dimension)
    return out


def dephase_output_control(j, target_dimension, input_dimension, visibility):
    outdim = 2 * target_dimension
    return [[times(value, visibility if (i % outdim) // target_dimension
                   != (k % outdim) // target_dimension else F(1))
             for k, value in enumerate(row)] for i, row in enumerate(j)]


def vacuum_channel(d, transmission_amplitude, loss_amplitude):
    x, y = transmission_amplitude, loss_amplitude
    assert x*x + y*y == 1 and x >= 0 and y >= 0
    no_loss = scale(identity(d+1), x)
    no_loss[d][d] = ONE
    operators = [no_loss]
    for i in range(d):
        loss = zeros(d+1, d+1)
        loss[d][i] = gaussian(y)
        operators.append(loss)
    assert matrix_sum([matmul(adjoint(k), k) for k in operators], d+1) == identity(d+1)
    return operators


def loss_example(d, x, lx, y, ly):
    aa, bb = x*x, y*y
    es, fs = vacuum_channel(d, x, lx), vacuum_channel(d, y, ly)
    operators = []
    for e in es:
        for f in fs:
            fe, ef = matmul(f, e), matmul(e, f)
            operators.append([row[:d] for row in fe + ef])
    actual = choi(operators, d, [F(1, 2)] * len(operators))
    expected = zeros(2*(d+1)*d, 2*(d+1)*d)
    transmission = zeros(2*(d+1), d)
    for i in range(d):
        transmission[i][i] = transmission[d+1+i][i] = gaussian(x*y)
    add_outer(expected, vectorize(transmission), F(1, 2*d))
    erasure = 1-aa*bb
    coherence = y*(1-aa) + x*(1-bb)
    tau = [[erasure/2, coherence/2], [coherence/2, erasure/2]]
    assert tau[0][0]*tau[1][1] - tau[0][1]**2 >= 0
    assert tau[0][0] + tau[1][1] == erasure
    for i in range(d):
        for c in range(2):
            for cc in range(2):
                row = c*(d+1) + d + 2*(d+1)*i
                col = cc*(d+1) + d + 2*(d+1)*i
                expected[row][col] = add(expected[row][col], gaussian(tau[c][cc]/d))
    assert actual == expected
    # The erasure register is orthogonal; the control flag has no input
    # dependence even on a reference, verified by the full Choi equality.
    if erasure:
        assert coherence/erasure == (x+y)/(1+x*y)
    return {"data_dimension": d, "transmission_probabilities": [str(aa), str(bb)],
            "serial_and_switched_survival": str(aa*bb),
            "unnormalized_lost_control_matrix": [[str(v) for v in r] for r in tau],
            "full_choi_entries_compared": len(actual)**2, "exact_residual": "0"}


def exact_norm(vector):
    norm_squared = sum((multiply(conjugate(x), x)[0] for x in vector), F(0))
    nr, dr = isqrt(norm_squared.numerator), isqrt(norm_squared.denominator)
    assert nr*nr == norm_squared.numerator and dr*dr == norm_squared.denominator
    return F(nr, dr)


def wire_example(d, mixed_unitaries, visibility):
    # Rank-one measure-and-prepare E; F either has genuine amplitude damping
    # or full-rank rational unitary Kraus operators. The second instance is
    # nonunital E, rather than only an orthogonal projective measurement.
    outputs = []
    for i in range(d):
        vector = [ZERO] * d
        if mixed_unitaries and i < 2:
            vector[0], vector[1] = gaussian(F(3, 5)), gaussian(F(4, 5))
        else:
            vector[i] = ONE
        outputs.append(vector)
    es = []
    for i, v in enumerate(outputs):
        e = zeros(d, d)
        for k in range(d):
            e[k][i] = v[k]
        es.append(e)
    if mixed_unitaries:
        u, v = identity(d), identity(d)
        u[0][0], u[0][1], u[1][0], u[1][1] = map(gaussian, (F(3,5), F(-4,5), F(4,5), F(3,5)))
        v[1][1] = gaussian(-1)
        fs = [scale(u, F(3, 5)), scale(v, F(4, 5))]
    else:
        f0, f1 = identity(d), zeros(d, d)
        f0[1][1], f1[0][1] = gaussian(F(3, 5)), gaussian(F(4, 5))
        fs = [f0, f1]
    for family in (es, fs):
        assert matrix_sum([matmul(adjoint(k), k) for k in family], d) == identity(d)
    ws, ls, wire_ops, wire_weights = [], [], [], []
    z = [[ONE, ZERO], [ZERO, gaussian(-1)]]
    for e, av in zip(es, outputs):
        for f in fs:
            w = diagonal_blocks(matmul(f, e), matmul(e, f))
            bv = [row[0] for row in matmul(f, [[x] for x in av])]
            norm = exact_norm(bv)
            u0 = [times(x, 1/norm) for x in bv] if norm else [ONE] + [ZERO]*(d-1)
            v = zeros(2*d, 2)
            for k in range(d):
                v[k][0], v[d+k][1] = u0[k], av[k]
            assert matmul(adjoint(v), v) == identity(2)
            l = matmul(adjoint(v), w)
            assert matmul(v, l) == w
            ls.append(l)
            ws.append(w)
            wire_ops.extend([matmul(v, l), matmul(matmul(v, z), l)])
            wire_weights.extend([(1+visibility)/2, (1-visibility)/2])
    assert matrix_sum([matmul(adjoint(l), l) for l in ls], 2*d) == identity(2*d)
    expected = dephase_output_control(choi(ws, 2*d), d, 2*d, visibility)
    actual = choi(wire_ops, 2*d, wire_weights)
    assert actual == expected
    return {"data_dimension": d, "second_channel": "mixed full-rank unitaries" if mixed_unitaries else "amplitude damping",
            "first_channel": "nonunital rank-one measure-and-prepare" if mixed_unitaries else "rank-one PVM",
            "control_visibility": str(visibility), "instrument_branches": len(ls),
            "full_control_input_allowed": True, "full_choi_entries_compared": len(actual)**2,
            "instrument_completeness": "I", "sector_isometry_and_full_choi_residual": "0"}


def tight_activation(visibility):
    paulis = pauli_basis(1)
    es = fs = [paulis[1], paulis[2]]  # X,Y; each channel has weight1/2.
    ts = []
    for e in es:
        for f in fs:
            ts.append(matmul(f, e) + matmul(e, f))
    j = dephase_output_control(choi(ts, 2, [F(1,8)]*4), 2, 2, visibility)
    decoded = zeros(4, 4)
    for s in (1, -1):
        for r in range(2):
            for t in range(2):
                correction = -1 if s == -1 and r != t else 1
                for i in range(2):
                    for k in range(2):
                        value = ZERO
                        for c in range(2):
                            for cc in range(2):
                                value = add(value, times(j[c*2+r+4*i][cc*2+t+4*k], F(correction*s**(c+cc), 2)))
                        decoded[r+2*i][t+2*k] = add(decoded[r+2*i][t+2*k], value)
    expected = choi([identity(2), paulis[3]], 2, [(1+visibility)/2, (1-visibility)/2])
    assert decoded == expected
    return {"visibility": str(visibility), "decoded_channel": "(1+kappa)/2 id +(1-kappa)/2 Ad_Z",
            "all_outcomes_retained": True, "exact_full_choi_residual": "0"}


def rank_two_slot_example(visibility):
    d,r = 4,2
    p0,p1 = [[ONE,ZERO],[ZERO,ZERO]],[[ZERO,ZERO],[ZERO,ONE]]
    es = [tensor(p,identity(2)) for p in (p0,p1)]
    paulis = pauli_basis(2)
    u = rational_rotation(paulis[5],3,4,5)
    v = paulis[13]
    fs = [(F(3,5),u),(F(4,5),v)]
    ws,ls,wire_ops,weights = [],[],[],[]
    z_wire = diagonal_blocks(identity(r),scale(identity(r),F(-1)))
    for i,e in enumerate(es):
        for amplitude,unitary in fs:
            f = scale(unitary,amplitude)
            w = diagonal_blocks(matmul(f,e),matmul(e,f))
            sector_v = zeros(2*d,2*r)
            for t in range(r):
                for out in range(d):
                    sector_v[out][t] = unitary[out][i*r+t]
                    sector_v[d+out][r+t] = ONE if out == i*r+t else ZERO
            assert matmul(adjoint(sector_v),sector_v) == identity(2*r)
            l = matmul(adjoint(sector_v),w)
            assert matmul(sector_v,l) == w
            ws.append(w)
            ls.append(l)
            wire_ops.extend([matmul(sector_v,l),matmul(matmul(sector_v,z_wire),l)])
            weights.extend([(1+visibility)/2,(1-visibility)/2])
    assert matrix_sum([matmul(adjoint(l),l) for l in ls],2*d) == identity(2*d)
    expected = dephase_output_control(choi(ws,2*d),d,2*d,visibility)
    assert choi(wire_ops,2*d,weights) == expected
    return {"data_dimension":d,"slot_kraus_rank_bound":r,"control_visibility":str(visibility),
            "simulating_wire":"Q_kappa tensor id_2","exact_full_choi_residual":"0"}


def elastic_node_example():
    """Accepted state-carving contractions with independent local spin faults."""
    i, x, y, z = pauli_basis(1)
    ra = [[gaussian(F(4,5)), ZERO], [ZERO, gaussian(F(1,5))]]
    rb = [[gaussian(F(3,5)), ZERO], [ZERO, gaussian(F(2,5))]]
    p0, p1 = [[ONE,ZERO],[ZERO,ZERO]], [[ZERO,ZERO],[ZERO,ONE]]
    def conditional_node(r, memory):
        blocks = (matmul(x,r), matmul(r,x))
        terms = [tensor(p, tensor(k,i) if memory == 0 else tensor(i,k))
                 for p,k in zip((p0,p1),blocks)]
        return matrix_sum(terms,8)
    base_a, base_b = conditional_node(ra,0), conditional_node(rb,1)
    es = [matmul(tensor(i,tensor(m,i)),base_a) for m in (scale(i,F(3,5)),scale(y,F(4,5)))]
    fs = [matmul(tensor(i,tensor(i,m)),base_b) for m in (scale(i,F(5,13)),scale(z,F(12,13)))]
    pairs = 0
    for e in es:
        for f in fs:
            fe,ef = matmul(f,e),matmul(e,f)
            assert fe == ef
            assert diagonal_blocks(fe,ef) == tensor(i,fe)
            pairs += 1
    # A bus-bin flip violates the hypothesis and really can create a signal.
    bus_flip = tensor(x,tensor(i,i))
    faulty_e = matmul(bus_flip,base_a)
    left,right = matmul(base_b,faulty_e),matmul(faulty_e,base_b)
    noncommuting_entries = sum(a != b for row,col in zip(left,right) for a,b in zip(row,col))
    assert noncommuting_entries > 0
    return {"bus_bins":2,"local_memory_dimensions":[2,2],"commuting_accepted_kraus_pairs":pairs,
            "full_control_kraus_factorization":"I_C tensor serial_product",
            "noncommuting_entries_when_bus_preservation_is_violated":noncommuting_entries,
            "scope":"Finite rational state-carving/local-fault example; no experimental parameter fit."}


def frequency_check_example():
    q = tensor(pauli_basis(1)[3],identity(2))
    def projection(k):
        conjugated = matmul(matmul(q,k),q)
        return [[times(add(a,b),F(1,2)) for a,b in zip(row,col)] for row,col in zip(k,conjugated)]
    reset = [[ZERO,ONE],[ZERO,ZERO]]
    checked = 0
    for memory in (identity(2),pauli_basis(1)[1],reset):
        for outgoing in range(2):
            for incoming in range(2):
                mode = zeros(2,2)
                mode[outgoing][incoming] = ONE
                k = tensor(mode,memory)
                assert projection(k) == (k if outgoing == incoming else zeros(4,4))
                checked += 1
    upward,downward = zeros(2,2),zeros(2,2)
    upward[1][0],downward[0][1] = ONE,ONE
    first,second = tensor(upward,identity(2)),tensor(downward,identity(2))
    returning = matmul(second,first)
    assert returning != zeros(4,4) and projection(returning) == returning
    assert projection(first) == projection(second) == zeros(4,4)
    return {"frequency_bins":2,"matrix_unit_local_operator_checks":checked,
            "cross_bin_jump_projection":"0","frequency_preserving_projection":"unchanged",
            "cross_return_requires_separate_node_checks":True,
            "scope":"Exact two-bin phase-check algebra only; spectral resolution, pulse reshaping, bath overlaps and helper costs not supplied."}


def reset_kraus(factor):
    """Replacement map with state factor factor*factor^dagger."""
    d = len(factor)
    operators = []
    for column in range(d):
        for incoming in range(d):
            k = zeros(d, d)
            for outgoing in range(d):
                k[outgoing][incoming] = factor[outgoing][column]
            operators.append(k)
    assert matrix_sum([matmul(adjoint(k), k) for k in operators], d) == identity(d)
    return operators


def reset_cycle_example(first_factor, second_factor, label):
    """Compare full Choi operators without assuming a cross-term formula.

    The standard switch uses B*A in control0 and A*B in control1.
    The ordinary circuit prepares tau_A,omega_B, applies the register cycle
    (a,s,b)->(b,a,s) in control0 and identity in control1, then retains A.
    Direct resource-state contraction includes arbitrary quantum control.
    """
    d, m = len(first_factor), 2 * len(first_factor)
    es, fs = reset_kraus(first_factor), reset_kraus(second_factor)
    switched = choi([diagonal_blocks(matmul(f, e), matmul(e, f))
                    for e in es for f in fs], m)
    tau = matmul(first_factor, adjoint(first_factor))
    omega = matmul(second_factor, adjoint(second_factor))
    ordinary = zeros(m * m, m * m)
    for c in range(2):
        for cc in range(2):
            for s in range(d):
                for ss in range(d):
                    for a in range(d):
                        for aa in range(d):
                            for b in range(d):
                                for bb in range(d):
                                    row = (b, a, s) if c == 0 else (a, s, b)
                                    col = (bb, aa, ss) if cc == 0 else (aa, ss, bb)
                                    if row[1:] != col[1:]:
                                        continue
                                    i = c*d + row[0] + m*(c*d + s)
                                    j = cc*d + col[0] + m*(cc*d + ss)
                                    value = times(multiply(tau[a][aa], omega[b][bb]), F(1, m))
                                    ordinary[i][j] = add(ordinary[i][j], value)
    assert switched == ordinary
    for i in range(m):
        for j in range(m):
            value = ZERO
            for output in range(m):
                value = add(value, switched[output + m*i][output + m*j])
            assert value == gaussian(F(1, m) if i == j else 0)
    noncommuting = matmul(tau, omega) != matmul(omega, tau)
    if "distinct" in label:
        assert noncommuting
    return {"case": label, "data_dimension": d,
            "reset_states_noncommuting": noncommuting,
            "full_control_input_allowed": True,
            "normalized_choi_dimension": m*m,
            "full_choi_entries_compared": (m*m)**2,
            "trace_preserving": True, "exact_full_choi_residual": "0",
            "scope": "Two fixed-order replacement calls, two controlled swaps and two auxiliary registers; no bath-output heat ledger."}


def reset_cycle_examples():
    values = {"1": ONE, "-1": gaussian(-1),
              "i": gaussian(0, 1), "-i": gaussian(0, -1)}
    def factor(rows, denominator):
        return [[times(values[x], F(1, denominator)) for x in row.split()]
                for row in rows]
    a2 = factor(["1 1", "1 i"], 2)
    b2 = factor(["1 1", "1 -i"], 2)
    a3 = factor(["1 1 1", "1 i -1", "i 1 -i"], 3)
    b3 = [[conjugate(x) for x in row] for row in a3]
    return [reset_cycle_example(a, b, label) for a, b, label in (
        (a2, a2, "identical complex qubit resets"),
        (a2, b2, "distinct complex qubit resets"),
        (a3, a3, "identical complex qutrit resets"),
        (a3, b3, "distinct complex qutrit resets"))]


def random_receiver_examples():
    """Finite global-parity and clean-Fredkin-bus identities, not free ports."""
    pairs_checked = control_units = code_pairs = code_units = 0
    for n in range(1, 8):
        for a, b in product(product(range(2), repeat=n), repeat=2):
            error = tuple(x ^ y for x, y in zip(a, b))
            parity = sum(error) % 2
            # At each site X Y=iZ, Y X=-iZ; equal factors multiply to I.
            forward = sum(y-x for x, y in zip(a, b)) % 4
            reverse = (-forward) % 4
            assert (reverse-forward) % 4 == 2*parity
            switched = [forward, reverse]
            # Controlled X^tensor n conjugates the common Z^error product.
            ordinary = [forward, (forward+2*parity) % 4]
            for r, c in product(range(2), repeat=2):
                assert (switched[r]-switched[c]) % 4 == (ordinary[r]-ordinary[c]) % 4
                control_units += 1
                # Code basis |0^n>,|1^n>: the read parity and one Z correct it.
                assert ((sum(error)+parity)*(r-c)) % 2 == 0
                code_units += 1
            code_pairs += 1
            pairs_checked += 1

    bus_branches = bus_basis_coefficients = bus_matrix_units = 0
    probabilities = {}
    for n in range(1, 9):
        branch_probability = F(1, 2**(n+1))
        total_probability = F(0)
        for measurements, bus_x in product(product(range(2), repeat=n), range(2)):
            parity = sum(measurements) % 2
            signs = []
            for c in range(2):
                # Omitted common amplitude is 2^(-(n+1)/2). Each local
                # auxiliary starts in 1 and is measured in its X basis.
                raw = (sum(m*(1-c) for m in measurements)+bus_x*c) % 2
                corrected = (raw+(parity+bus_x)*c) % 2
                assert corrected == parity
                signs.append(corrected)
                bus_basis_coefficients += 1
            for r, c in product(range(2), repeat=2):
                assert (signs[r]-signs[c]) % 2 == 0
                bus_matrix_units += 1
            # Every corrected Kraus is a scalar times the same isometry;
            # this is its exact K^dagger K weight, independent of input.
            total_probability += branch_probability
            bus_branches += 1
        assert total_probability == 1
        probabilities[str(n)] = str(branch_probability)

    fredkin_basis_states = 0
    for c, t, a in product(range(2), repeat=3):
        # F Z_T F Z_T = P0 I + P1 Z_T Z_A; F swaps targets only if c=1.
        t_after, a_after = ((a, t) if c else (t, a))
        phase = (t+t_after) % 2
        t_final, a_final = ((a_after, t_after) if c else (t_after, a_after))
        assert (t_final, a_final) == (t, a)
        assert phase == (c*(t+a)) % 2
        if a == 0:
            assert phase == c*t
        fredkin_basis_states += 1

    # All Hadamards occur in even pairs, so these complete local SWAP
    # synthesis identities use Gaussian rationals without square roots.
    i2, x, _, z = pauli_basis(1)
    hraw = matrix_sum([x, z], 2)
    cz = diagonal_blocks(i2, z)
    target_h = tensor(i2, hraw)
    cnot = scale(matmul(target_h, matmul(cz, target_h)), F(1, 2))
    expected_cnot = diagonal_blocks(i2, x)
    assert cnot == expected_cnot
    both_h = tensor(hraw, hraw)
    reverse_cnot = scale(matmul(both_h, matmul(cnot, both_h)), F(1, 4))
    swap = matmul(cnot, matmul(reverse_cnot, cnot))
    expected_swap = zeros(4, 4)
    for c, t in product(range(2), repeat=2):
        expected_swap[2*t+c][2*c+t] = ONE
    assert swap == expected_swap

    return {
        "product_channel_sites_n": list(range(1, 8)),
        "module_label_Pauli_string_pairs": pairs_checked,
        "full_control_matrix_unit_phase_coefficients": control_units,
        "GHZ_code_error_and_correction_pairs": code_pairs,
        "GHZ_code_matrix_unit_coefficients": code_units,
        "clean_bus_sites_n": list(range(1, 9)),
        "clean_bus_measurement_branches": bus_branches,
        "clean_bus_basis_coefficients": bus_basis_coefficients,
        "clean_bus_corrected_logical_matrix_unit_coefficients": bus_matrix_units,
        "clean_bus_branch_probability_by_n": probabilities,
        "clean_bus_total_branch_probability_per_n": "1",
        "Fredkin_CZ_complete_basis_actions": fredkin_basis_states,
        "local_source_CNOT_reverse_CNOT_and_SWAP_identities": 3,
        "source_SWAP_Fredkin_count": 6,
        "scope": ("Exact finite Pauli/control/code phases, normalized clean-bus "
                  "branch isometries and local Fredkin-to-CZ/SWAP synthesis. "
                  "Universal identities, late-choice LOCC correctness, physical "
                  "controller ports, bus/fanout graph, channel extensions and "
                  "hardware costs remain analytic assumptions/proofs. No free "
                  "side-wire equivalence or native advantage is certified."),
    }


def late_record_guard_examples():
    """Finite operator identities supporting the analytic Markov guard bound."""
    def complex_scale(a, value):
        value = gaussian(value) if not isinstance(value, tuple) else value
        return [[multiply(value, x) for x in row] for row in a]

    def total(matrices, dimension):
        return matrix_sum(list(matrices), dimension)

    def local(a, site, emitters):
        out = [[ONE]]
        for j in range(emitters):
            out = tensor(out, a if j == site else identity(2))
        return out

    def generator_adjoint(hamiltonian, jumps, observable):
        d = len(observable)
        commutator = matrix_sum([
            matmul(hamiltonian, observable),
            scale(matmul(observable, hamiltonian), -1)], d)
        terms = [complex_scale(commutator, gaussian(0, 1))]
        for jump in jumps:
            jd = adjoint(jump)
            rate = matmul(jd, jump)
            terms.append(matrix_sum([
                matmul(jd, matmul(observable, jump)),
                scale(matmul(rate, observable), F(-1, 2)),
                scale(matmul(observable, rate), F(-1, 2))], d))
        return matrix_sum(terms, d)

    cases = []
    lowering = [[ZERO, ONE], [ZERO, ZERO]]
    for m in (2, 3):
        d = 2**m
        lowers = [local(lowering, j, m) for j in range(m)]
        occupations = [matmul(adjoint(a), a) for a in lowers]
        number = matrix_sum(occupations, d)
        hamiltonian = total((scale(a, F(j+1, 7))
                             for j, a in enumerate(occupations)), d)
        for i in range(m):
            for j in range(i+1, m):
                exchange = matmul(adjoint(lowers[i]), lowers[j])
                coefficient = gaussian(F(i+j+1, 9), F(j-i, 11))
                hamiltonian = matrix_sum([
                    hamiltonian, complex_scale(exchange, coefficient),
                    complex_scale(adjoint(exchange), conjugate(coefficient))], d)
        assert hamiltonian == adjoint(hamiltonian)
        assert matmul(hamiltonian, number) == matmul(number, hamiltonian)
        guided = [total((complex_scale(a, gaussian(F(j+k+1, 5), F((j+1)*(k+1), 13)))
                         for j, a in enumerate(lowers)), d) for k in range(2)]
        loss_amplitudes = [F(j+1, j+2) for j in range(m)]
        losses = [scale(a, b) for a, b in zip(lowers, loss_amplitudes)]
        dephasing = [scale(a, F(j+1, 3)) for j, a in enumerate(occupations)]
        dephasing.append(scale(matmul(occupations[0], occupations[1]), F(2, 7)))
        jumps = guided+losses+dephasing
        actual = generator_adjoint(hamiltonian, jumps, number)
        radiative_rate = total((matmul(adjoint(a), a) for a in guided+losses), d)
        assert actual == scale(radiative_rate, -1)
        loss_floor = min(a*a for a in loss_amplitudes)
        positive_remainder = matrix_sum([
            total((matmul(adjoint(a), a) for a in guided), d),
            total((scale(a, b*b-loss_floor)
                   for a, b in zip(occupations, loss_amplitudes)), d)], d)
        assert matrix_sum([actual, scale(number, loss_floor)], d) == scale(positive_remainder, -1)
        assert all(jump[r][0] == ZERO for jump in jumps for r in range(d))
        assert all(hamiltonian[r][0] == ZERO for r in range(d))
        cases.append({"emitters": m, "complete_number_operator_entries": d*d,
                      "radiative_jumps": len(guided+losses),
                      "ground_vacuum_entries": len(jumps)*d,
                      "certified_local_loss_floor": str(loss_floor)})

    # Nominal reciprocal two-emitter Gram, in units of 2*pi GHz. This
    # enclosure is an exact model calculation, not an uncertainty fit.
    gamma1, gamma2, floor = F(388, 1000), F(345, 1000), F(99, 1000)
    guided1, guided2 = gamma1*F(95, 100), gamma2*F(85, 100)
    # cos^2(4*pi/5)=(3+sqrt(5))/8 < 21/32, since sqrt(5)<9/4.
    assert F(5) < F(9, 4)**2
    determinant_lower = ((gamma1-floor)*(gamma2-floor)
                         -guided1*guided2*F(21, 32))
    assert gamma1-floor > 0 and gamma2-floor > 0
    assert determinant_lower == F(101541, 640000000) > 0

    # A declared uncertainty box, not a confidence region inferred from
    # the source's point estimates. Extremal diagonals and off-diagonal
    # magnitude independently give a sufficient PSD enclosure.
    box_floor = F(95, 1000)
    lower1, lower2 = F(386, 1000), F(343, 1000)
    upper1, upper2 = F(390, 1000), F(347, 1000)
    box_determinant_lower = ((lower1-box_floor)*(lower2-box_floor)
        -upper1*upper2*F(95, 100)*F(85, 100)*F(21, 32))
    assert lower1 > box_floor and lower2 > box_floor
    assert box_determinant_lower == F(580701, 1280000000) > 0

    # Lossless nearly dark modes give no positive dimension-only decay
    # rate. The normalized antisymmetric state's population decay is
    # exp(-2*epsilon^2*t); the vector below omits its common sqrt(2).
    s1, s2 = [local(lowering, j, 2) for j in range(2)]
    dark = [ZERO, gaussian(-1), ONE, ZERO]
    def apply_to_dark(a):
        answer = []
        for row in a:
            value = ZERO
            for x, y in zip(row, dark):
                value = add(value, multiply(x, y))
            answer.append(value)
        return answer

    for epsilon in (F(1, 2), F(1, 7), F(1, 31)):
        plus = matrix_sum([s1, s2], 4)
        minus = scale(matrix_sum([s1, scale(s2, -1)], 4), epsilon)
        rate = matrix_sum([matmul(adjoint(plus), plus),
                           matmul(adjoint(minus), minus)], 4)
        assert apply_to_dark(plus) == [ZERO]*4
        assert apply_to_dark(rate) == [times(x, 2*epsilon*epsilon) for x in dark]

    return {"number_operator_cases": cases,
            "nominal_Gram_floor_in_2pi_GHz": str(floor),
            "nominal_Gram_determinant_lower": str(determinant_lower),
            "declared_box_Gram_floor_in_2pi_GHz": str(box_floor),
            "declared_box_Gram_determinant_lower": str(box_determinant_lower),
            "near_dark_eigenvalue_examples": 3,
            "scope": ("Exact finite full-excitation number identities, positive "
                      "loss remainder, vacuum ground and nominal Gram enclosure. "
                      "Semigroup/future-record bounds, compact-input errors and "
                      "physical model validity remain analytic; no fitted bath, "
                      "measured guard interval or hardware advantage is certified.")}


def chiral_parity_examples():
    """Elastic QND MZI/two-click and quarter-phase photon-bus guards."""
    def minus(a, b):
        return add(a, times(b, -1))

    def norm(a):
        value = multiply(a, conjugate(a))
        assert value[1] == 0
        return value[0]

    def diagonal_product(a, b):
        return [multiply(x, y) for x, y in zip(a, b)]

    def cp_coefficient(k, i, j):
        return multiply(k[i], conjugate(k[j]))

    transmissions = (ZERO, gaussian(-1), ONE, gaussian(F(1, 2)),
                     gaussian(F(-4, 5)), gaussian(F(3, 5), F(4, 5)),
                     gaussian(F(1, 2), F(1, 2)))
    even = [ONE, ZERO, ZERO, ONE]
    odd = [ZERO, ONE, ONE, ZERO]
    z0 = [ONE, ONE, gaussian(-1), gaussian(-1)]
    z1 = [ONE, gaussian(-1), ONE, gaussian(-1)]
    two_click_units = direction_units = bus_units = 0
    for t0, t1 in product(transmissions, repeat=2):
        # Separate-arm ordinary MZI; unmonitored arm loss completes its effect.
        d0, d1 = [ONE, ONE, t0, t0], [ONE, t1, ONE, t1]
        kp = [times(add(a, b), F(1, 2)) for a, b in zip(d0, d1)]
        km = [times(minus(a, b), F(1, 2)) for a, b in zip(d0, d1)]
        loss = (F(0), (1-norm(t1))/2, (1-norm(t0))/2,
                (2-norm(t0)-norm(t1))/2)
        assert all(value >= 0 for value in loss)
        assert all(norm(kp[i])+norm(km[i])+loss[i] == 1 for i in range(4))
        t = times(add(t0, t1), F(1, 2))
        a = times(multiply(add(ONE, t0), add(ONE, t1)), F(1, 4))
        b = times(multiply(minus(ONE, t0), minus(ONE, t1)), F(1, 4))
        for k, expected in ((kp, [t, a, a, t]),
                            (km, [ZERO, times(b, -1), times(b, -1), ZERO])):
            # F=X0X1 conjugation reverses the diagonal before composition.
            actual = diagonal_product(k[::-1], k)
            assert actual == expected
            for i, j in product(range(4), repeat=2):
                assert cp_coefficient(actual, i, j) == cp_coefficient(expected, i, j)
                two_click_units += 1

        # Complementary-direction model uses both spins per photon history.
        # These monitored photon/spin operators commute in fixed order;
        # no equality of photon-loss branches is inferred.
        v0 = [t0, t0, ONE, ONE, ONE, ONE, t0, t0]
        v1 = [t1, ONE, t1, ONE, ONE, t1, ONE, t1]
        dr = [multiply(t0, t1), t0, t1, ONE]
        dl = [ONE, t1, t0, multiply(t0, t1)]
        fixed = diagonal_product(v0, v1)
        assert fixed == diagonal_product(v1, v0) == dr+dl
        for i, j in product(range(8), repeat=2):
            assert cp_coefficient(fixed, i, j) == cp_coefficient(dr+dl, i, j)
            bus_units += 1
        u = times(add(ONE, multiply(t0, t1)), F(1, 2))
        v = times(add(t0, t1), F(1, 2))
        w = times(minus(multiply(t0, t1), ONE), F(1, 2))
        z = times(minus(t0, t1), F(1, 2))
        actual_flags = ([times(add(x, y), F(1, 2)) for x, y in zip(dr, dl)],
                        [times(minus(x, y), F(1, 2)) for x, y in zip(dr, dl)])
        expected_flags = ([u, v, v, u], [w, z, times(z, -1), times(w, -1)])
        for actual, expected in zip(actual_flags, expected_flags):
            assert actual == expected
            for i, j in product(range(4), repeat=2):
                assert cp_coefficient(actual, i, j) == cp_coefficient(expected, i, j)
                direction_units += 1

    # Ideal separate-arm MZI correction is the full parity instrument.
    kp = [times(add(a, b), F(1, 2)) for a, b in zip(z0, z1)]
    km = [times(minus(a, b), F(1, 2)) for a, b in zip(z0, z1)]
    assert diagonal_product(z0, kp) == even
    assert diagonal_product(z0, km) == odd

    # Quarter phase gives both Bell outputs, while pi gives no order flag.
    for transmission in (gaussian(0, 1), gaussian(-1)):
        dr = [multiply(transmission, transmission), transmission, transmission, ONE]
        dl = [ONE, transmission, transmission, multiply(transmission, transmission)]
        kp = [times(add(a, b), F(1, 2)) for a, b in zip(dr, dl)]
        km = [times(minus(a, b), F(1, 2)) for a, b in zip(dr, dl)]
        if transmission == gaussian(0, 1):
            assert kp == [multiply(gaussian(0, 1), value) for value in odd]
            assert km == [times(value, -1) for value in diagonal_product(z0, even)]
            assert sum(map(norm, kp))/4 == sum(map(norm, km))/4 == F(1, 2)
        else:
            assert kp == diagonal_product(z0, z1) and km == [ZERO]*4

    # Same-forward-rail early/late echo with arbitrary spin/frequency coherence.
    # Here the two frequency modes have distinct complex monitored amplitudes.
    # The matrix identity includes both photon bins and every spin input.
    echo_units = 0
    frequency_cases = (
        ((gaussian(F(3, 5), F(4, 5)), gaussian(-1)),
         (gaussian(F(1, 2), F(1, 2)), gaussian(0, 1))),
        ((gaussian(0, 1), gaussian(F(3, 5), F(4, 5))),
         (gaussian(0, 1), gaussian(F(5, 13), F(12, 13)))),
    )
    spin_flip = zeros(4, 4)
    for j in range(4):
        spin_flip[3-j][j] = ONE
    flip = tensor(identity(2), tensor(spin_flip, identity(2)))
    for first, second in frequency_cases:
        right = [[multiply(first[w], second[w]), first[w], second[w], ONE]
                 for w in range(2)]
        left = [[ONE, second[w], first[w], multiply(first[w], second[w])]
                for w in range(2)]
        dr, dl = zeros(8, 8), zeros(8, 8)
        for s, w in product(range(4), range(2)):
            dr[2*s+w][2*s+w] = right[w][s]
            dl[2*s+w][2*s+w] = left[w][s]
        early = diagonal_blocks(dr, identity(8))
        late = diagonal_blocks(identity(8), dr)
        actual = matmul(flip, matmul(late, matmul(flip, early)))
        expected = diagonal_blocks(dr, dl)
        assert actual == expected
        assert all(actual[i][j] == ZERO for i, j in product(range(16), repeat=2) if i != j)
        for i, j in product(range(16), repeat=2):
            assert multiply(actual[i][i], conjugate(actual[j][j])) == multiply(
                expected[i][i], conjugate(expected[j][j]))
            echo_units += 1

    # In the ideal lossless model, a passive time-bin analyzer's central
    # window has exactly half the complete X-readout effect. A same-order
    # resonant pair versus a bypass also gives the complete parity map.
    resonance_pair = diagonal_product(z0, z1)
    bypass_plus = [times(add(ONE, x), F(1, 2)) for x in resonance_pair]
    bypass_minus = [times(minus(ONE, x), F(1, 2)) for x in resonance_pair]
    assert bypass_plus == even and bypass_minus == odd
    assert all((norm(bypass_plus[i])+norm(bypass_minus[i]))/2 == F(1, 2)
               for i in range(4))

    return {"complex_transmission_pairs": len(transmissions)**2,
            "two_click_CP_matrix_unit_coefficients": two_click_units,
            "direction_flag_CP_matrix_unit_coefficients": direction_units,
            "full_photon_bus_CP_matrix_unit_coefficients": bus_units,
            "ideal_parity_maps": 2, "quarter_and_pi_phase_guards": 2,
            "same_rail_frequency_echo_cases": len(frequency_cases),
            "same_rail_echo_CP_matrix_unit_coefficients": echo_units,
            "resonant_external_bypass_parity_maps": 2,
            "passive_time_bin_central_effect": "1/2",
            "scope": ("Exact elastic QND monochromatic stationary MZI/two-click "
                      "filters, monitored complementary-direction photon-bus and "
                      "same-rail early/late echo identities with frequency coherence. "
                      "Finite pulses, emitted records, native ports, calibration, "
                      "source/detection costs and delivered rates remain analytic.")}


def raman_sprint_examples():
    """Ideal helper baselines and flat symmetric accepted Raman instruments.

    A node preserves the independent helper degree by hypothesis.  The
    physical port, known Z dressings, Bell readout, loss/reset and timing
    costs are analytic assumptions, not certified by these matrix checks.
    """
    def subtract(a, b):
        return add(a, times(b, -1))

    def norm2(vector):
        out = ZERO
        for value in vector:
            out = add(out, multiply(conjugate(value), value))
        assert out[1] == 0
        return out[0]

    def mv(matrix, vector):
        return [sum_gaussian(multiply(a, b) for a, b in zip(row, vector))
                for row in matrix]

    def sum_gaussian(values):
        out = ZERO
        for value in values:
            out = add(out, value)
        return out

    def bits(index, n):
        return [(index >> (n-1-j)) & 1 for j in range(n)]

    def index(bitstring):
        out = 0
        for bit in bitstring:
            out = 2*out+bit
        return out

    def embed(gate, first, second, n):
        out = zeros(2**n, 2**n)
        for col in range(2**n):
            source = bits(col, n)
            local_col = 2*source[first]+source[second]
            for local_row in range(4):
                target = source[:]
                target[first], target[second] = divmod(local_row, 2)
                out[index(target)][col] = gate[local_row][local_col]
        return out

    # Complete radiative-channel rank-one Lambda resolvent at fixed total
    # energy.  Unequal complex legs and unobserved radiative rows are kept;
    # this does not turn dephasing or a recurrent field into disappearance.
    resolvent_cases = resolvent_unit_entries = monitored_gram_entries = 0
    dark_cases = 0
    radiative_legs = (
        (gaussian(1), gaussian(0, 2)),
        (gaussian(F(3, 5), F(4, 5)), gaussian(F(1, 2)), gaussian(0, F(3, 2))),
        (gaussian(1), gaussian(1, 1), gaussian(F(2, 3), F(-1, 4)),
         gaussian(F(-2, 5), F(3, 7))),
    )
    for v in radiative_legs:
        dimension = len(v)
        gamma = norm2(v)
        assert gamma > 0
        vv = [[multiply(x, conjugate(y)) for y in v] for x in v]
        for delta in (F(0), F(2, 7), F(-5, 3)):
            denominator = delta*delta+gamma*gamma/4
            # c=-i/(delta+i gamma/2), reconstructed by exact real fractions.
            coefficient = gaussian(-gamma/(2*denominator), -delta/denominator)
            scalar_denominator = gaussian(delta, gamma/2)
            assert multiply(coefficient, scalar_denominator) == gaussian(0, -1)
            scattering = [[add(ONE if i == j else ZERO,
                               multiply(coefficient, vv[i][j]))
                           for j in range(dimension)] for i in range(dimension)]
            assert matmul(adjoint(scattering), scattering) == identity(dimension)
            assert matmul(scattering, adjoint(scattering)) == identity(dimension)
            resolvent_unit_entries += 2*dimension*dimension
            bright_phase = add(ONE, times(coefficient, gamma))
            assert multiply(bright_phase, conjugate(bright_phase)) == ONE
            assert mv(scattering, v) == [multiply(bright_phase, x) for x in v]
            for j in range(1, dimension):
                dark = [ZERO]*dimension
                dark[0], dark[j] = times(conjugate(v[j]), -1), conjugate(v[0])
                assert sum_gaussian(multiply(conjugate(x), y) for x, y in zip(v, dark)) == ZERO
                assert mv(scattering, dark) == dark
                dark_cases += 1
            # Incident photons occupy monitored channels.  The other rows
            # are retained as loss amplitudes, whose Gram is exactly the
            # monitored contraction defect, including off-diagonal phases.
            for monitored in range(1, dimension):
                accepted = [row[:monitored] for row in scattering[:monitored]]
                lost = [row[:monitored] for row in scattering[monitored:]]
                defect = matrix_sum([identity(monitored),
                    scale(matmul(adjoint(accepted), accepted), -1)], monitored)
                assert defect == matmul(adjoint(lost), lost)
                monitored_gram_entries += monitored*monitored
            resolvent_cases += 1

    swap = zeros(4, 4)
    cnot = zeros(4, 4)
    for a, b in product(range(2), repeat=2):
        swap[2*b+a][2*a+b] = ONE
        cnot[2*a+(a ^ b)][2*a+b] = ONE
    z_pair = [[times(value, (-1)**(bits(i, 2)[0]+bits(i, 2)[1]))
               for value in row] for i, row in enumerate(swap)]
    # Raw resonant SPRINT is a SWAP with known local Z_P Z_S phases.
    raw_resonant = [row[:] for row in identity(4)]
    raw_resonant[1][1] = raw_resonant[2][2] = ZERO
    raw_resonant[1][2] = raw_resonant[2][1] = gaussian(-1)
    assert raw_resonant == z_pair
    assert matmul(raw_resonant, raw_resonant) == identity(4)

    # Literal dressed SWAPs, P,A,B; order branch normalization is 1/2.
    a, b = embed(swap, 0, 1, 3), embed(swap, 0, 2, 3)
    source = [ZERO]*8
    source[4] = ONE
    ba, ab = mv(matmul(b, a), source), mv(matmul(a, b), source)
    switched = []
    for sign in (1, -1):
        actual = [times(add(x, times(y, sign)), F(1, 2)) for x, y in zip(ba, ab)]
        expected = [ZERO]*8
        expected[2], expected[1] = gaussian(F(1, 2)), gaussian(F(sign, 2))
        assert actual == expected and norm2(actual) == F(1, 2)
        switched.append(actual)

    # Ordinary ideal fanout with the same independent helper: O,P,A,B.
    # The Bell input is unnormalized; the eventual O-X bra supplies the
    # second 1/sqrt(2), so the final branch has rational factor 1/2.
    fan_source = [ZERO]*16
    fan_source[0] = fan_source[12] = ONE
    fanout = matmul(embed(swap, 1, 3, 4), matmul(embed(cnot, 0, 1, 4),
                     embed(swap, 1, 2, 4)))
    fan_output = mv(fanout, fan_source)
    fanout_units = 0
    for sign in (1, -1):
        branch = [times(add(fan_output[i], times(fan_output[8+i], sign)), F(1, 2))
                  for i in range(8)]
        expected = [ZERO]*8
        expected[0], expected[3] = gaussian(F(1, 2)), gaussian(F(sign, 2))
        assert branch == expected and norm2(branch) == F(1, 2)
        for i, j in product(range(8), repeat=2):
            assert multiply(branch[i], conjugate(branch[j])) == multiply(
                expected[i], conjugate(expected[j]))
            fanout_units += 1

    # Arbitrary unknown A,B input: one flying P with independent clean Q,
    # initial Bell(P,Q), two serial SWAPs and complete joint Bell readout.
    # Q is the second photonic logical degree, not a new matter memory.
    # Ordering here is P,Q,A,B.  Prepare/bra normalization multiplies to 1/2.
    prepare = zeros(16, 4)
    for matter, p in product(range(4), range(2)):
        prepare[12*p+matter][matter] = ONE
    bus = matmul(embed(swap, 0, 3, 4), embed(swap, 0, 2, 4))
    propagated = matmul(bus, prepare)
    corrected = []
    teleportation_units = 0
    for m, n in product(range(2), repeat=2):
        bell_bra = zeros(4, 16)
        for p, matter in product(range(2), range(4)):
            q = p ^ m
            bell_bra[matter][8*p+4*q+matter] = gaussian((-1)**(n*p))
        branch = scale(matmul(bell_bra, propagated), F(1, 2))
        correction = zeros(4, 4)
        for aa, bb in product(range(2), repeat=2):
            # Z^n X^m reverses the teleported X^m Z^n on memory A.
            correction[2*(aa ^ m)+bb][2*aa+bb] = gaussian((-1)**(n*(aa ^ m)))
        branch = matmul(correction, branch)
        expected = scale(swap, F(1, 2))
        assert branch == expected
        assert matmul(adjoint(branch), branch) == scale(identity(4), F(1, 4))
        corrected.append(branch)
        for out_i, out_j, in_i, in_j in product(range(4), repeat=4):
            assert multiply(branch[out_i][in_i], conjugate(branch[out_j][in_j])) == \
                times(multiply(swap[out_i][in_i], conjugate(swap[out_j][in_j])), F(1, 4))
            teleportation_units += 1
    assert choi(corrected, 4) == choi([swap], 4)
    assert matrix_sum([matmul(adjoint(k), k) for k in corrected], 4) == identity(4)

    # The noisy model has raw accepted equal-state identity and odd block
    # t I+r X.  This is not replaced by the ideal dressed-SWAP circuit.
    betas = (F(0), F(1, 10), F(1, 3), F(1, 2), F(7, 10), F(9, 10), F(1))
    lossy_units = contraction_cases = 0
    records = []
    for beta in betas:
        t, r = 1-beta, -beta
        node = identity(4)
        node[1][1] = node[2][2] = gaussian(t)
        node[1][2] = node[2][1] = gaussian(r)
        rejection = matrix_sum([identity(4), scale(matmul(adjoint(node), node), -1)], 4)
        # Exact PSD factorization: 2 beta(1-beta) |01+10><01+10|.
        loss_vector = [ZERO, ONE, ONE, ZERO]
        expected_rejection = zeros(4, 4)
        add_outer(expected_rejection, loss_vector, 2*beta*(1-beta))
        assert rejection == expected_rejection and 2*beta*(1-beta) >= 0
        aa, bb = embed(node, 0, 1, 3), embed(node, 0, 2, 3)
        baa, abb = matmul(bb, aa), matmul(aa, bb)
        ra, rb = embed(rejection, 0, 1, 3), embed(rejection, 0, 2, 3)
        accepted_effect = scale(matrix_sum([matmul(adjoint(baa), baa),
                                             matmul(adjoint(abb), abb)], 8), F(1, 2))
        reject_effect = matrix_sum([identity(8), scale(accepted_effect, -1)], 8)
        psd_decomposition = scale(matrix_sum([ra, matmul(adjoint(aa), matmul(rb, aa)),
                                             rb, matmul(adjoint(bb), matmul(ra, bb))], 8), F(1, 2))
        assert reject_effect == psd_decomposition
        contraction_cases += 1
        va, vb = mv(baa, source), mv(abb, source)
        total = bell = F(0)
        flag_probabilities = []
        for sign in (1, -1):
            vector = [times(add(x, times(y, sign)), F(1, 2)) for x, y in zip(va, vb)]
            expected = [ZERO]*8
            expected[4] = gaussian(t*t if sign == 1 else 0)
            expected[2] = gaussian(r*(1+sign*t)/2)
            expected[1] = gaussian(r*(t+sign)/2)
            assert vector == expected
            # Resolve every photon P and order-X outcome.  P=0 is exact
            # Bell, while P=1,+ is a non-Bell residual and is not accepted.
            expected_bell = r*r*(1+sign*t)**2/2
            actual_bell = norm2(vector[:4])
            actual_nonbell = norm2(vector[4:])
            assert actual_bell == expected_bell
            assert actual_nonbell == (t**4 if sign == 1 else 0)
            if actual_bell:
                assert vector[0] == vector[3] == ZERO
                assert vector[1] == times(vector[2], sign)
            total += norm2(vector)
            bell += actual_bell
            flag_probabilities.append(str(actual_bell))
            for i, j in product(range(8), repeat=2):
                assert multiply(vector[i], conjugate(vector[j])) == multiply(
                    expected[i], conjugate(expected[j]))
                lossy_units += 1
        assert bell == beta*beta*(1+(1-beta)**2)
        assert total == bell+t**4 <= 1
        # Restricted helper-free serial detuning optimum.  The continuous
        # optimum proof is analytic; these identities guard its arithmetic.
        serial_optimum = 2*beta*beta/(2-t*t)
        assert bell-serial_optimum == beta*beta*t*t*(1-t*t)/(2-t*t)
        two_which_node_attempts = 2*beta*beta-beta**4
        assert two_which_node_attempts-bell == 2*beta**3*(1-beta)
        records.append({"beta": str(beta), "Bell_flags": flag_probabilities,
                        "total_Bell_probability": str(bell),
                        "restricted_serial_detuning_optimum": str(serial_optimum),
                        "two_which_node_attempts_probability": str(two_which_node_attempts),
                        "surviving_nonBell_probability": str(t**4),
                        "rejected_loss_probability": str(1-total)})
    return {"full_radiative_Lambda_resolvent_cases": resolvent_cases,
            "full_radiative_unitarity_entries": resolvent_unit_entries,
            "full_radiative_dark_vector_cases": dark_cases,
            "monitored_loss_Gram_entries": monitored_gram_entries,
            "ideal_resonant_local_phase_guard": 1,
            "ideal_switch_Bell_flags": 2,
            "ideal_ordinary_fanout_CP_coefficients": fanout_units,
            "ordinary_remote_SWAP_Bell_outcomes": len(corrected),
            "ordinary_remote_SWAP_CP_matrix_unit_coefficients": teleportation_units,
            "flat_lossy_contraction_factorizations": contraction_cases,
            "flat_lossy_complete_survivor_CP_coefficients": lossy_units,
            "flat_lossy_Bell_probabilities": records,
            "scope": ("Exact finite full-radiative rank-one Lambda resolvents and "
                      "monitored loss-Gram identities; ideal same-helper ordinary Bell fanout and reference-complete "
                      "remote-SWAP teleportation, with known local Z dressings. Flat "
                      "symmetric accepted Raman/loss branch identities do not assert "
                      "that those ideal ordinary protocols dominate the noisy switch. "
                      "Actual helper-preserving ports, finite-frequency records, loss "
                      "dilation, controls, readout and delivered rates remain analytic.")}


def raman_ordinary_gate_programs():
    """Ideal helper-preserving SWAP gate programs on every unknown ABR.

    Hadamard/Bell square roots are kept as explicit squared normalization:
    F4/F8 CZ numerators have CP weight1/8, F16 numerators weight1/16.
    Failures, source coherence, uniform keys and extra query windows are
    separate instruments/resources, not a noisy Raman or hardware theorem.
    """
    def integer_matrix(rows):
        return [[gaussian(x) for x in row] for row in rows]

    def pauli(xa=0, xb=0, za=0, zb=0):
        out = zeros(4, 4)
        for a, b in product(range(2), repeat=2):
            out[2*(a ^ xa)+(b ^ xb)][2*a+b] = gaussian((-1)**(za*a+zb*b))
        return out

    def direct_branch(v, m, n, p=None, source_label=None):
        # Bell source, first SWAP: A=d,D=a,E0=d,E1=0.
        # After V and second SWAP: A=d,B=x,D=b,E0=f,E1=p.
        out = zeros(4, 4)
        for a, b, d, x, f in product(range(2), repeat=5):
            if source_label is not None and d != source_label:
                continue
            if f != (b ^ m):
                continue
            value = v[2*x+f][2*a+d] if p is None else v[4*x+2*f+p][4*a+2*d]
            out[2*d+x][2*a+b] = add(out[2*d+x][2*a+b], times(value, (-1)**(n*b)))
        return out

    def cp_guard(numerator, target, weight):
        assert numerator == target
        assert scale(matmul(adjoint(numerator), numerator), weight) == scale(identity(4), weight)
        count = 0
        for i, j, a, b in product(range(4), repeat=4):
            actual = times(multiply(numerator[i][a], conjugate(numerator[j][b])), weight)
            desired = times(multiply(target[i][a], conjugate(target[j][b])), weight)
            assert actual == desired
            count += 1
        return count

    def swap_state(state, first, second):
        out = {}
        for bits, value in state.items():
            result = list(bits)
            result[first], result[second] = result[second], result[first]
            key = tuple(result)
            out[key] = add(out.get(key, ZERO), value)
        return out

    def arbitrary_branch(u, ma, na, mb, nb):
        # Registers A,B,D,E,F,G; two unnormalized Bell sources.
        # Source and two normalized Bell bras together supply factor1/4.
        # Equivalence to the canonical staged Bell preparation is checked
        # below before B, with common source amplitude normalization1/2.
        out = zeros(4, 4)
        for a, b in product(range(2), repeat=2):
            state = {(a, b, d, d, f, f): ONE for d, f in product(range(2), repeat=2)}
            for pair in ((0, 2), (2, 4), (1, 2)):
                state = swap_state(state, *pair)
            processed = {}
            for bits, value in state.items():
                column = 2*bits[4]+bits[2]
                for x, y in product(range(2), repeat=2):
                    result = list(bits)
                    result[4], result[2] = x, y
                    key = tuple(result)
                    processed[key] = add(processed.get(key, ZERO), multiply(u[2*x+y][column], value))
            for (ao, bo, d, e, f, g), value in processed.items():
                if e == (f ^ ma) and g == (d ^ mb):
                    out[2*ao+bo][2*a+b] = add(out[2*ao+bo][2*a+b],
                                              times(value, (-1)**(na*f+nb*d)))
        return out

    # Canonical RS18 starts Bell(DE),F=G=0, then after AD/DF prepares
    # Bell(D,G) by H_D/CNOT_D->G. Compare before B with the convenient
    # preprepared Bell(DE)Bell(FG) form used by arbitrary_branch.
    for a, b in product(range(2), repeat=2):
        prepared = {(a, b, d, d, f, f): ONE for d, f in product(range(2), repeat=2)}
        staged = {(a, b, d, d, 0, 0): ONE for d in range(2)}
        for pair in ((0, 2), (2, 4)):
            prepared = swap_state(prepared, *pair)
            staged = swap_state(staged, *pair)
        expanded = {}
        for bits, value in staged.items():
            assert bits[2] == bits[5] == 0
            for h in range(2):
                result = list(bits)
                result[2] = result[5] = h
                key = tuple(result)
                expanded[key] = add(expanded.get(key, ZERO), value)
        assert expanded == prepared  # both have physical amplitude factor1/2
    cz = identity(4)
    cz[3][3] = gaussian(-1)
    # F4: a genuine accepted contraction, with rejected odd modes halted
    # BEFORE the B contact. It is not a closed four-mode unitary.
    even_h = zeros(4, 4)
    even_h[0][0] = even_h[0][3] = even_h[3][0] = ONE
    even_h[3][3] = gaussian(-1)
    even, odd = zeros(4, 4), zeros(4, 4)
    for j in range(4):
        (even if j in (0, 3) else odd)[j][j] = ONE
    assert scale(matmul(adjoint(even_h), even_h), F(1, 2)) == even
    assert matrix_sum([even, matmul(adjoint(odd), odd)], 4) == identity(4)
    f4_units, f4_effects = 0, []
    for m, n in product(range(2), repeat=2):
        raw = direct_branch(even_h, m, n)
        expected = matmul(matmul(pauli(xb=m), cz), pauli(za=m, zb=n))
        assert raw == expected
        correction = matmul(pauli(za=m, zb=n), pauli(xb=m))
        f4_units += cp_guard(matmul(correction, raw), cz, F(1, 8))
        f4_effects.append(scale(matmul(adjoint(raw), raw), F(1, 8)))
    assert matrix_sum(f4_effects, 4) == scale(identity(4), F(1, 2))
    rejected = []
    for a, d in ((0, 1), (1, 0)):
        branch = zeros(4, 4)
        for b in range(2):
            branch[2*d+b][2*a+b] = ONE
        rejected.append(branch)
    assert matrix_sum([scale(matmul(adjoint(k), k), F(1, 2)) for k in rejected], 4) == scale(identity(4), F(1, 2))
    # Tracing these odd ports is a destructive completion, not unavoidable.
    assert choi(rejected, 4, [F(1, 2)]*2) != choi([identity(4)], 4, [F(1, 2)])
    # With coherent odd ports available, Bell-read them BEFORE B instead.
    # Source Bell and odd-Bell bra give amplitude1/2. Each known local
    # correction restores arbitrary ABR, allowing an ideal fresh-helper retry.
    odd_bras = [[ZERO, ONE, gaussian((-1)**n), ZERO] for n in range(2)]
    assert matrix_sum([scale(matmul(adjoint([row]), [row]), F(1, 2))
                       for row in odd_bras], 4) == odd
    safe_failure_units, safe_failure_effects = 0, []
    for n, row in enumerate(odd_bras):
        raw = zeros(4, 4)
        for a, b, d in product(range(2), repeat=3):
            if a != d:
                raw[2*d+b][2*a+b] = add(raw[2*d+b][2*a+b], row[2*a+d])
        assert raw == pauli(xa=1, za=n)
        correction = matmul(pauli(za=n), pauli(xa=1))
        safe_failure_units += cp_guard(matmul(correction, raw), identity(4), F(1, 4))
        safe_failure_effects.append(scale(matmul(adjoint(raw), raw), F(1, 4)))
    assert matrix_sum(f4_effects+safe_failure_effects, 4) == identity(4)
    # F8: construct the entire known unitary numerator, not only its E1=0
    # columns: parity copy; CNOT D->E0, H_D, CNOT D->E0.
    circuit = zeros(8, 8)
    for d, e0, e1, x in product(range(2), repeat=4):
        copied = e1 ^ d ^ e0
        final_e0 = e0 ^ d ^ x
        circuit[4*x+2*final_e0+copied][4*d+2*e0+e1] = gaussian((-1)**(d*x))
    assert matmul(adjoint(circuit), circuit) == scale(identity(8), 2)
    assert matmul(circuit, adjoint(circuit)) == scale(identity(8), 2)
    key_phase_circuit = [[times(value, (-1)**(row % 2)) for value in values]
                         for row, values in enumerate(circuit)]
    f8_units = source_units = key_units = 0
    f8_effects = []
    for p, m, n in product(range(2), repeat=3):
        raw = direct_branch(circuit, m, n, p)
        r = m ^ p
        expected = matmul(matmul(pauli(xa=p, xb=r), cz), pauli(za=r, zb=n))
        assert raw == expected
        correction = matmul(pauli(za=r, zb=n), pauli(xa=p, xb=r))
        fixed = matmul(correction, raw)
        f8_units += cp_guard(fixed, cz, F(1, 8))
        f8_effects.append(scale(matmul(adjoint(raw), raw), F(1, 8)))
        # E1 is untouched after BOTH parity-copy CNOTs. An unobserved Z_E1
        # only supplies the final scalar phase(-1)^p, harmless per flag.
        key_phased = matmul(correction, direct_branch(key_phase_circuit, m, n, p))
        assert key_phased == scale(fixed, (-1)**p)
        pieces = [matmul(correction, direct_branch(circuit, m, n, p, d)) for d in range(2)]
        minus_source = matrix_sum([pieces[0], scale(pieces[1], -1)], 4)
        assert minus_source == scale(matmul(pauli(za=1), cz), (-1)**p)
        for i, j, a, b in product(range(4), repeat=4):
            ideal = multiply(cz[i][a], conjugate(cz[j][b]))
            assert multiply(key_phased[i][a], conjugate(key_phased[j][b])) == ideal
            key_units += 1
            mixed = add(multiply(pieces[0][i][a], conjugate(pieces[0][j][b])),
                        multiply(pieces[1][i][a], conjugate(pieces[1][j][b])))
            assert mixed == (ideal if a//2 == b//2 else ZERO)
            source_units += 1
    assert matrix_sum(f8_effects, 4) == identity(4)
    # Before B, source/H normalization is1/2 in amplitude. Each p effect
    # is I/2, even on reference-entangled data; measuring p is not granted.
    for p in range(2):
        prefix = zeros(16, 4)
        for a, b, d, x, f in product(range(2), repeat=5):
            row = 8*d+4*b+2*x+f
            prefix[row][2*a+b] = add(prefix[row][2*a+b],
                                      circuit[4*x+2*f+p][4*a+2*d])
        assert scale(matmul(adjoint(prefix), prefix), F(1, 4)) == scale(identity(4), F(1, 2))
    # Coherent serialization A,B0,B1 uses two potential B windows. The
    # unoccupied window is identity, in the declared common idle frame.
    for bits in product(range(2), repeat=5):
        actual = list(bits)
        for window in range(2):
            if actual[4] == window:
                actual[1], actual[2] = actual[2], actual[1]
        desired = list(bits)
        desired[1], desired[2] = desired[2], desired[1]
        assert actual == desired
    # Optional F4 unitary program: known CZ_DE implements physical SWAP*CZ,
    # not fixed-output-port CZ. All four outcomes are retained.
    swap_cz = zeros(4, 4)
    for a, b in product(range(2), repeat=2):
        swap_cz[2*b+a][2*a+b] = gaussian((-1)**(a*b))
    swapped_units = 0
    for m, n in product(range(2), repeat=2):
        raw = direct_branch(cz, m, n)
        correction = matmul(pauli(za=n, zb=m), pauli(xa=m))
        swapped_units += cp_guard(matmul(correction, raw), swap_cz, F(1, 4))
    # F16: coefficient-complete tensor identity. Testing all sixteen E_ij
    # proves corrected numerator=U for EVERY complex U by linearity.
    tensor_entries = 0
    for row, column in product(range(4), repeat=2):
        unit = zeros(4, 4)
        unit[row][column] = ONE
        for ma, na, mb, nb in product(range(2), repeat=4):
            raw = arbitrary_branch(unit, ma, na, mb, nb)
            frame = pauli(xa=ma, xb=mb, za=na, zb=nb)
            correction = matmul(pauli(za=na, zb=nb), pauli(xa=ma, xb=mb))
            assert raw == matmul(frame, unit)
            assert matmul(correction, raw) == unit
            tensor_entries += 16
    controlled_phase = identity(4)
    controlled_phase[3][3] = gaussian(F(3, 5), F(4, 5))
    x = [[ZERO, ONE], [ONE, ZERO]]
    z = [[ONE, ZERO], [ZERO, gaussian(-1)]]
    xx = tensor(x, x)
    xx_rotation = matrix_sum([scale(identity(4), F(3, 5)),
                              [[multiply(gaussian(0, F(4, 5)), v) for v in row] for row in xx]], 4)
    controlled_rotation = identity(4)
    controlled_rotation[2][2] = controlled_rotation[3][3] = gaussian(F(5, 13))
    controlled_rotation[2][3], controlled_rotation[3][2] = gaussian(-F(12, 13)), gaussian(F(12, 13))
    targets = [cz, controlled_phase, xx_rotation, controlled_rotation]
    product_inputs = [[ONE]*4, [ONE]*4, [ONE, ZERO, ZERO, ZERO], [ONE, ZERO, ONE, ZERO]]
    generators = [tensor(x, identity(2)), tensor(identity(2), x),
                  tensor(z, identity(2)), tensor(identity(2), z)]
    signed_paulis = [scale(v, s) for v in pauli_basis(2) for s in (1, -1)]
    generic_units = 0
    for target_index, (u, source) in enumerate(zip(targets, product_inputs)):
        assert matmul(adjoint(u), u) == identity(4)
        assert multiply(source[0], source[3]) == multiply(source[1], source[2])
        output = [row[0] for row in matmul(u, [[v] for v in source])]
        assert multiply(output[0], output[3]) != multiply(output[1], output[2])
        if target_index:
            assert any(matmul(matmul(u, p), adjoint(u)) not in signed_paulis for p in generators)
        effects = []
        for ma, na, mb, nb in product(range(2), repeat=4):
            raw = arbitrary_branch(u, ma, na, mb, nb)
            correction = matmul(pauli(za=na, zb=nb), pauli(xa=ma, xb=mb))
            generic_units += cp_guard(matmul(correction, raw), u, F(1, 16))
            effects.append(scale(matmul(adjoint(raw), raw), F(1, 16)))
        assert matrix_sum(effects, 4) == identity(4)
    return {"status": "passed", "arithmetic": "Gaussian rational and explicit squared sqrt(2) normalization; stdlib",
            "F4_heralded_CZ_flags": 4, "F4_heralded_CZ_probability": "1/2",
            "F4_heralded_CZ_CP_coefficients": f4_units,
            "F4_traced_odd_reject_example": "effect I/2; destructive if odd ports are discarded",
            "F4_coherent_odd_Bell_failure_flags": 2,
            "F4_corrected_failure_CP_coefficients": safe_failure_units,
            "F4_complete_success_failure_flags": 6,
            "F4_corrected_failure_instrument": "two maps (1/4)id_ABR; halt before B",
            "F8_deterministic_CZ_flags": 8, "F8_deterministic_CZ_CP_coefficients": f8_units,
            "F8_pre_B_key_effect_entries": 32,
            "F8_key_phase_invariance_CP_coefficients": key_units,
            "F8_dephased_source_CP_coefficients": source_units,
            "F8_dephased_source_channel": "Ad_CZ after complete input-A dephasing",
            "complementary_B_window_basis_vectors": 32,
            "F4_SWAP_CZ_flags": 4, "F4_SWAP_CZ_CP_coefficients": swapped_units,
            "F16_arbitrary_U_flags": 16,
            "F16_staged_Bell_source_equivalence_inputs": 4,
            "F16_coefficient_complete_tensor_entries": tensor_entries,
            "F16_exact_entangling_unitary_fixtures": len(targets),
            "F16_nonClifford_fixtures": len(targets)-1,
            "F16_unitary_fixture_CP_coefficients": generic_units,
            "scope": "ideal literal helper-preserving SWAP contacts, known flying controls, charged "
                     "filter/reject ports and complete local-Pauli-corrected readouts; unknown ABR "
                     "and all flags; corrected odd-reject retry requires coherent ports/readout, "
                     "not noisy Raman simulation, mode optimality, generic harmless loss, "
                     "a free temporal serialization or measured native gate/rate advantage"}


def main():
    from rydberg_memory_schur import verify_rydberg_memory_schur
    from rydberg_exchange_eraser import verify_exchange_eraser
    losses = [loss_example(d, x, lx, y, ly) for d, x, lx, y, ly in (
        (2,F(3,5),F(4,5),F(5,13),F(12,13)),
        (3,F(3,5),F(4,5),F(5,13),F(12,13)),
        (2,F(0),F(1),F(3,5),F(4,5)), (2,F(1),F(0),F(3,5),F(4,5)),
        (2,F(1),F(0),F(1),F(0)), (2,F(0),F(1),F(0),F(1))) ]
    visibilities = (F(0), F(1,3), F(7,10), F(1))
    wires = [wire_example(d, mode, k) for d in (2,3) for mode in (False,True) for k in visibilities]
    activation = [tight_activation(k) for k in visibilities]
    print(json.dumps({"status":"passed", "arithmetic":"exact Gaussian fractions and Q(sqrt(2)); standard library only",
        "absorbing_vacuum_examples":losses, "sector_wire_factorizations":wires,
        "tight_qubit_activation_examples":activation,
        "rank_two_slot_factorizations":[rank_two_slot_example(k) for k in visibilities],
        "elastic_node_example":elastic_node_example(),
        "frequency_check_example":frequency_check_example(),
        "replacement_reset_cycle_examples":reset_cycle_examples(),
        "random_receiver_native_baselines":random_receiver_examples(),
        "late_record_guard_examples":late_record_guard_examples(),
        "chiral_parity_examples":chiral_parity_examples(),
        "raman_sprint_examples":raman_sprint_examples(),
        "raman_ordinary_gate_programs":raman_ordinary_gate_programs(),
        "raman_stronger_baselines":verify_raman_stronger_baselines(),
        "raman_multimode_helper":verify_raman_multimode_helper(),
        "raman_phase_covariance":verify_raman_phase_covariance(),
        "raman_reciprocal_ports":verify_reciprocal_raman_ports(),
        "raman_route_and_echo_phases":verify_raman_route_and_echo_phases(),
        "raman_port_routes":verify_raman_port_routes(),
        "raman_direct_temporal":verify_raman_direct_temporal(),
        "raman_timed_controls":verify_raman_timed_controls(),
        "raman_temporal_tail":verify_raman_temporal_tail(),
        "rydberg_memory_schur":verify_rydberg_memory_schur(),
        "rydberg_exchange_eraser":verify_exchange_eraser(),
        "scope":"Finite full-Choi identities, including arbitrary-control replacement-channel cycle simulations, random-receiver phase/normalized-bus isometries, and ideal helper-preserving SWAP gate programs with filter, source-coherence and query-window guards. General rank, LOCC, capacity, cooling inequalities, entropy-ledger, stopping and physical resource-graph proofs remain analytic in communication.md; no hardware advantage or priority claim."},indent=2))


if __name__ == "__main__":
    main()
