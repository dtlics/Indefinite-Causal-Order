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


def main():
    losses = [loss_example(d, x, lx, y, ly) for d, x, lx, y, ly in (
        (2,F(3,5),F(4,5),F(5,13),F(12,13)),
        (3,F(3,5),F(4,5),F(5,13),F(12,13)),
        (2,F(0),F(1),F(3,5),F(4,5)), (2,F(1),F(0),F(3,5),F(4,5)),
        (2,F(1),F(0),F(1),F(0)), (2,F(0),F(1),F(0),F(1))) ]
    visibilities = (F(0), F(1,3), F(7,10), F(1))
    wires = [wire_example(d, mode, k) for d in (2,3) for mode in (False,True) for k in visibilities]
    activation = [tight_activation(k) for k in visibilities]
    print(json.dumps({"status":"passed", "arithmetic":"exact Gaussian fractions; standard library only",
        "absorbing_vacuum_examples":losses, "sector_wire_factorizations":wires,
        "tight_qubit_activation_examples":activation,
        "rank_two_slot_factorizations":[rank_two_slot_example(k) for k in visibilities],
        "elastic_node_example":elastic_node_example(),
        "frequency_check_example":frequency_check_example(),
        "replacement_reset_cycle_examples":reset_cycle_examples(),
        "random_receiver_native_baselines":random_receiver_examples(),
        "late_record_guard_examples":late_record_guard_examples(),
        "chiral_parity_examples":chiral_parity_examples(),
        "scope":"Finite full-Choi identities, including arbitrary-control replacement-channel cycle simulations, and random-receiver phase/normalized-bus isometry checks. General rank, LOCC, capacity, cooling inequalities, entropy-ledger, stopping and physical resource-graph proofs remain analytic in communication.md; no hardware advantage or priority claim."},indent=2))


if __name__ == "__main__":
    main()
