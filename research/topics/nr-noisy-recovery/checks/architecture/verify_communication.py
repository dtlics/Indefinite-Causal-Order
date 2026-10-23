"""Exact finite communication identities; analytic scope is communication.md.

Uses Gaussian rationals from the existing exact matrix engine. All reports go
to stdout. This does not replay the all-history entropy/capacity argument.
"""
from fractions import Fraction as F
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
        "scope":"Finite full-Choi identities and instrument/isometry checks. General rank, LOCC, capacity, entropy-ledger and stopping proofs remain analytic in communication.md; no hardware advantage or priority claim."},indent=2))


if __name__ == "__main__":
    main()
