"""Exact finite replay of NR-R06's native symmetry-check baselines.

Standard library only; Gaussian-rational arithmetic reuses the fault-simulation
matrix helpers. Examples include coherent, nonunital CPTP noise, rather than
only Pauli mixtures. General projection and physical-cost arguments are
analytic inputs, not certified by these finite examples. No files are written.
"""

from fractions import Fraction as F
from itertools import product
import json

from verify_fault_simulation import (
    ZERO, ONE, require, gaussian, add, multiply, conjugate, times,
    zeros, identity, adjoint, matmul, tensor, vectorize, inner,
    pauli_basis, rational_rotation,
)


def scaled(a, value):
    return [[times(x, value) for x in row] for row in a]


def plus(a, b):
    return [[add(x, y) for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]


def trace(a):
    out = ZERO
    for i in range(len(a)):
        out = add(out, a[i][i])
    return out


def absolute_squared(z):
    return z[0]**2+z[1]**2


def pq(kraus):
    """Weighted relative Kraus operators, with probabilities outside matrices."""
    d = len(kraus[0][1])
    p = q = F(0)
    for weight, k in kraus:
        p += weight*inner(vectorize(k), vectorize(k))[0]/d
        q += weight*absolute_squared(trace(k))/(d*d)
    return p, q


def require_tp(kraus):
    d = len(kraus[0][1])
    total = zeros(d, d)
    for weight, k in kraus:
        total = plus(total, scaled(matmul(adjoint(k), k), weight))
    require(total == identity(d), "Example noise is not trace preserving.")


def arbitrary_noise(n):
    """Nonunital amplitude damping after a coherent non-Clifford rotation."""
    damping = [
        [[ONE, ZERO], [ZERO, gaussian(F(3, 5))]],
        [[ZERO, gaussian(F(4, 5))], [ZERO, ZERO]],
    ]
    ks = [[[ONE]]]
    for _ in range(n):
        ks = [tensor(k, a) for k in ks for a in damping]
    ps = pauli_basis(n)
    rotation = matmul(rational_rotation(ps[1], 3, 4, 5),
                      rational_rotation(ps[-1], 5, 12, 13))
    out = [(F(1), matmul(k, rotation)) for k in ks]
    require_tp(out)
    coefficients = [[times(inner(vectorize(p), vectorize(k)), F(1, 2**n))
                     for p in ps] for _, k in out]
    has_offdiagonal = False
    for a, b in product(range(len(ps)), repeat=2):
        if a == b:
            continue
        chi = ZERO
        for row in coefficients:
            chi = add(chi, multiply(row[a], conjugate(row[b])))
        has_offdiagonal |= chi != ZERO
    require(has_offdiagonal, "Noise example accidentally became a Pauli channel.")
    return out


def filter_once(kraus, check, visibility):
    out = []
    a, b = (1+visibility)/2, (1-visibility)/2
    for weight, k in kraus:
        conjugated = matmul(matmul(check, k), check)
        out.append((weight*a, scaled(plus(k, conjugated), F(1, 2))))
        if b:
            out.append((weight*b, scaled(plus(k, scaled(conjugated, -1)), F(1, 2))))
    return out


def clifford(n):
    phase = [[ONE, ZERO], [ZERO, gaussian(0, 1)]]
    if n == 1:
        return phase
    cnot = zeros(4, 4)
    for a, b in product([0, 1], repeat=2):
        cnot[2*a+(b ^ a)][2*a+b] = ONE
    return matmul(cnot, tensor(phase, identity(2)))


def replay_pcs():
    count = 0
    for n in [1, 2]:
        errors = arbitrary_noise(n)
        f = pq(errors)[1]
        checks = pauli_basis(n)
        c = clifford(n)
        for q in checks:
            p = matmul(matmul(adjoint(c), q), c)
            require(p in checks or scaled(p, -1) in checks,
                    "Transported check is not a Hermitian Pauli.")
            for _, e in errors:
                # Direct controlled-pre/post circuit, reduced to relative error.
                second = matmul(matmul(matmul(q, e), c), p)
                actual = matmul(scaled(plus(matmul(e, c), second), F(1, 2)), adjoint(c))
                expected = scaled(plus(e, matmul(matmul(q, e), q)), F(1, 2))
                require(actual == expected, "Transported-check circuit identity failed.")
        for k in [1, 2]:
            for nu in [F(1), F(97, 100)]:
                total_p = total_q = F(0)
                for selected in product(checks, repeat=k):
                    ks = errors
                    for check in selected:
                        ks = filter_once(ks, check, nu)
                    p, q = pq(ks)
                    total_p += p
                    total_q += q
                denominator = len(checks)**k
                p, q = total_p/denominator, total_q/denominator
                expected_q = f*((1+nu)/2)**k
                require(q == expected_q, "PCS good-weight/visibility identity failed.")
                require(p == expected_q+(1-f)/2**k, "PCS acceptance identity failed.")
                count += 1
    require(F(81, 100)-F(19, 200) == F(143, 200), "One-check score arithmetic failed.")
    require(F(81, 100)-F(19, 400) == F(61, 80), "Two-check score arithmetic failed.")
    # Reset noise demonstrates that Bell acceptance is not payload-uniform.
    reset = [(F(1), [[ONE, ZERO], [ZERO, ZERO]]),
             (F(1), [[ZERO, ONE], [ZERO, ZERO]])]
    p = q = F(0)
    payload_acceptance = [F(0), F(0)]
    for check in pauli_basis(1):
        filtered = filter_once(reset, check, F(1))
        pp, qq = pq(filtered)
        p += pp/4
        q += qq/4
        for column in [0, 1]:
            payload_acceptance[column] += sum(weight*sum(absolute_squared(row[column])
                for row in kk) for weight, kk in filtered)/4
    require((p, q) == (F(5, 8), F(1, 4)), "Reset Bell example failed.")
    require(payload_acceptance == [F(3, 4), F(1, 2)], "Payload-dependence witness failed.")
    return count


def read_oracle(bits):
    out = zeros(2*len(bits), 2*len(bits))
    for address, bit in enumerate(bits):
        for target in [0, 1]:
            out[2*address+(target ^ bit)][2*address+target] = ONE
    return out


def read_check_group(address_qubits):
    z = pauli_basis(1)[3]
    x = pauli_basis(1)[1]
    out = []
    for labels in product([0, 1], repeat=address_qubits+1):
        h = [[ONE]]
        for flag in labels[:-1]:
            h = tensor(h, z if flag else identity(2))
        out.append(tensor(h, x if labels[-1] else identity(2)))
    return out


def pinch(k, group):
    out = zeros(len(k), len(k))
    for h in group:
        out = plus(out, matmul(matmul(h, k), h))
    return scaled(out, F(1, len(group)))


def replay_read_oracles():
    count = 0
    for address_qubits in [1, 2]:
        d = 2**(address_qubits+1)
        bits_a = [int(bin(i).count('1') == address_qubits) for i in range(2**address_qubits)]
        bits_b = [bin(i).count('1') % 2 for i in range(2**address_qubits)]
        a, b = read_oracle(bits_a), read_oracle(bits_b)
        group = read_check_group(address_qubits)
        require(matmul(a, b) == matmul(b, a), "Read oracles failed to commute.")
        errors = [(weight, tensor(identity(2**address_qubits), k))
                  for weight, k in arbitrary_noise(1)]
        require_tp(errors)
        for other in [a, b]:
            switched = [(w, scaled(plus(e, matmul(matmul(other, e), other)), F(1, 2)))
                        for w, e in errors]
            checked = [(w, pinch(e, group)) for w, e in errors]
            ps, qs = pq(switched)
            po, qo = pq(checked)
            require(qo == qs and po <= ps, "Single-module projection dominance failed.")
            count += 1
        ea, eb = F(1, 10), F(3, 10)
        aes = [(1-ea, identity(d))]+[(ea*w, e) for w, e in errors]
        bfs = [(1-eb, identity(d))]+[(eb*w, e) for w, e in errors]
        switched, checked = [], []
        for wa, e in aes:
            for wb, f in bfs:
                first = matmul(matmul(matmul(f, b), e), b)
                second = matmul(matmul(matmul(e, a), f), a)
                switched.append((wa*wb, scaled(plus(first, second), F(1, 2))))
                checked.append((wa*wb, pinch(first, group)))
        ps, qs = pq(switched)
        po, qo = pq(checked)
        require((2*qs-ps)-(2*qo-po) <= 2*ea*eb, "Double-fault residual bound failed.")
        count += 1
        # Check every claimed local-Pauli syndrome of the one-ancilla refinement.
        q_all = group[-1]
        local = pauli_basis(1)
        for location in range(address_qubits+1):
            for label in [1, 2, 3]:
                p = [[ONE]]
                for j in range(address_qubits+1):
                    p = tensor(p, local[label] if j == location else identity(2))
                central = (location < address_qubits and label == 3) or (
                    location == address_qubits and label == 1)
                expected = p if central else scaled(p, -1)
                require(matmul(matmul(q_all, p), q_all) == expected,
                        "One-ancilla local-fault syndrome failed.")
    # The double-fault residual is necessary, even with all checks ideal.
    a = identity(4)
    b = read_oracle([0, 1])
    z_target = tensor(identity(2), pauli_basis(1)[3])
    first = matmul(matmul(matmul(z_target, b), z_target), b)
    second = matmul(matmul(matmul(z_target, a), z_target), a)
    ps, qs = pq([(F(1), scaled(plus(first, second), F(1, 2)))])
    po, qo = pq([(F(1), pinch(first, read_check_group(1)))])
    require((ps, qs, po, qo) == (F(1, 2), F(1, 4), F(1), F(0)),
            "Double-fault counterexample failed.")
    return count


def main():
    pcs_cases = replay_pcs()
    read_cases = replay_read_oracles()
    print(json.dumps({
        "status": "passed", "arithmetic": "exact Gaussian rational, standard library",
        "pcs_nonpauli_cases": pcs_cases, "read_oracle_cases": read_cases,
        "scope": "Finite replay; general projection, costs and physical hypotheses are analytic.",
    }, sort_keys=True))


if __name__ == '__main__':
    main()
