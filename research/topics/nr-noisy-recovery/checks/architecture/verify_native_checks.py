"""Exact finite replay of NR-R06's native symmetry-check baselines.

Standard library only; Gaussian-rational arithmetic reuses the fault-simulation
matrix helpers. Examples include coherent, nonunital CPTP noise, rather than
only Pauli mixtures. General projection and physical-cost arguments are
analytic inputs, not certified by these finite examples. No files are written.
"""

from fractions import Fraction as F
from itertools import product
import json
import sys

if not __debug__:
    raise RuntimeError("Run exact native checks without -O.")
sys.dont_write_bytecode = True

from verify_fault_simulation import (
    ZERO, ONE, require, gaussian, add, multiply, conjugate, times,
    zeros, identity, adjoint, matmul, tensor, vectorize, inner,
    pauli_basis, rational_rotation, add_outer,
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


def replay_qutrit_router():
    """Full operator identities for an address-controlled two-exit router.

    Registers: qutrit address, input bus, left bus, right bus. The logical
    address is 0/2; level 1 is leakage and the chosen unitary completion
    leaves its buses alone. Equality is checked Kraus by Kraus, including
    both flags, so no restriction to unentangled test inputs is used.
    """
    def index(address, incoming, left, right):
        return 8*address+4*incoming+2*left+right

    router = zeros(24, 24)
    for address, incoming, left, right in product(range(3), range(2), range(2), range(2)):
        before = index(address, incoming, left, right)
        if address == 0:
            after = index(address, left, incoming, right)
        elif address == 2:
            after = index(address, right, left, incoming)
        else:
            after = before
        router[after][before] = ONE
    require(matmul(adjoint(router), router) == identity(24), "Router completion is not unitary.")

    code, code_injection = zeros(24, 24), zeros(24, 16)
    for logical, address in enumerate((0, 2)):
        for data in range(8):
            code[8*address+data][8*address+data] = ONE
            code_injection[8*address+data][8*logical+data] = ONE
    leak = plus(identity(24), scaled(code, -1))
    q_er = plus(scaled(code, 2), scaled(identity(24), -1))
    q_logic_a = identity(3)
    q_logic_a[2][2] = gaussian(-1)
    q_logic = tensor(q_logic_a, identity(8))
    for q in (q_er, q_logic):
        require(matmul(q, q) == identity(24), "Address check is not an involution.")
        require(matmul(q, router) == matmul(router, q), "Ideal router changes its address check.")

    damping0 = identity(3)
    damping0[2][2] = gaussian(F(3, 5))
    damping1 = zeros(3, 3)
    damping1[1][2] = gaussian(F(4, 5))
    flip = identity(3)
    flip[0][0] = flip[2][2] = ZERO
    flip[0][2] = flip[2][0] = ONE
    rotation = identity(3)
    rotation[0][0] = rotation[2][2] = gaussian(F(3, 5))
    rotation[0][2] = gaussian(F(-4, 5))
    rotation[2][0] = gaussian(F(4, 5))
    noises = [
        [(F(1), q_logic)],
        [(F(1), tensor(k, identity(8))) for k in (damping0, damping1)],
        [(F(1), tensor(flip, identity(8)))],
        [(F(1), tensor(rotation, identity(8)))],
    ]
    comparisons = 0
    for noise_number, noise in enumerate(noises):
        require_tp(noise)
        actual = [(weight, matmul(k, router)) for weight, k in noise]
        require_tp(actual)
        for _, k in actual:
            for q, sign in product((q_er, q_logic), (1, -1)):
                switched = scaled(plus(matmul(q, k), scaled(matmul(k, q), sign)), F(1, 2))
                checked = scaled(plus(k, scaled(matmul(matmul(q, k), q), sign)), F(1, 2))
                require(matmul(q, switched) == checked,
                        "Known-address switch/check full instrument equality failed.")
                comparisons += 1
            for sign, projector in ((1, code), (-1, leak)):
                checked = scaled(plus(k, scaled(matmul(matmul(q_er, k), q_er), sign)), F(1, 2))
                require(matmul(checked, code_injection) == matmul(matmul(projector, k), code_injection),
                        "One-postcheck nondestructive code/leakage flag identity failed.")
            if noise_number == 0:
                for q in (q_er, q_logic):
                    minus = scaled(plus(k, scaled(matmul(matmul(q, k), q), -1)), F(1, 2))
                    require(matmul(minus, code_injection) == zeros(24, 16),
                            "Address-diagonal phase noise spuriously triggers an order syndrome.")
    return comparisons


def native_choi(kraus):
    """Full normalized Choi, including a possibly rectangular output."""
    input_dimension = len(kraus[0][1][0])
    length = len(kraus[0][1])*input_dimension
    result = zeros(length, length)
    for weight, k in kraus:
        if weight:
            add_outer(result, vectorize(k), weight/input_dimension)
    return result


def require_tp_native_choi(j, input_dimension, output_dimension):
    marginal = zeros(input_dimension, input_dimension)
    for r, c, o in product(range(input_dimension), range(input_dimension), range(output_dimension)):
        marginal[r][c] = add(marginal[r][c],
            j[o+output_dimension*r][o+output_dimension*c])
    require(marginal == scaled(identity(input_dimension), F(1, input_dimension)),
            "Self-channel full-control Choi is not TP.")


def echo_arm_pair(u, z, bits, switched):
    # bits=(a1,a2,b1,b2) are pre-existing classical potential-slot faults.
    a1, a2, b1, b2 = bits
    first = lambda bit: matmul(z, u) if bit else u
    if switched:
        return matmul(first(b2), first(a1)), matmul(first(a2), first(b1))
    return matmul(first(a2), first(a1)), matmul(first(b2), first(b1))


def full_control_kraus(first, second):
    # Control-plus input isometry is [first;second]/sqrt(2); keep the
    # square-root factor outside as a probability weight in native_choi.
    return [list(row) for row in first]+[list(row) for row in second]


def self_channel_examples(n):
    basis = pauli_basis(n)
    d = 2**n
    yield identity(d)
    yield basis[1]  # anticommutes with the chosen full Z string
    rotation = matmul(rational_rotation(basis[1], 3, 4, 5),
                      rational_rotation(basis[-1], 5, 12, 13))
    if n == 2:
        rotation = matmul(rotation, rational_rotation(basis[4], 8, 15, 17))
    yield rotation


def replay_self_channel_routes():
    metric_cases, instrument_cases = 0, 0
    for n in [1, 2]:
        d = 2**n
        z = pauli_basis(n)[-1]
        require(z == adjoint(z) and matmul(z, z) == identity(d) and trace(z) == ZERO,
                "Fault generator is not a traceless Hermitian involution.")
        for u in self_channel_examples(n):
            require(matmul(adjoint(u), u) == identity(d), "Self-channel example is not unitary.")
            target = matmul(u, u)
            target_choi = native_choi([(F(1), target)])
            r_gaussian = times(trace(matmul(matmul(matmul(adjoint(u), z), u), z)), F(1, d))
            require(r_gaussian[1] == 0, "Target error overlap is not real.")
            r = r_gaussian[0]
            require(-1 <= r <= 1, "Target error overlap is outside its norm bound.")
            # Check every quasistatic fault event by its COMPLETE accepted
            # Bell Choi, including cases where the plus probability is zero.
            event = {}
            for a, b in product([0, 1], repeat=2):
                bits = (a, a, b, b)
                results = []
                for switched in [True, False]:
                    first, second = echo_arm_pair(u, z, bits, switched)
                    accepted = scaled(plus(first, second), F(1, 2))
                    j = native_choi([(F(1), accepted)])
                    p = trace(j)
                    q = inner(vectorize(target_choi), vectorize(j))
                    expected_p = F(1) if a == b else (1+r)/2
                    expected_q = (F(1) if a == b == 0 else r*r if a == b else
                                  F(0) if switched else (1+r)**2/4)
                    require((p, q) == (gaussian(expected_p), gaussian(expected_q)),
                            "Self-channel quasistatic event Choi metrics failed.")
                    relative = matmul(adjoint(target), accepted)
                    require(pq([(F(1), relative)]) == (expected_p, expected_q),
                            "Self-channel Choi and relative-Kraus Bell metrics disagree.")
                    results.append((expected_p, expected_q, j))
                event[a, b] = results
            for epsilon in [F(0), F(1, 10), F(1, 2), F(9, 10), F(1)]:
                js, jo = zeros(d*d, d*d), zeros(d*d, d*d)
                for a, b in product([0, 1], repeat=2):
                    weight = (epsilon if a else 1-epsilon)*(epsilon if b else 1-epsilon)
                    js = plus(js, scaled(event[a, b][0][2], weight))
                    jo = plus(jo, scaled(event[a, b][1][2], weight))
                p = 1-epsilon*(1-epsilon)*(1-r)
                qs = (1-epsilon)**2+epsilon**2*r*r
                qo = qs+epsilon*(1-epsilon)*(1+r)**2/2
                require(trace(js) == trace(jo) == gaussian(p), "Self-channel mixture yields differ.")
                require(inner(vectorize(target_choi), vectorize(js)) == gaussian(qs),
                        "Switched quasistatic Bell weight failed.")
                require(inner(vectorize(target_choi), vectorize(jo)) == gaussian(qo),
                        "Ordinary quasistatic Bell weight failed.")
                require(2*(qo-qs) == epsilon*(1-epsilon)*(1+r)**2 >= 0,
                        "Pointwise exact ordinary Bell-score dominance failed.")
                metric_cases += 1
            # The iid claim is stronger: the ENTIRE output control/data
            # channel is equal, with arbitrary passive references, not just
            # the above Bell overlap or one control measurement.
            for epsilon in [F(0), F(1, 10), F(1, 2), F(1)]:
                switched, ordinary = [], []
                for bits in product([0, 1], repeat=4):
                    a1, a2, b1, b2 = bits
                    permuted = (a1, b2, b1, a2)  # swap the LATE station bits
                    weight = epsilon**sum(bits)*(1-epsilon)**(4-sum(bits))
                    s0, s1 = echo_arm_pair(u, z, bits, True)
                    o0, o1 = echo_arm_pair(u, z, bits, False)
                    permuted0, permuted1 = echo_arm_pair(u, z, permuted, False)
                    require((s0, s1) == (permuted0, permuted1), "Iid bit bijection failed.")
                    # Even before averaging, S differs from O by the SAME
                    # left unitary on both control branches. Every payload's
                    # control readout probabilities therefore agree.
                    common = z if a2 != b2 else identity(d)
                    require(s0 == matmul(common, o0) and s1 == matmul(common, o1),
                            "Common hidden output-Pauli relation failed.")
                    switched.append((weight/2, full_control_kraus(s0, s1)))
                    ordinary.append((weight/2, full_control_kraus(o0, o1)))
                js, jo = native_choi(switched), native_choi(ordinary)
                require(js == jo, "Iid full control/data Choi equality failed.")
                require_tp_native_choi(js, d, 2*d)
                instrument_cases += 1
    # The amplitude-level vacuum premise cannot be inferred from Ad_U:
    # stations I and iI have identical occupied channels, but ordinary
    # same-station arms I and -I interfere differently from switch iI,iI.
    i = identity(2)
    ip = [[multiply(gaussian(0, 1), value) for value in row] for row in i]
    switch_plus = scaled(plus(matmul(ip, i), matmul(i, ip)), F(1, 2))
    ordinary_plus = scaled(plus(matmul(i, i), matmul(ip, ip)), F(1, 2))
    require(pq([(F(1), switch_plus)])[0] == 1 and pq([(F(1), ordinary_plus)])[0] == 0,
            "Vacuum-relative occupied-phase caveat failed.")
    return metric_cases, instrument_cases


def main():
    pcs_cases = replay_pcs()
    read_cases = replay_read_oracles()
    router_cases = replay_qutrit_router()
    self_metric_cases, self_instrument_cases = replay_self_channel_routes()
    print(json.dumps({
        "status": "passed", "arithmetic": "exact Gaussian rational, standard library",
        "pcs_nonpauli_cases": pcs_cases, "read_oracle_cases": read_cases,
        "qutrit_router_flagged_kraus_identities": router_cases,
        "self_channel_quasistatic_full_choi_metric_cases": self_metric_cases,
        "self_channel_iid_full_control_choi_cases": self_instrument_cases,
        "scope": "Finite replay; general projection, costs and physical hypotheses are analytic.",
    }, sort_keys=True))


if __name__ == '__main__':
    main()
