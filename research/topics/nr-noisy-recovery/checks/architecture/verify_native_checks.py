"""Exact finite replay of NR-R06's native symmetry-check baselines.

Standard library only; Gaussian-rational arithmetic reuses the fault-simulation
matrix helpers. Examples include coherent, nonunital CPTP noise, rather than
only Pauli mixtures. General projection and physical-cost arguments are
analytic inputs, not certified by these finite examples. Terminal common-replacement checks include arbitrary global CPTP preprocessing, direct reduced cross maps and sharp SWAP examples; their universal norm bounds remain analytic. Calibrated Pauli/Weyl recovery checks include correlated histories, sparse qutrit phase assignments and common final control noise. General recovery/POVM and all-dimensional dominance proofs remain analytic. No files are written.
"""

from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import gcd
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


def diagonal_part(k):
    out = zeros(len(k), len(k))
    for x in range(len(k)):
        out[x][x] = k[x][x]
    return out


def physical_bell_metrics(kraus, target):
    """Compute p/q directly from normalized physical Choi matrices."""
    j = native_choi(kraus)
    ideal = native_choi([(F(1), target)])
    p = trace(j)
    q = inner(vectorize(ideal), vectorize(j))
    require(p[1] == q[1] == 0, "Bell probabilities became complex.")
    relative = [(w, matmul(adjoint(target), k)) for w, k in kraus]
    require((p[0], q[0]) == pq(relative), "Physical and relative Bell metrics differ.")
    return p[0], q[0]


def copied_label_zero_kraus(k, labels, modulus):
    """Explicit coherent copy, physical Kraus, uncopy, then zero readout.

    Labels can be complete basis indices or photon-number values.  No input
    label is measured.  The reference-complete effective Kraus is extracted
    from the full data-plus-syndrome operator, not assumed to be diagonal.
    """
    d = len(k)
    copy = zeros(d*modulus, d*modulus)
    for x, label in enumerate(labels):
        for r in range(modulus):
            copy[x*modulus+(r+label) % modulus][x*modulus+r] = ONE
    full = matmul(adjoint(copy), matmul(tensor(k, identity(modulus)), copy))
    return [[full[x*modulus][y*modulus] for y in range(d)] for x in range(d)]


def diagonal_ideals(d):
    pairs = [
        (ONE, ONE),
        (gaussian(F(3, 5), F(4, 5)), gaussian(0, 1)),
        (gaussian(F(5, 13), F(12, 13)), gaussian(F(7, 25), F(24, 25))),
        (gaussian(F(8, 17), F(15, 17)), gaussian(F(20, 29), F(21, 29))),
    ]
    a, b = zeros(d, d), zeros(d, d)
    for x in range(d):
        a[x][x], b[x][x] = pairs[x]
    require_tp([(F(1), a)])
    require_tp([(F(1), b)])
    require(matmul(a, b) == matmul(b, a), "Ideal diagonal layers fail to commute.")
    return a, b


def replay_known_basis_layers():
    count = cross_term_cases = 0
    for n in (1, 2):
        d = 2**n
        a, b = diagonal_ideals(d)
        target = matmul(b, a)
        errors = arbitrary_noise(n)
        for faulty_first in (True, False):
            switched, checked, offdiagonal, minus = [], [], [], []
            for weight, e in errors:
                if faulty_first:
                    first = matmul(b, matmul(e, a))
                    second = matmul(matmul(e, a), b)
                else:
                    first = matmul(matmul(e, b), a)
                    second = matmul(a, matmul(e, b))
                k = scaled(plus(first, second), F(1, 2))
                diagonal = copied_label_zero_kraus(first, range(d), d)
                require(diagonal == diagonal_part(first) == diagonal_part(k),
                        "Known-basis physical check does not match switch diagonal.")
                switched.append((weight, k))
                checked.append((weight, diagonal))
                offdiagonal.append((weight, plus(k, scaled(diagonal, -1))))
                minus.append((weight, scaled(plus(first, scaled(second, -1)), F(1, 2))))
            require_tp(switched+minus)
            ps, qs = physical_bell_metrics(switched, target)
            po, qo = physical_bell_metrics(checked, target)
            extra_p = trace(native_choi(offdiagonal))
            require(qo == qs and gaussian(ps-po) == extra_p and po <= ps,
                    "Known-basis one-fault p/q comparison failed.")
            cross = plus(native_choi(checked), native_choi(offdiagonal))
            if native_choi(switched) != cross:
                cross_term_cases += 1
            count += 1
        # Include both non-Pauli/nonunital fault channels, not only the
        # single-fault sectors, in the conservative independent-event bound.
        for ea, eb in ((F(1, 10), F(3, 10)), (F(1, 2), F(1, 2))):
            aes = [(1-ea, identity(d))]+[(ea*w, e) for w, e in errors]
            bfs = [(1-eb, identity(d))]+[(eb*w, e) for w, e in errors]
            switched, checked = [], []
            for wa, e in aes:
                for wb, f in bfs:
                    first = matmul(matmul(f, b), matmul(e, a))
                    second = matmul(matmul(e, a), matmul(f, b))
                    switched.append((wa*wb, scaled(plus(first, second), F(1, 2))))
                    checked.append((wa*wb, diagonal_part(first)))
            ps, qs = physical_bell_metrics(switched, target)
            po, qo = physical_bell_metrics(checked, target)
            require(2*qo-po >= 2*qs-ps-2*ea*eb, "Known-basis double-fault bound failed.")
            count += 1
    require(cross_term_cases > 0, "Examples missed coherent Choi cross terms.")
    # Two faults can reverse the ordinary comparison.  No all-orders
    # dominance is inferred from the one-fault identities.
    a, b = diagonal_ideals(2)
    x = pauli_basis(1)[1]
    first = matmul(matmul(x, b), matmul(x, a))
    second = matmul(matmul(x, a), matmul(x, b))
    ps, qs = physical_bell_metrics([(F(1), scaled(plus(first, second), F(1, 2)))],
                                  matmul(b, a))
    po, qo = physical_bell_metrics([(F(1), diagonal_part(first))], matmul(b, a))
    require(2*qs-ps > 2*qo-po, "Missing double-fault limitation witness.")
    return count, cross_term_cases


def number_loss_example(d, offset):
    triples = [(3, 4, 5), (5, 12, 13), (7, 24, 25), (9, 40, 41)]
    target, nojump, jump = zeros(d, d), zeros(d, d), zeros(d, d)
    target[0][0] = nojump[0][0] = ONE
    for n in range(1, d):
        a, b, c = triples[offset+n-1]
        phase = gaussian(F(a, c), F(b, c))
        target[n][n] = phase
        nojump[n][n] = times(phase, F(a, c))
        jump[n-1][n] = times(phase, F(b, c))
    phase_error = identity(d)
    for n in range(1, d, 2):
        phase_error[n][n] = gaussian(0, 1)
    ks = []
    for k, shift in ((nojump, 0), (jump, 1)):
        ks.append((F(9, 25), k, shift))
        ks.append((F(16, 25), matmul(phase_error, k), shift))
    require_tp([(w, k) for w, k, _ in ks])
    return target, ks


def replay_number_diagonal_loss():
    count = 0
    for d in (2, 3, 4):
        a, aks = number_loss_example(d, 0)
        b, bks = number_loss_example(d, 1)
        target = matmul(b, a)
        switched, checked, no_loss, loss, minus = [], [], [], [], []
        for wa, ka, la in aks:
            for wb, kb, lb in bks:
                first, second = matmul(kb, ka), matmul(ka, kb)
                k = scaled(plus(first, second), F(1, 2))
                accepted = copied_label_zero_kraus(first, range(d), d)
                switched.append((wa*wb, k))
                checked.append((wa*wb, accepted))
                minus.append((wa*wb, scaled(plus(first, scaled(second, -1)), F(1, 2))))
                if la+lb == 0:
                    require(first == second == accepted,
                            "No-loss modular-number circuit changed a diagonal Kraus.")
                    no_loss.append((wa*wb, k))
                else:
                    require(accepted == zeros(d, d), "Positive loss passed modular number.")
                    require(trace(matmul(adjoint(target), k)) == ZERO,
                            "Lowering Kraus has nonzero target Bell overlap.")
                    loss.append((wa*wb, k))
                count += 1
        require_tp(switched+minus)
        require(native_choi(checked) == native_choi(no_loss),
                "Complete ordinary no-loss Choi identity failed.")
        require(native_choi(switched) == plus(native_choi(no_loss), native_choi(loss)),
                "Complete switched CP loss remainder failed.")
        ps, qs = physical_bell_metrics(switched, target)
        po, qo = physical_bell_metrics(checked, target)
        require(qo == qs and po <= ps and 2*qo-po >= 2*qs-ps,
                "Number-diagonal loss signed Bell comparison failed.")
        require(qo*ps >= qs*po, "Conditional Bell fidelity comparison failed.")
    # A genuine two-photon jump defeats parity, even though full number
    # difference still detects it.  First-order parity protection therefore
    # requires a single-photon weak-loss law, not merely nonnegative shifts.
    two_loss = zeros(3, 3)
    two_loss[0][2] = gaussian(F(4, 5))
    no_two_loss = identity(3)
    no_two_loss[2][2] = gaussian(F(3, 5))
    require_tp([(F(1), no_two_loss), (F(1), two_loss)])
    require(copied_label_zero_kraus(two_loss, (0, 1, 0), 2) == two_loss,
            "Two-photon loss unexpectedly triggered parity.")
    require(copied_label_zero_kraus(two_loss, range(3), 3) == zeros(3, 3),
            "Full modular number missed a two-photon jump.")
    return count


def repl_zeros(rows, cols=None):
    return zeros(rows, rows if cols is None else cols)


def repl_total(values):
    out = ZERO
    for value in values:
        out = add(out, value)
    return out

def repl_gaussian_scale(a, value):
    return [[multiply(value, v) for v in row] for row in a]

def repl_matmul(a, b):
    out = repl_zeros(len(a), len(b[0]))
    for i, row in enumerate(a):
        for k, first in enumerate(row):
            if first == ZERO:
                continue
            for j, second in enumerate(b[k]):
                if second != ZERO:
                    out[i][j] = add(out[i][j], multiply(first, second))
    return out

def repl_units(n):
    for i, j in product(range(n), repeat=2):
        out = repl_zeros(n)
        out[i][j] = ONE
        yield out

def repl_kraus_norm(kraus):
    out = repl_zeros(len(kraus[0][0]))
    for k in kraus:
        out = plus(out, repl_matmul(adjoint(k), k))
    return out

def repl_givens(n, first, second, cosine=F(3, 5), sine=F(4, 5)):
    out = identity(n)
    out[first][first] = out[second][second] = gaussian(cosine)
    out[first][second], out[second][first] = (gaussian(0, -sine), gaussian(0, -sine))
    require(repl_matmul(adjoint(out), out) == identity(n), 'Terminal replacement cross-map identity failed.')
    return out

def repl_damp_after(unitary, source, target):
    n = len(unitary)
    k0, k1 = (identity(n), repl_zeros(n))
    k0[source][source], k1[target][source] = (gaussian(F(3, 5)), gaussian(F(4, 5)))
    out = [repl_matmul(k0, unitary), repl_matmul(k1, unitary)]
    require(repl_kraus_norm(out) == identity(n), 'Terminal replacement cross-map identity failed.')
    return out

def repl_reduced_kraus(pre, d, r):
    out = []
    for k in pre:
        for z in range(d):
            a = [list(row) for row in k[z * r:(z + 1) * r]]
            if any((v != ZERO for row in a for v in row)):
                out.append(a)
    require(repl_kraus_norm(out) == identity(d * r), 'Terminal replacement cross-map identity failed.')
    return out

def repl_input_block(a, x, r):
    return [row[x * r:(x + 1) * r] for row in a]

def repl_output_embed(a, x, d, r):
    out = repl_zeros(d * r)
    for i in range(r):
        out[x * r + i] = list(a[i])
    return out

def repl_trace_j(a, d, r):
    return [[repl_total((a[x * r + i][x * r + j] for x in range(d))) for j in range(r)] for i in range(r)]

def repl_cross_map(pairs, rho, r, weight=F(1)):
    out = repl_zeros(r)
    for left, right in pairs:
        out = plus(out, repl_gaussian_scale(repl_matmul(repl_matmul(left, rho), adjoint(right)), gaussian(weight)))
    return out

def repl_replay(pre_a, pre_b, d, r, full_units=False):
    n = d * r
    a, b = (repl_reduced_kraus(pre_a, d, r), repl_reduced_kraus(pre_b, d, r))
    pairs = [(repl_matmul(repl_input_block(bj, x, r), ai), repl_matmul(repl_input_block(ai, x, r), bj)) for x, ai, bj in product(range(d), a, b)]
    require(repl_kraus_norm([left for left, right in pairs]) == repl_gaussian_scale(identity(n), gaussian(d)), 'Terminal replacement cross-map identity failed.')
    require(repl_kraus_norm([right for left, right in pairs]) == repl_gaussian_scale(identity(n), gaussian(d)), 'Terminal replacement cross-map identity failed.')
    effect = repl_zeros(n)
    for left, right in pairs:
        effect = plus(effect, repl_gaussian_scale(repl_matmul(adjoint(right), left), gaussian(F(1, d * d))))
    checked = 0
    if full_units:
        raw_a = [repl_output_embed(ai, x, d, r) for x, ai in product(range(d), a)]
        raw_b = [repl_output_embed(bj, y, d, r) for y, bj in product(range(d), b)]
        physical = [(repl_matmul(bb, aa), repl_matmul(aa, bb)) for aa, bb in product(raw_a, raw_b)]
        for rho in repl_units(n):
            actual_full = repl_cross_map(physical, rho, n, F(1, d * d))
            actual = repl_trace_j(actual_full, d, r)
            expected = repl_cross_map(pairs, rho, r, F(1, d * d))
            require(actual == expected, 'Terminal replacement cross-map identity failed.')
            require(trace(actual) == trace(repl_matmul(effect, rho)), 'Terminal replacement cross-map identity failed.')
            checked += 1
    return (effect, pairs, checked)

def replay_terminal_replacement():
    """Exact common-replacement rectangular factors, direct reduced cross maps, SWAP sharpness and nonuniform qudit weights. Universal norm/convexity arguments remain analytic."""
    cases, matrix_units = (0, 0)
    for d, r in [(2, 1), (2, 2), (2, 3), (3, 2)]:
        n = d * r
        ua = repl_givens(n, 0, n - 1)
        ub = repl_matmul(repl_givens(n, 0, 1, F(5, 13), F(12, 13)), repl_givens(n, 1, n - 1)) if n > 2 else repl_givens(n, 0, 1, F(5, 13), F(12, 13))
        for pre_a, pre_b in [([ua], [ub]), (repl_damp_after(ua, n - 1, 0), repl_damp_after(ub, n - 2, 1 if n > 2 else 0))]:
            _, _, count = repl_replay(pre_a, pre_b, d, r, full_units=d == 2 and r <= 2)
            matrix_units += count
            cases += 1
    for d in [2, 3]:
        r, n = (d, d * d)
        swap = repl_zeros(n)
        for j, k in product(range(d), repeat=2):
            swap[k * d + j][j * d + k] = ONE
        effect, pairs, count = repl_replay([swap], [swap], d, r, full_units=d == 2)
        matrix_units += count
        require(effect == repl_gaussian_scale(swap, gaussian(F(1, d))), 'Terminal replacement cross-map identity failed.')
        for rho in repl_units(n):
            actual = repl_cross_map(pairs, rho, r, F(1, d * d))
            expected = repl_gaussian_scale(identity(r), multiply(gaussian(F(1, d * d)), trace(repl_matmul(swap, rho))))
            require(actual == expected, 'Terminal replacement cross-map identity failed.')
        witness = repl_zeros(n)
        witness[0][0] = ONE
        require(trace(repl_cross_map(pairs, witness, r, F(1, d * d))) == gaussian(F(1, d)), 'Terminal replacement cross-map identity failed.')
        cases += 1
    dimensions = [2, 3, 2]
    eta_a, eta_b = ([F(1, 5), F(2, 7), F(1, 3)], [F(3, 8), F(1, 6), F(4, 9)])
    for retained in [set(), {1}, {0, 1, 2}]:
        expected = F(1)
        for j, d in enumerate(dimensions):
            if j not in retained:
                expected *= 1 - (1 - F(1, d)) * eta_a[j] * eta_b[j]
        expanded = F(0)
        for sa, sb in product(range(8), repeat=2):
            weight, reciprocal_dim = (F(1), F(1))
            for j, d in enumerate(dimensions):
                in_a, in_b = (bool(sa & 1 << j), bool(sb & 1 << j))
                weight *= eta_a[j] if in_a else 1 - eta_a[j]
                weight *= eta_b[j] if in_b else 1 - eta_b[j]
                if in_a and in_b and (j not in retained):
                    reciprocal_dim /= d
            expanded += weight * reciprocal_dim
        require(expanded == expected, 'Terminal replacement cross-map identity failed.')
    return {'status': 'passed', 'arithmetic': 'exact Gaussian rational fractions', 'replacement_channel_examples': cases, 'direct_physical_reduced_cross_map_matrix_units': matrix_units, 'rectangular_cross_factor_both_column_sums': 'd I', 'swap_effects': {'d2': 'SWAP/2', 'd3': 'SWAP/3'}, 'swap_reduced_map': 'I_R Tr(SWAP X)/d^2', 'nonuniform_qudit_replacement_expansions': 3, 'scope': 'Finite CPTP preprocessing, direct cross-map, sharpness and convex-weight identities; universal cb/diamond and postselection proofs remain analytic.'}


def replay_transported_pauli_calibration():
    """Input-independent ordinary cross trace and mixed-probe switch blindness."""
    ps = pauli_basis(2)
    g = zeros(4, 4)
    for a, b in product(range(2), repeat=2):
        g[2*a+(a ^ b)][2*a+b] = ONE
    require(matmul(g, g) == identity(4), "Calibration CNOT is not involutory.")
    raw = [1000, 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
    weights = [F(value, sum(raw)) for value in raw]
    relations = cross_units = effect_entries = blind = 0
    for p in ps:
        q = matmul(adjoint(g), matmul(p, g))
        blocks, signs = [], []
        for error in ps:
            left = matmul(error, g)
            right = matmul(p, matmul(left, q))
            chi = dw_sign_comm(p, error)
            require(right == scaled(left, chi), "Transported Pauli check failed.")
            blocks.append((left, right))
            signs.append(chi)
            relations += 1
        eigenvalue = sum(w*s for w, s in zip(weights, signs))
        effect = zeros(4, 4)
        for weight, error in zip(weights, ps):
            eg = matmul(error, g)
            term = matmul(adjoint(matmul(eg, p)), matmul(p, eg))
            effect = plus(effect, scaled(term, weight))
        require(effect == scaled(matmul(p, q), eigenvalue),
                "Known-Pauli switch has the wrong cross effect.")
        effect_entries += 16
        if q != p and q != scaled(p, -1):
            require(trace(effect) == ZERO, "Mixed-probe switch is not blind.")
            blind += 1
        for row, column in product(range(4), repeat=2):
            unit = zeros(4, 4)
            unit[row][column] = ONE
            actual = ZERO
            for weight, (left, right) in zip(weights, blocks):
                actual = add(actual, times(trace(matmul(left, matmul(unit,
                                                                      adjoint(right)))),
                                           weight))
            require(actual == times(trace(unit), eigenvalue),
                    "Ordinary cross trace depends on the input data.")
            cross_units += 1
    lam1, helper1, lam2, helper2 = F(3, 5), F(5, 6), F(2, 3), F(3, 4)
    require(lam1 != lam2 and lam1*helper1 == lam2*helper2 == F(1, 2),
            "Helper-target identifiability counterexample changed.")
    for length in range(9):
        require((lam1*helper1)**length == (lam2*helper2)**length,
                "Length fitting resolved identical product decays.")
    p_error = F(1, 5)
    persistent = (1-p_error)+p_error*(-1)**2
    independent = (1-2*p_error)**2
    require((persistent, independent) == (F(1), F(9, 25)),
            "Temporal-correlation counterexample changed.")
    return {
        "status": "passed", "arithmetic": "exact Gaussian rational",
        "CNOT_Pauli_branch_relations": relations,
        "reduced_cross_block_matrix_units": cross_units,
        "known_Pauli_switch_effect_entries": effect_entries,
        "maximally_mixed_blind_transported_Paulis": blind,
        "equal_helper_target_product_decay_lengths": 9,
        "persistent_two_step_control_coherence": str(persistent),
        "independent_two_step_control_coherence": str(independent),
        "scope": "Finite transported-check, cross-effect and process counterexamples; no general calibration or native advantage claim.",
    }


def dw_sign_comm(q, e):
    character = trace(matmul(matmul(q, e), matmul(q, e)))[0]/len(q)
    require(character in [-1, 1], "Pauli commutator is not a sign.")
    return character


def dw_add_matrix_unit(out, left, right, row, column, weight):
    left_column = [(i, r[row]) for i, r in enumerate(left) if r[row] != ZERO]
    right_column = [(j, r[column]) for j, r in enumerate(right)
                    if r[column] != ZERO]
    for i, x in left_column:
        for j, y in right_column:
            out[i][j] = add(out[i][j], times(multiply(x, conjugate(y)), weight))


def replay_deterministic_pauli_weyl():
    """Finite DW1--DW4 guards; recovery/POVM and dimension bounds are analytic."""
    ps, d = pauli_basis(2), 4
    local_indices = [1, 2, 3, 4, 8, 12]
    separator_pairs = 0
    for i, j in product(range(16), repeat=2):
        if i == j:
            continue
        require(any(dw_sign_comm(ps[k], ps[i]) != dw_sign_comm(ps[k], ps[j])
                    for k in local_indices), "No local Pauli separator found.")
        separator_pairs += 1

    # Full support, with two correlated boosts: this is not a product law.
    raw = [[F(1+50*(a == b == 0)+30*(a == 1 and b == 3))
            for b in range(16)] for a in range(16)]
    total = sum(sum(row) for row in raw)
    law = [[x/total for x in row] for row in raw]
    require(law[0][0]*law[1][1] != law[0][1]*law[1][0],
            "Correlated Pauli example became a product law.")
    mass_plus, mass_minus = [F(0)]*16, [F(0)]*16
    histories = []
    for a, b in product(range(16), repeat=2):
        k0, k1 = matmul(ps[b], ps[a]), matmul(ps[a], ps[b])
        chi = dw_sign_comm(ps[a], ps[b])
        require(k1 == scaled(k0, chi), "Pauli order histories disagree.")
        matches = []
        for e, pe in enumerate(ps):
            phase = times(trace(matmul(adjoint(pe), k0)), F(1, d))
            if phase != ZERO:
                require(phase in [ONE, gaussian(-1), gaussian(0, 1),
                                  gaussian(0, -1)], "Invalid Pauli phase.")
                require(k0 == [[multiply(phase, x) for x in row] for row in pe],
                        "Wrong net Pauli label.")
                matches.append(e)
        require(len(matches) == 1, "Net Pauli label is not unique.")
        e = matches[0]
        (mass_plus if chi == 1 else mass_minus)[e] += law[a][b]
        histories.append((law[a][b], k0+k1))

    input_units = 0
    for row, column in product(range(d), repeat=2):
        direct, cq = zeros(2*d, 2*d), zeros(2*d, 2*d)
        for probability, stack in histories:
            dw_add_matrix_unit(direct, stack, stack, row, column, probability/2)
        for e, pe in enumerate(ps):
            for sign, weight in [(1, mass_plus[e]), (-1, mass_minus[e])]:
                stack = pe+scaled(pe, sign)
                dw_add_matrix_unit(cq, stack, stack, row, column, weight/2)
        require(direct == cq, "Complete switched Pauli CQ channel differs.")
        input_units += 1

    priors = [a+b for a, b in zip(mass_plus, mass_minus)]
    dominant = sorted(range(16), key=lambda e: priors[e], reverse=True)[:2]
    separator = next(k for k in local_indices
                     if dw_sign_comm(ps[k], ps[dominant[0]]) !=
                     dw_sign_comm(ps[k], ps[dominant[1]]))
    ordinary_fidelity = sum(priors[e] for e in dominant)
    # These control states are X diagonal, so guessing is exactly classical.
    switch_fidelity = max(mass_plus)+max(mass_minus)
    require((switch_fidelity, ordinary_fidelity) == (F(13, 42), F(1, 3)),
            "Correlated Pauli fidelity witness changed.")

    weyl_images = 0
    for dim in range(2, 21):
        for x, z in product(range(dim), repeat=2):
            if x == z == 0:
                continue
            g = gcd(dim, gcd(x, z))
            order = dim//g
            image = {(u*z-v*x) % dim for u, v in product(range(dim), repeat=2)}
            require(image == {g*k for k in range(order)},
                    "Weyl-character image differs from its gcd subgroup.")
            target = g*(order//2)
            require(target in image, "Nearest antipodal character unavailable.")
            require(2*target == dim-(g if order % 2 else 0),
                    "Wrong nearest antipodal character.")
            weyl_images += 1
    return {
        "status": "passed", "arithmetic": "exact Gaussian rational and integer",
        "two_qubit_ordered_error_pairs_with_local_separator": separator_pairs,
        "nonproduct_joint_histories": len(histories),
        "complete_fixed_plus_switch_input_matrix_units": input_units,
        "dominant_error_labels": dominant, "single_qubit_check_label": separator,
        "switch_optimal_deterministic_fidelity": str(switch_fidelity),
        "ordinary_deterministic_fidelity": str(ordinary_fidelity),
        "finite_Weyl_nonzero_difference_images": weyl_images,
        "Weyl_dimensions": "2..20, all nonzero differences",
        "scope": "Finite CQ transcription, local separators and character images; recovery-to-POVM and all-dimension bounds remain analytic.",
    }


# Eisenstein rationals a+b*omega, omega^2+omega+1=0. These are not the
# Gaussian-rational pairs used by the existing fault-simulation helpers.
TRI_ZERO, TRI_ONE, TRI_OMEGA = (F(0), F(0)), (F(1), F(0)), (F(0), F(1))


def tri_add(x, y):
    return (x[0]+y[0], x[1]+y[1])


def tri_multiply(x, y):
    a, b = x
    c, d = y
    return (a*c-b*d, a*d+b*c-b*d)


def tri_conjugate(x):
    return (x[0]-x[1], -x[1])


def tri_power(k):
    out = TRI_ONE
    for _ in range(k % 3):
        out = tri_multiply(out, TRI_OMEGA)
    return out


def tri_matrix(rows):
    return [[(F(x), F(0)) for x in row] for row in rows]


def tri_plus(a, b):
    return [[tri_add(x, y) for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]


def tri_scale(a, value):
    return [[(x[0]*value, x[1]*value) for x in row] for row in a]


def tri_cscale(a, value):
    return [[tri_multiply(x, value) for x in row] for row in a]


def tri_matmul(a, b):
    return [[tri_add(tri_multiply(a[i][0], b[0][j]),
                     tri_multiply(a[i][1], b[1][j]))
             for j in range(2)] for i in range(2)]


def tri_adjoint(a):
    return [[tri_conjugate(a[j][i]) for j in range(2)] for i in range(2)]


def tri_trace(a):
    return tri_add(a[0][0], a[1][1])


def tri_real(x):
    require(x[1] == 0, "Expected an exactly real Eisenstein rational.")
    return x[0]


def tri_score(a, b):
    return tri_real(tri_trace(tri_matmul(a, b)))


def tri_phase(k):
    return [[TRI_ONE, TRI_ZERO], [TRI_ZERO, tri_power(k)]]


def tri_orbit(rho, k):
    phase = tri_phase(k)
    return tri_matmul(tri_matmul(phase, rho), tri_adjoint(phase))


def tri_dot(a, b):
    return sum(x*y for x, y in zip(a, b)) % 3


def tri_sparse_functional(v, w, a, b):
    """Solve q.v=a,q.w=b with at most two coordinates over F3."""
    for i, j in combinations(range(len(v)), 2):
        determinant = (v[i]*w[j]-v[j]*w[i]) % 3
        if determinant:
            inverse = determinant  # Both nonzero elements of F3 are self inverse.
            q = [0]*len(v)
            q[i] = inverse*(a*w[j]-v[j]*b) % 3
            q[j] = inverse*(v[i]*b-a*w[i]) % 3
            require((tri_dot(q, v), tri_dot(q, w)) == (a, b),
                    "Sparse affine interpolation failed.")
            return tuple(q)
    require(any(v) and tuple(w) == tuple((-x) % 3 for x in v)
            and b == -a % 3, "Invalid collinear ternary differences.")
    i = next(i for i, x in enumerate(v) if x)
    q = [0]*len(v)
    q[i] = a*v[i] % 3
    require((tri_dot(q, v), tri_dot(q, w)) == (a, b),
            "Collinear affine interpolation failed.")
    return tuple(q)


def replay_qutrit_affine_recovery():
    """Finite DW5--DW6 guards; all-n grouping and interpolation are analytic."""
    plus_state = tri_matrix([[F(1, 2), F(1, 2)], [F(1, 2), F(1, 2)]])
    flip = tri_matrix([[0, 1], [1, 0]])
    symmetries, state_identities = set(), 0
    for shift, reflection in product(range(3), range(2)):
        rotation = tri_phase(shift)
        u = tri_matmul(rotation, flip) if reflection else rotation
        permutation = tuple((shift+(-k if reflection else k)) % 3
                            for k in range(3))
        symmetries.add(permutation)
        for k in range(3):
            require(tri_matmul(tri_matmul(u, tri_orbit(plus_state, k)),
                               tri_adjoint(u)) == tri_orbit(plus_state, permutation[k]),
                    "Trine permutation is not a unitary symmetry.")
            state_identities += 1
    require(len(symmetries) == 6, "Not all trine permutations are covered.")
    trine = [tri_orbit(plus_state, k) for k in range(3)]
    fair_ordinary = sum(F(1, 4)*tri_score(tri_scale(rho, F(2, 3)), rho)
                        for rho in trine)
    require(fair_ordinary == F(1, 2), "Fair qutrit recovery witness changed.")

    points = list(product(range(3), repeat=2))
    assignments = 0
    for count in [1, 2, 3]:
        for chosen in combinations(points, count):
            for colors in permutations(range(3), count):
                solutions = [(q, c) for q in points for c in range(3)
                             if all((tri_dot(q, p)+c) % 3 == k
                                    for p, k in zip(chosen, colors))]
                require(any(sum(x != 0 for x in q) <= 2 for q, _ in solutions),
                        "Selected qutrit labels cannot receive distinct colors.")
                assignments += 1

    vectors = [v for v in product(range(3), repeat=4) if any(v)]
    sparse_cases = independent = collinear = 0
    for v, w in product(vectors, repeat=2):
        if v == w:
            continue
        for a in [1, 2]:
            q = tri_sparse_functional(v, w, a, -a % 3)
            require(sum(x != 0 for x in q) <= 2 and
                    sum(any(q[2*j:2*j+2]) for j in range(2)) <= 2,
                    "Affine check exceeds the two-qutrit support bound.")
            sparse_cases += 1
        if w == tuple((-x) % 3 for x in v):
            collinear += 1
        else:
            independent += 1
    return {
        "status": "passed", "arithmetic": "exact F3 integers and Eisenstein rationals",
        "weighted_trine_unitary_permutations": len(symmetries),
        "trine_state_identities": state_identities,
        "single_qutrit_selected_point_color_assignments": assignments,
        "two_qutrit_sparse_functional_color_assignments": sparse_cases,
        "ordered_independent_difference_pairs": independent,
        "ordered_collinear_difference_pairs": collinear,
        "fair_binary_ordinary_fidelity": str(fair_ordinary),
        "scope": "Finite trine symmetry and sparse affine interpolation; all-n grouped-POVM dominance remains analytic.",
    }


def replay_common_control_noise():
    """Finite DN1--DN4 grouping, top-prior replacement and physical phase guards."""
    ident, empty = tri_matrix([[1, 0], [0, 1]]), tri_matrix([[0, 0], [0, 0]])
    plus_state = tri_matrix([[F(1, 2), F(1, 2)], [F(1, 2), F(1, 2)]])
    minus_state = tri_matrix([[F(1, 2), F(-1, 2)], [F(-1, 2), F(1, 2)]])
    z0, z1 = tri_matrix([[1, 0], [0, 0]]), tri_matrix([[0, 0], [0, 1]])

    def measure_prepare(rho):
        # Manifestly CPTP: X+ -> maximally mixed, X- -> |0>.
        pplus = tri_trace(tri_matmul(plus_state, rho))
        pminus = tri_trace(tri_matmul(minus_state, rho))
        return tri_plus(tri_cscale(tri_scale(ident, F(1, 2)), pplus),
                        tri_cscale(z0, pminus))

    u = tri_matrix([[F(3, 5), F(-4, 5)], [F(4, 5), F(3, 5)]])
    r = tri_matrix([[F(5, 13), F(-12, 13)], [F(12, 13), F(5, 13)]])
    k0 = tri_matrix([[1, 0], [0, F(3, 5)]])
    k1 = tri_matrix([[0, F(4, 5)], [0, 0]])
    weighted_kraus = [(F(2, 5), u), (F(3, 5), tri_matmul(k0, r)),
                     (F(3, 5), tri_matmul(k1, r))]
    total = empty
    for weight, k in weighted_kraus:
        total = tri_plus(total, tri_scale(tri_matmul(tri_adjoint(k), k), weight))
    require(total == ident, "Common control-noise example is not TP.")

    def mixed_rotation_damping(rho):
        out = empty
        for weight, k in weighted_kraus:
            out = tri_plus(out, tri_scale(tri_matmul(tri_matmul(k, rho),
                                                   tri_adjoint(k)), weight))
        return out

    labels = list(product(range(3), repeat=2))
    raw = [(a, b, F(1+17*(a == (0, 0) and b == (1, 0))
                    +11*(a == (0, 1) and b == (1, 1))+3*(a == b)))
           for a, b in product(labels, repeat=2)]
    total_weight = sum(weight for _, _, weight in raw)
    law = [(a, b, weight/total_weight) for a, b, weight in raw]
    base_povms = [
        [tri_scale(tri_orbit(plus_state, k), F(2, 3)) for k in range(3)],
        [tri_scale(z0, F(1, 3)), tri_scale(plus_state, F(2, 3)),
         tri_plus(tri_scale(z1, F(1, 3)), tri_scale(minus_state, F(2, 3)))],
    ]
    for base in base_povms:
        require(tri_plus(tri_plus(base[0], base[1]), base[2]) == ident,
                "Common-noise base POVM is not normalized.")

    guards = state_images = phase_checks = 0
    for prep in [plus_state, tri_matrix([[F(3, 5), F(1, 5)],
                                        [F(1, 5), F(2, 5)]])]:
        vertices = [tri_orbit(prep, k) for k in range(3)]
        masses, unnormalized = [F(0)]*9, [empty for _ in labels]
        for a, b, probability in law:
            e = ((a[0]+b[0]) % 3, (a[1]+b[1]) % 3)
            i = labels.index(e)
            k = (a[1]*b[0]-b[1]*a[0]) % 3
            masses[i] += probability
            unnormalized[i] = tri_plus(unnormalized[i],
                                       tri_scale(vertices[k], probability))
        require(sum(masses) == 1, "Qutrit joint law is not normalized.")
        for channel in [measure_prepare, mixed_rotation_damping]:
            noisy_vertices = [channel(v) for v in vertices]
            require(all(tri_trace(tau) == TRI_ONE for tau in noisy_vertices),
                    "Noisy control vertex is not normalized.")
            state_images += 3
            noisy_errors = [channel(rho) for rho in unnormalized]
            for base in base_povms:
                effects = [tri_scale(base[i % 3], F(i//3+1, 6)) for i in range(9)]
                total_effect = empty
                for effect in effects:
                    total_effect = tri_plus(total_effect, effect)
                require(total_effect == ident, "Nine-effect POVM is not normalized.")
                value = sum(tri_score(m, rho) for m, rho in zip(effects, noisy_errors))
                colors = [max(range(3), key=lambda k: tri_score(m, noisy_vertices[k]))
                          for m in effects]
                first_bound = sum(masses[i]*tri_score(effects[i], noisy_vertices[colors[i]])
                                  for i in range(9))
                grouped, selected = [empty, empty, empty], {}
                for i, color in enumerate(colors):
                    grouped[color] = tri_plus(grouped[color], effects[i])
                    if color not in selected or masses[i] > masses[selected[color]]:
                        selected[color] = i
                second_bound = sum(masses[i]*tri_score(grouped[k], noisy_vertices[k])
                                   for k, i in selected.items())
                require(value <= first_bound <= second_bound,
                        "Noisy-vertex grouping inequality failed.")
                # Replace the group maxima by globally dominant priors, keeping
                # the same vertices and effects. No noise-image symmetry is used.
                sorted_colors = sorted(selected, key=lambda k: masses[selected[k]],
                                       reverse=True)
                top = sorted(range(9), key=lambda i: masses[i], reverse=True)
                targets = dict(zip(sorted_colors, top))
                replacement = sum(masses[i]*tri_score(grouped[k], noisy_vertices[k])
                                  for k, i in targets.items())
                require(replacement >= second_bound,
                        "Global dominant priors decreased the grouped score.")
                q, offset = next((q, c) for q in labels for c in range(3)
                                 if all((tri_dot(q, labels[i])+c) % 3 == k
                                        for k, i in targets.items()))
                ordinary = F(0)
                for k, i in targets.items():
                    physical = channel(tri_orbit(tri_orbit(prep, tri_dot(q, labels[i])),
                                                 offset))
                    require(physical == noisy_vertices[k],
                            "Phase assignment was not applied before control noise.")
                    phase_checks += 1
                    ordinary += masses[i]*tri_score(grouped[k], physical)
                require(ordinary == replacement and ordinary >= value,
                        "Ordinary noisy-control recovery failed its bound.")
                guards += 1

    # A noncovariant binary channel: a phase after N cannot swap its images.
    z = tri_matrix([[1, 0], [0, -1]])
    mixed, pure = measure_prepare(plus_state), measure_prepare(minus_state)
    require(mixed == tri_scale(ident, F(1, 2)) and pure == z0,
            "Noncovariant image example changed.")
    require(measure_prepare(tri_matmul(tri_matmul(z, plus_state), z)) !=
            tri_matmul(tri_matmul(z, mixed), z), "Noise became phase covariant.")

    def classical_binary(first, second):
        return sum(max(F(3, 5)*tri_real(first[j][j]),
                       F(2, 5)*tri_real(second[j][j])) for j in range(2))

    wrong, optimized = classical_binary(mixed, pure), classical_binary(pure, mixed)
    require((wrong, optimized) == (F(7, 10), F(4, 5)),
            "Pre-noise phase-assignment witness changed.")
    return {
        "status": "passed", "arithmetic": "exact Eisenstein rationals",
        "different_CPTP_control_channels": 2,
        "fixed_common_control_preparations": 2,
        "nine_effect_POVMs_per_channel_preparation": len(base_povms),
        "physical_qutrit_joint_histories": len(law),
        "noisy_vertex_images": state_images,
        "convex_grouping_top_prior_and_ordinary_recovery_guards": guards,
        "physical_before_noise_phase_assignment_checks": phase_checks,
        "noncovariant_wrong_assignment_fidelity": str(wrong),
        "noncovariant_optimized_before_noise_assignment_fidelity": str(optimized),
        "scope": "Finite channel-image, grouped-POVM, top-prior and phase-ordering guards; general H_N optimum and all-n dominance remain analytic. No native performance is certified.",
    }


def main():
    pcs_cases = replay_pcs()
    read_cases = replay_read_oracles()
    router_cases = replay_qutrit_router()
    self_metric_cases, self_instrument_cases = replay_self_channel_routes()
    known_basis_cases, coherent_cross_cases = replay_known_basis_layers()
    loss_cases = replay_number_diagonal_loss()
    replacement_cases = replay_terminal_replacement()
    calibration_cases = replay_transported_pauli_calibration()
    deterministic_cases = replay_deterministic_pauli_weyl()
    affine_cases = replay_qutrit_affine_recovery()
    common_control_cases = replay_common_control_noise()
    print(json.dumps({
        "status": "passed", "arithmetic": "exact Gaussian and Eisenstein rational, standard library",
        "pcs_nonpauli_cases": pcs_cases, "read_oracle_cases": read_cases,
        "qutrit_router_flagged_kraus_identities": router_cases,
        "self_channel_quasistatic_full_choi_metric_cases": self_metric_cases,
        "self_channel_iid_full_control_choi_cases": self_instrument_cases,
        "known_basis_fault_full_choi_cases": known_basis_cases,
        "known_basis_coherent_cross_term_cases": coherent_cross_cases,
        "number_diagonal_loss_kraus_pair_cases": loss_cases,
        "terminal_replacement_contraction": replacement_cases,
        "transported_pauli_calibration": calibration_cases,
        "deterministic_pauli_weyl_recovery": deterministic_cases,
        "qutrit_affine_recovery": affine_cases,
        "common_control_noise_recovery": common_control_cases,
        "scope": "Finite projection, routing, loss, replacement and calibrated Pauli/Weyl recovery replay; general cb/diamond, recovery/POVM dominance, all-n interpolation, costs and physical hypotheses remain analytic.",
    }, sort_keys=True))


if __name__ == '__main__':
    main()
