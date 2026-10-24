"""Exact finite guard for the NR-R06 final-flag completion comparison.

The diamond inequality is analytic in methods/final-flag-completion.md. This finite
replay certifies the CP decompositions on all matrix units, including an
explicit identity reference, without numerical matrix norms or dependencies.
Import is quiet and guards remain active under optimized Python.
"""
from fractions import Fraction as F
from itertools import product
import json


from retained_photon_serial import G, require, eye, zeros, mm, adj, add, scale


def equal(a, b, label):
    require(a == b, label)


def trace(a):
    return sum((a[i][i] for i in range(len(a))), G())


def unitary(a):
    equal(mm(adj(a), a), eye(len(a)), "fixture unitary")


def diagonal(values):
    a = zeros(len(values))
    for i, z in enumerate(values):
        a[i][i] = G(z)
    return a


def rotation(d, i, j, c, s, imaginary=False):
    a = eye(d)
    a[i][i] = a[j][j] = G(c)
    if imaginary:
        a[i][j] = a[j][i] = G(0, s)
    else:
        a[i][j], a[j][i] = G(s), G(-s)
    unitary(a)
    return a


def power(a, n):
    out = eye(len(a))
    for _ in range(n):
        out = mm(a, out)
    return out


def comm(a, b):
    return add(mm(a, b), scale(mm(b, a), -1))


def cubic_witness(d):
    a = zeros(d)
    a[0][1] = a[1][0] = G(1)
    if d == 3:
        a[1][2] = a[2][1] = G(2)
    b = diagonal([1, -1] if d == 2 else [1, 0, -1])
    x, y = scale(a, G(0, -1)), scale(b, G(0, -1))
    cross = add(add(mm(power(x, 2), y), mm(x, power(y, 2))),
                add(mm(power(y, 2), x), mm(y, power(x, 2))))
    avg_cubic = add(scale(add(power(x, 3), power(y, 3)), F(1, 6)),
                    scale(cross, F(1, 4)))
    target_cubic = scale(power(add(x, y), 3), F(1, 6))
    actual = add(avg_cubic, scale(target_cubic, -1))
    nested = scale(add(comm(x, comm(x, y)), comm(y, comm(y, x))), F(1, 12))
    equal(actual, nested, "exact noncommuting cubic coefficient")
    require(actual != zeros(d), "generic second-order obstruction")
    if d == 2:
        equal(actual, scale(add(a, b), G(0, F(1, 3))),
              "Pauli cubic coefficient sign and normalization")


def cyclic(d):
    out = zeros(d)
    for j in range(d):
        out[(j+1) % d][j] = G(1)
    return out


def fixture(d):
    if d == 2:
        a = diagonal([G(F(3, 5), F(4, 5)), G(F(3, 5), -F(4, 5))])
        b = rotation(2, 0, 1, F(5, 13), F(12, 13))
    else:
        a = diagonal([G(1), G(F(3, 5), F(4, 5)),
                      G(F(5, 13), F(12, 13))])
        b = mm(rotation(3, 1, 2, F(8, 17), F(15, 17), imaginary=True),
               rotation(3, 0, 1, F(5, 13), F(12, 13)))
    unitary(a)
    unitary(b)
    require(mm(a, b) != mm(b, a), "noncommuting module witness")
    return a, b


def steps(d, count, varying):
    a, b = fixture(d)
    out = []
    for j in range(count):
        q = power(cyclic(d), j if varying else 0)
        aj = mm(mm(q, a), adj(q))
        u, v = mm(b, aj), mm(aj, b)
        kp = scale(add(u, v), F(1, 2))  # MUTANT_NORMALIZATION
        km = scale(add(u, scale(v, -1)), F(1, 2))  # MUTANT_FLAG_SIGN
        equal(add(mm(adj(kp), kp), mm(adj(km), km)), eye(d),
              "complete two-flag effect")
        require(km != zeros(d), "nonzero rejected amplitude")
        out.append((u, v, kp, km))
    return out


def history_operators(step_list, quantum):
    out = []
    d = len(step_list[0][0])
    for word in product((0, 1), repeat=len(step_list)):
        k = eye(d)
        for bit, st in zip(word, step_list):
            k = mm(st[2+bit] if quantum else st[bit], k)
        out.append((word, k))
    return out


def effect(kraus, d):
    out = zeros(d)
    for weight, k in kraus:
        require(weight >= 0, "nonnegative Kraus weight")
        out = add(out, scale(mm(adj(k), k), weight))
    return out


def coefficients(kraus, d):
    """All input E_ij, output entries rs, in fixed i,j,r,s order."""
    return {(i, j, r, s): sum((weight*k[r][i]*k[s][j].conj()
                              for weight, k in kraus), G())
            for i, j, r, s in product(range(d), repeat=4)}


def compare_maps(left, right, d, label, counts):
    lc, rc = coefficients(left, d), coefficients(right, d)
    equal(lc, rc, label)
    counts["payload_matrix_unit_coefficients"] += d**4
    # Explicitly tensor identity on a d-dimensional reference: all input
    # E_ij tensor E_kl and every output payload/reference matrix coefficient.
    for i, j, k, l, r, s, q, t in product(range(d), repeat=8):
        ref_entry = int(q == k and t == l)
        equal(lc[i, j, r, s]*ref_entry, rc[i, j, r, s]*ref_entry,
              label+" with arbitrary reference matrix unit")
    counts["reference_matrix_unit_coefficients"] += d**8


def compose_decoder(kraus, decoder):
    return [(w*z, mm(d, k)) for w, k in kraus for z, d in decoder]


def mass_on_basis(effect_matrix, i):
    value = effect_matrix[i][i]
    require(value.i == 0, "survival probability real")
    return value.r


def run():
    counts = {"dimensions": [2, 3], "cases": 0,
              "nonzero_cubic_witnesses": 0,
              "quantum_histories": 0, "ordinary_histories": 0,
              "payload_matrix_unit_coefficients": 0,
              "reference_matrix_unit_coefficients": 0,
              "reject_trace_matrix_units": 0, "call_ledger_inputs": 0,
              "reject_payload_inequality_witnesses": 0}
    for d in (2, 3):
        cubic_witness(d)
        counts["nonzero_cubic_witnesses"] += 1
    for d, varying, r in product((2, 3), (False, True), (1, 2, 3)):
        st = steps(d, r, varying)
        qhist = history_operators(st, True)
        ohist = history_operators(st, False)
        all_native = [(F(1), k) for _, k in qhist]
        ordinary = [(F(1, 2**r), k) for _, k in ohist]
        accepted = [(F(1), qhist[0][1])]
        complement = [(F(1), k) for word, k in qhist if any(word)]  # MUTANT_HISTORY
        counts["quantum_histories"] += len(qhist)
        counts["ordinary_histories"] += len(ohist)
        compare_maps(ordinary, all_native, d, "ignored flags equal random order", counts)
        compare_maps(ordinary, accepted+complement, d, "explicit CP completion", counts)
        equal(effect(ordinary, d), eye(d), "ordinary channel TP")
        equal(effect(all_native, d), eye(d), "all flags TP")
        # D is a nonunitary, CPTP dephasing decoder with rational weights.
        z = diagonal([(-1)**j for j in range(d)])
        decoder = [(F(1, 2), eye(d)), (F(1, 2), z)]
        equal(effect(decoder, d), eye(d), "common decoder TP")
        compare_maps(compose_decoder(ordinary, decoder),
                     compose_decoder(accepted+complement, decoder), d,
                     "common CPTP decoder preserves completion", counts)
        # First-minus abort leaves no later payload calls. Its payload map
        # generally differs from the full-history complement, but its effect
        # and trace on every input matrix unit agree exactly.
        prefix = eye(d)
        abort = []
        prefixes = [eye(d)]
        for _, _, kp, km in st:
            abort.append((F(1), mm(km, prefix)))
            prefix = mm(kp, prefix)
            prefixes.append(mm(adj(prefix), prefix))
        ea, et, ep = effect(abort, d), effect(complement, d), effect(accepted, d)
        equal(ea, et, "early-abort/full-history rejection effects")
        equal(add(ep, ea), eye(d), "accepted plus rejected instrument complete")
        ca, ct = coefficients(abort, d), coefficients(complement, d)
        for i, j in product(range(d), repeat=2):
            equal(sum((ca[i, j, s, s] for s in range(d)), G()),
                  sum((ct[i, j, s, s] for s in range(d)), G()),
                  "reject trace on input matrix unit")
            counts["reject_trace_matrix_units"] += 1
        if ca != ct:
            counts["reject_payload_inequality_witnesses"] += 1
        # Exact mean call ledger and the always-success accuracy implication:
        # for epsilon=p_fail(input), E_Q >= 2r(1-epsilon).
        for i in range(d):
            survival = [mass_on_basis(p, i) for p in prefixes]
            require(survival[0] == 1, "initial survival")
            require(all(0 <= s <= 1 for s in survival), "physical survival")
            require(all(survival[j] >= survival[j+1] for j in range(r)),
                    "prefix survival monotone")
            mean_calls = 2*sum(survival[:-1])
            failure = 1-survival[-1]
            first_failure = []
            for k in range(r):
                fk = effect([abort[k]], d)[i][i]
                require(fk.i == 0 and fk.r >= 0, "first-reject mass positive")
                first_failure.append(fk.r)
            equal(sum(first_failure), failure, "first-reject probability ledger")
            # All-plus runs execute r rounds; first rejection at k+1 executes k+1.
            event_calls = 2*(r*survival[-1] + sum((k+1)*p
                                                for k, p in enumerate(first_failure)))
            equal(mean_calls, event_calls, "survival/event expected-call equality")
            require(2*r*(1-failure) <= mean_calls <= 2*r,
                    "high-accuracy expected-call inequality")
            counts["call_ledger_inputs"] += 1
        counts["cases"] += 1
    require(counts["reject_payload_inequality_witnesses"] >= 1,
            "reject map equality is not assumed")
    return counts


def verify():
    result = run()
    return {"status": "passed",
            "arithmetic": "Gaussian rational matrices; standard library",
            **result,
            "scope": "Finite noncommuting 2D/3D unitary fixtures, static/varying steps, r=1,2,3; exact random-order/all-flags CP completion on all payload and reference matrix units, common CPTP decoder, abort effects/traces, mean-call ledgers and nonzero cubic witnesses. Final-flag diamond/payoff inequalities, general exponential and survival bounds are analytic. No finite diamond-norm computation, physical coherent routing, persistent-bath reduction, branch-dependent/retained-control decoding, legitimate accepted-only service or exact equal-mean-cost claim."}


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True))
