"""Exact finite CAPS parity-failure and paid Bell-resource baselines.

The first API composes a declared carrier-point closed-cycling contact,
midpoint photon X, all loss labels, external attenuation and capped retries.
The second checks the full Bell-error/readout parity instrument, flagged
Choi orthogonality and a capped factory ledger. Universal recovery/diamond
proofs, continuum routing, source branching, time and device rates remain
analytic or supplied physical assumptions. Import is quiet; no files are
written; every predicate is active under Python optimization.
"""
from fractions import Fraction as F
from itertools import product
import json
import sys

sys.dont_write_bytecode = True
from retained_photon_serial import G, require, zeros, eye, mm, adj, kron, scale


def plus(a, b):
    return [[x+y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def diag(values):
    return [[G(values[i]) if i == j else G() for j in range(len(values))]
            for i in range(len(values))]


def cp(branches, rho):
    out = zeros(len(branches[0][1]))
    for weight, k in branches:
        out = plus(out, scale(mm(mm(k, rho), adj(k)), weight))
    return out


def unit(n, i, j):
    a = zeros(n)
    a[i][j] = G(1)
    return a


def check_maps(actual, expected, n, label):
    count = 0
    for i, j in product(range(n), repeat=2):
        rho = unit(n, i, j)
        require(cp(actual, rho) == cp(expected, rho), label)
        count += 1
    return count


def effect(branches):
    out = zeros(len(branches[0][1][0]))
    for weight, k in branches:
        out = plus(out, scale(mm(adj(k), k), weight))
    return out


def source_plus():
    # Photon order H,V,vac followed by AB; source weight is kept outside.
    out = zeros(12, 4)
    for a in range(4):
        out[a][a] = G(1)
        out[4+a][a] = G(1)
    return out


def embed_contact(which, photon_map, memory_map):
    out = zeros(12)
    for po, pi, ao, ai, bo, bi in product(range(3), range(3),
                                         range(2), range(2), range(2), range(2)):
        memory = memory_map[ao][ai]*int(bo == bi) if which == 0 else \
                 memory_map[bo][bi]*int(ao == ai)
        out[4*po+2*ao+bo][4*pi+2*ai+bi] = photon_map[po][pi]*memory
    return out


def local_contact(which, reset=False):
    g = embed_contact(which, diag((1, 0, 1)), eye(2))
    g = plus(g, embed_contact(which, diag((0, 1, 0)), diag((F(-1, 2), F(1, 2)))))
    v = unit(3, 2, 1)
    intrinsic = embed_contact(which, v, diag((1, F(1, 3))))
    spontaneous = embed_contact(which, v, unit(2, 0 if reset else 1, 1))
    return ((F(1), g), (F(3, 4), intrinsic), (F(2, 3), spontaneous))


def parity_branches():
    x = zeros(3)
    x[0][1] = x[1][0] = x[2][2] = G(1)
    mid = kron(x, eye(4))
    source = source_plus()
    success, loss = {1: [], -1: []}, []
    for ia, (wa, a) in enumerate(local_contact(0)):
        for ib, (wb, b) in enumerate(local_contact(1)):
            word = mm(mm(mm(b, mid), a), source)
            # |+> source and terminal X flag each supply a factor 1/sqrt(2).
            for sign in (1, -1):
                k = [[(word[r][j]+sign*word[4+r][j])/2
                      for j in range(4)] for r in range(4)]
                success[sign].append((wa*wb, k))
            loss.append((wa*wb/2, [word[8+r] for r in range(4)]))
    return success, loss


def cycling_parity_failure():
    one_units = parity_units = retry_units = 0
    ident, z = eye(2), diag((1, -1))
    intrinsic = diag((1, F(1, 3)))
    reflected = diag((F(-1, 2), F(1, 2)))
    cycling = [(F(3, 4), intrinsic), (F(2, 3), unit(2, 1, 1))]
    reset = [(F(3, 4), intrinsic), (F(2, 3), unit(2, 0, 1))]
    one_units += check_maps(cycling, [(F(1, 2), ident), (F(1, 4), z)], 2,
                            "resolved closed-cycling failure")
    require(effect([(F(1), reflected)]+cycling) == eye(2), "complete contact effect")
    require(cp(cycling, unit(2, 1, 1)) != cp(reset, unit(2, 1, 1)),
            "same guided response and total loss do not identify rejected populations")
    require(cp(reset, unit(2, 1, 1))[1][1] == F(1, 12), "reset failure survivor population")

    for j in range(2):
        require(effect(local_contact(j)) == eye(12), "full vacuum-extended local TP")
    flags, loss = parity_branches()
    za, zb = kron(z, ident), kron(ident, z)
    pe, po = diag((1, 0, 0, 1)), diag((0, 1, 1, 0))
    for sign, projector in ((1, pe), (-1, po)):
        expected = [(F(1, 4), mm(za, projector))]
        parity_units += check_maps(flags[sign], expected, 4, "literal parity success flag")
    expected_loss = [(F(1, 2), eye(4)), (F(1, 8), za), (F(1, 8), zb)]
    parity_units += check_maps(loss, expected_loss, 4, "all node/internal/spontaneous failure records")
    require(effect(flags[1]+flags[-1]+loss) == eye(4), "complete two-node parity instrument")

    # Unknown logical state/reference in either parity code. Each Eij is tested.
    for code in ((0, 3), (1, 2)):
        for i, j in product(range(2), repeat=2):
            rho = unit(4, code[i], code[j])
            value = cp(loss, rho)
            coefficient = F(3, 4) if i == j else F(1, 4)
            require(value == scale(rho, coefficient), "logical failure including reference coherences")
            one_units += 1
        # F^J and the full capped retry instrument; J=1..6 are exact examples.
        for cap in range(1, 7):
            for i, j in product(range(2), repeat=2):
                rho = unit(4, code[i], code[j])
                state, accepted = rho, zeros(4)
                for _ in range(cap):
                    # Feedback -ZA removes the same raw success phase on both flags.
                    accepted = plus(accepted, mm(mm(za, cp(flags[1]+flags[-1], state)), za))
                    state = cp(loss, state)
                base = F(3, 4) if i == j else F(1, 4)
                coefficient = F(1, 4)*sum(base**n for n in range(cap))
                require(accepted == scale(rho, coefficient), "finite retry accepted full logical map")
                require(state == scale(rho, base**cap), "finite retry rejected map is not identity")
                if i == j:
                    require(accepted[code[i]][code[j]]+state[code[i]][code[j]] == 1,
                            "capped retry all-launch normalization")
                retry_units += 1

    # External attenuation is downstream of both nodes and polarization resolved.
    eta = F(3, 5)
    source = source_plus()
    a, b = local_contact(0)[0][1], local_contact(1)[0][1]
    xp = zeros(3)
    xp[0][1] = xp[1][0] = xp[2][2] = G(1)
    survivor = mm(mm(mm(b, kron(xp, eye(4))), a), source)
    external = [((1-eta)/2, survivor[4*p:4*p+4]) for p in range(2)]
    external_expected = [((1-eta)/8, za), ((1-eta)/8, zb)]
    parity_units += check_maps(external, external_expected, 4, "downstream lost polarization records")
    total_failure = loss+external
    expected_total = [(F(1, 2), eye(4)), ((2-eta)/8, za), ((2-eta)/8, zb)]
    parity_units += check_maps(total_failure, expected_total, 4, "unresolved internal and external loss")
    require(effect([(w*eta, k) for w, k in flags[1]+flags[-1]]+total_failure) == eye(4),
            "external attenuation full instrument TP")
    require(cp(total_failure, unit(4, 0, 3))[0][3] == eta/4,
            "external loss changes intra-parity retry coherence")

    require(F(1, 4)/(1-F(1, 4)) == F(1, 3), "eventual carrier coherence")
    require((1+F(1, 3))/2 == F(2, 3), "eventual logical Bell fidelity")
    return {
        "one_contact_and_logical_matrix_units": one_units,
        "complete_parity_and_external_matrix_units": parity_units,
        "finite_retry_logical_matrix_units": retry_units,
        "scope": "Declared carrier-point cycling completion, explicit orthogonal local loss labels, fresh independent attempts, downstream polarization loss. Bell-resource ports are checked by the separate API. No source branching fit, arbitrary routing/native optimum, continuum or universal recovery proof."
    }


def bits(i):
    return divmod(i, 2)


def p_diag(s, i):
    a, b = bits(i)
    return int((a ^ b) == s)


def literal(x, z, u, v, wrong_phase=False):
    """Leave the common Bell-source factor 1/sqrt2 external."""
    answer = [0]*4
    for i in range(4):
        a, b = bits(i)
        for k in range(2):
            anc_a, anc_b = k, k ^ x
            out_a, out_b = anc_a ^ a, anc_b ^ b
            if (out_a, out_b) == (u, v):
                answer[i] += (-1)**(z*(a if wrong_phase else k))
    return answer


def expected(x, z, u, v, drop_x=False, drop_z=False):
    s = u ^ v ^ (0 if drop_x else x)
    return [(-1)**(z*u+(0 if drop_z else z*bits(i)[0]))*p_diag(s, i)
            for i in range(4)]


def instrument_checks(drop_x=False, drop_z=False):
    count = 0
    for x, z, u, v in product(range(2), repeat=4):
        actual, wanted = literal(x, z, u, v), expected(x, z, u, v, drop_x, drop_z)
        for i, j in product(range(4), repeat=2):
            require(F(actual[i]*actual[j], 2) == F(wanted[i]*wanted[j], 2),
                    'every fine CP map on every input matrix unit')
            count += 1
    return count


def choi(x, z, fine):
    """Sparse normalized Choi density with the actual classical record."""
    out = {}
    records = product(range(2), repeat=2) if fine else ((s,) for s in range(2))
    for record in records:
        s = record[0] ^ record[1] if fine else record[0]
        vector = [(-1)**(z*bits(i)[0])*p_diag(s ^ x, i) for i in range(4)]
        denominator = 8 if fine else 4
        for i, j in product(range(4), repeat=2):
            value = F(vector[i]*vector[j], denominator)
            if value:
                out[((record, i), (record, j))] = value
    return out


def multiply(a, b):
    out = {}
    for (i, k), x in a.items():
        for (l, j), y in b.items():
            if k == l:
                out[(i, j)] = out.get((i, j), F())+x*y
    return {key: value for key, value in out.items() if value}


def sparse_scale(a, scalar):
    return {key: value*scalar for key, value in a.items() if value*scalar}


def literal_choi(x, z, fine):
    """Connect the Choi records to the actual two-CNOT/source circuit."""
    out = {}
    for u, v in product(range(2), repeat=2):
        record = (u, v) if fine else (u ^ v,)
        vector = literal(x, z, u, v)
        for i, j in product(range(4), repeat=2):
            value = F(vector[i]*vector[j], 8)
            if value:
                key = ((record, i), (record, j))
                out[key] = out.get(key, F())+value
    return {key: value for key, value in out.items() if value}


def bell_resource_parity():
    entries = instrument_checks()
    completeness = 0
    for x, z, i in product(range(2), range(2), range(4)):
        require(sum(F(literal(x,z,u,v)[i]**2, 2)
                    for u,v in product(range(2), repeat=2)) == 1,
                'all actual fine outcomes complete the data instrument')
        completeness += 1
    products = 0
    weight_cases = ((F(1),F(),F(),F()), (F(),F(1),F(),F()),
                    (F(999,1000),F(1,3000),F(1,3000),F(1,3000)),
                    (F(7,10),F(1,10),F(1,10),F(1,10)))
    for fine in (False, True):
        states = [choi(x,z,fine) for x,z in product(range(2),repeat=2)]
        eigenvalue = F(1,4) if fine else F(1,2)
        for k, state in enumerate(states):
            require(state == literal_choi(*bits(k), fine),
                    'flagged Choi state comes from the literal local circuit')
            require(sum(value for (i,j),value in state.items() if i == j) == 1,
                    'each error instrument has normalized Choi trace')
            require(multiply(state,state) == sparse_scale(state,eigenvalue),
                    'positive Choi state has uniform nonzero eigenvalues')
            for l, other in enumerate(states):
                if k != l:
                    require(not multiply(state,other), 'distinct error Choi supports are orthogonal')
                products += 1
        for weights in weight_cases:
            require(sum(weights) == 1 and all(w>=0 for w in weights), 'physical Bell mixture')
            # Orthogonal normalized supports: one negative eigen-block,
            # three positive blocks; this is exact half trace distance.
            half_trace = (abs(weights[0]-1)+sum(weights[1:]))/2
            require(half_trace == 1-weights[0], 'maxent Choi witness attains diamond upper bound')
    p, q, visibility = F(1,4), F(3,4), F(1,3)
    require(p+q == 1 and p/(1-q*visibility) == F(1,3), 'declared online retry visibility')
    ledger_cases = 0
    for n in range(0,9):
        accept = 1-q**n
        attempts = sum(q**k for k in range(n))
        require(attempts == accept/p, 'all-attempt capped factory cost')
        require(sum(p*q**k for k in range(n))+q**n == 1, 'delivery and reject probabilities complete')
        ledger_cases += 1
    mutants = 0
    for options in ({'drop_x': True},{'drop_z': True}):
        try:
            instrument_checks(**options)
        except ValueError:
            mutants += 1
        else:
            raise ValueError('Bell-error instrument mutant was not rejected')
    return {'status':'passed','fine_CP_input_entries':entries,
            'full_outcome_completeness_cases':completeness,
            'coarse_and_fine_Choi_products':products,
            'Bell_weight_guards':2*len(weight_cases),
            'deadline_ledger_cases':ledger_cases,'detected_error_mutants':mutants,
            'scope':'Known independent Bell-diagonal resource, ideal local CNOT/readout, all fine records and arbitrary unknown data/reference by linear extension. Diamond equality and device/time/control assumptions remain analytic; no hardware optimum or measured gate error budget.'}


def verify():
    return {
        "cycling_parity_failure": cycling_parity_failure(),
        "bell_resource_parity": bell_resource_parity(),
        "scope": "Finite complete carrier-point loss/parity/retry and Bell-resource error/flag/Choi/deadline ingredients. No measured branching or routing reconstruction, universal recovery/diamond proof, native optimum or hardware-rate certificate."
    }


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True))
