"""Exact private-program resource and factory ingredients for NR-R19.

The Gaussian-rational matrix engine is reused without running its parent
certificate. All checks remain active under -O and import is quiet. The
checks perform no explicit file I/O; use -B or the caller's bytecode flag
for cache-free loading. General all-angle, privacy, native access, full
physical loss/clock and hardware-cost deductions remain analytic.
"""
from fractions import Fraction as F
from itertools import product
import json
import sys

sys.dont_write_bytecode = True
from retained_photon_serial import G, add, adj, blockdiag, cp_difference, cp_equal, eye, kron, mm, require, scale, zeros

def verify():
    identity, x, z = eye(2), [[G(), G(1)], [G(1), G()]], [[G(1), G()], [G(), G(-1)]]
    y = [[G(), G(0, -1)], [G(0, 1), G()]]
    p0, p1 = [[G(1), G()], [G(), G()]], [[G(), G()], [G(), G(1)]]
    xp, xm = scale(add(identity, x), F(1, 2)), scale(add(identity, scale(x, -1)), F(1, 2))
    ua = add(kron(kron(p0, identity), identity), kron(kron(p1, x), identity))
    ub = add(kron(kron(xp, identity), identity), kron(kron(xm, identity), x))
    kab = add(eye(4), scale(kron(xm, xm), -2))
    k = kron(identity, kab)
    require(mm(ua, ub) == mm(k, mm(ub, ua)), "central photon commutator relation")
    require(mm(k, ua) == mm(ua, k) and mm(k, ub) == mm(ub, k), "centrality")
    controlled = blockdiag(eye(8), k)
    ordered = blockdiag(mm(ub, ua), mm(ua, ub))
    ordinary = mm(controlled, blockdiag(mm(ub, ua), mm(ub, ua)))
    require(ordered == ordinary and mm(adj(ordered), ordered) == eye(16), "full known-unitary compiler")
    full_units = cp_equal(ordered, ordinary)
    fresh = [[ordered[row][c*8+s*4] for c, s in product(range(2), repeat=2)] for row in range(16)]
    fresh_ordinary = [[ordinary[row][c*8+s*4] for c, s in product(range(2), repeat=2)] for row in range(16)]
    fresh_units = cp_equal(fresh, fresh_ordinary)
    # Same fresh-source isometry, different nonblank-input extension.
    ua_alternative = mm(ua, kron(kron(identity, z), identity))
    require(mm(adj(ua_alternative), ua_alternative) == eye(8), "alternative unitary extension")
    require(all(ua[row][s*4+pb] == ua_alternative[row][s*4+pb]
                for row, s, pb in product(range(8), range(2), range(2))),
            "extensions agree on every fresh-a column")
    alternative_order = blockdiag(mm(ub, ua_alternative), mm(ua_alternative, ub))
    alternative_fresh = [[alternative_order[row][c*8+s*4]
                          for c, s in product(range(2), repeat=2)] for row in range(16)]
    require(alternative_fresh == fresh, "native fresh-source instrument ignores extension choice")
    wrong_offline = mm(blockdiag(mm(ub, ua_alternative), mm(ub, ua_alternative)), controlled)
    wrong_offline_fresh = [[wrong_offline[row][c*8+s*4]
                           for c, s in product(range(2), repeat=2)] for row in range(16)]
    extension_witness = cp_difference(fresh, wrong_offline_fresh)
    require(extension_witness is not None, "fresh source columns do not certify offline nonblank ports")

    def pauli(bit, op):
        return op if bit else identity

    def proportional(a, b):
        row, col = next((r, c) for r, c in product(range(2), repeat=2) if b[r][c] != 0)
        return a == scale(b, a[row][col]/b[row][col])

    phases = [(G(1), G(1)), (G(0, 1), G(0, 1)),
              (G(F(3, 5), F(4, 5)), G(F(5, 13), F(12, 13))),
              (G(F(-5, 13), F(12, 13)), G(F(-3, 5), F(4, 5)))]
    branch_units = 0
    for case, (phase_a, phase_b) in enumerate(phases):
        require(phase_a*phase_a.conj() == 1 and phase_b*phase_b.conj() == 1, "unit phases")
        a = [[G(1), G()], [G(), phase_a]]
        b = scale([[1+phase_b, 1-phase_b], [1-phase_b, 1+phase_b]], F(1, 2))
        target = blockdiag(mm(b, a), mm(a, b))
        branches = []
        for key_a, key_b in product(range(2), repeat=2):
            branch = zeros(4)
            for cout, sout, cin, sinput in product(range(2), repeat=4):
                branch[cout*2+sout][cin*2+sinput] = sum(
                    (fresh[cout*8+sout*4+pa*2+pb][cin*2+sinput]
                     * (-1)**(key_a*pa+key_b*pb)
                     * (phase_a if pa else G(1)) * (phase_b if pb else G(1))
                     for pa, pb in product(range(2), repeat=2)), G())/2
            ak, bk = mm(pauli(key_a, z), a), mm(pauli(key_b, x), b)
            expected = scale(blockdiag(mm(bk, ak), mm(ak, bk)), F(1, 2))
            require(branch == expected, "all module-labelled key amplitudes and order phases")
            require(mm(adj(branch), branch) == scale(eye(4), F(1, 4)), "uniform full-input keys")
            branch_units += cp_equal(branch, expected)
            branches.append(branch)
            c0 = mm(mm(mm(b, pauli(key_a, z)), adj(b)), pauli(key_b, x))
            c1 = mm(mm(mm(a, pauli(key_b, x)), adj(a)), pauli(key_a, z))
            require(mm(blockdiag(c0, c1), branch) == scale(target, F(1, 2)),
                    "exact order-dependent branch correction")
            if case == 0 and key_a == key_b == 1:
                require(branch == scale(kron(z, mm(x, z)), F(1, 2)), "key11 relative control-Z phase")
            if case == 2 and (key_a, key_b) in ((1, 0), (0, 1), (1, 1)):
                require(not proportional(c0, c1), "generic correction is not one common data unitary")
            if case == 2 and (key_a, key_b) == (1, 0):
                require(not any(proportional(c0, p) for p in (identity, x, y, z)), "generic key10 needs non-Pauli correction")
        # All server-side CS/R matrix units match the premeasurement partial
        # trace, independently of the private phases and without reading keys.
        for i, j, row, col in product(range(4), repeat=4):
            measured = sum((branch[row][i]*branch[col][j].conj() for branch in branches), G())
            unmeasured = sum((fresh[row*4+p][i]*fresh[col*4+p][j].conj() for p in range(4)), G())
            require(measured == unmeasured, "unkeyed channel is client-angle independent")
    # Moving controlled K offline is an identity for the full CNOT extensions;
    # fresh-source isometries alone do not promise this nonblank input port.
    require(mm(controlled, blockdiag(ua, ua)) == mm(blockdiag(ua, ua), controlled)
            and mm(controlled, blockdiag(ub, ub)) == mm(blockdiag(ub, ub), controlled),
            "offline algebraic commutation")
    cab = blockdiag(eye(4), kab)
    initial = [[G(int(index in (0, 4)))] for index in range(8)]
    omega = mm(cab, initial)
    h2 = scale(kron([[G(1), G(1)], [G(1), G(-1)]],
                    [[G(1), G(1)], [G(1), G(-1)]]), F(1, 2))
    ccz = eye(8)
    ccz[7][7] = G(-1)
    magic = scale(mm(kron(identity, h2), mm(ccz, [[G(1)] for _ in range(8)])), F(1, 2))
    require(omega == magic, "fixed-plus control resource is locally a CCZ magic state")
    # A distinct native factory uses only fresh a,b and known S=0. Its
    # S-X branches, after X_b feedback, encode arbitrary C/R as cab columns.
    target_factory = [[cab[row][cin*4] for cin in range(2)] for row in range(8)]
    factory_units = 0
    for h in (1, -1):
        numerator = [[sum((ordered[cout*8+s*4+pa*2+pb][cin*8] * h**s
                           for s in range(2)), G())
                      for cin in range(2)]
                     for cout, pa, pb in product(range(2), repeat=3)]
        corrected = numerator if h == 1 else mm(kron(kron(identity, identity), x), numerator)
        require(corrected == target_factory, "fresh-source native factory preserves C/R on both flags")
        require(scale(mm(adj(numerator), numerator), F(1, 2)) == scale(identity, F(1, 2)),
                "factory X flags each have probability one half")
        factory_units += cp_equal(corrected, target_factory)
    # Ordinary factory: two known matter CH controls and two fresh copies.
    # The two H factors in the C=1 block have total rational scale 1/2.
    uzb = add(kron(kron(p0, identity), identity), kron(kron(p1, identity), x))
    h_numerator = kron(kron([[G(1), G(1)], [G(1), G(-1)]], identity), identity)
    factory_ordinary = blockdiag(mm(uzb, ua),
        scale(mm(uzb, mm(h_numerator, mm(ua, h_numerator))), F(1, 2)))
    require(mm(adj(factory_ordinary), factory_ordinary) == eye(16), "ordinary controlled-H factory unitary")
    require(mm(h_numerator, mm(ub, h_numerator)) == scale(uzb, 2),
            "JX-to-JZ Hadamard source wrapper")
    ordinary_factory_units = 0
    for h in (1, -1):
        numerator = [[sum((factory_ordinary[cout*8+s*4+pa*2+pb][cin*8] * h**s
                           for s in range(2)), G())
                      for cin in range(2)]
                     for cout, pa, pb in product(range(2), repeat=3)]
        corrected = numerator if h == 1 else mm(kron(kron(identity, identity), z), numerator)
        require(corrected == target_factory, "ordinary CH factory matches all C/R amplitudes")
        require(mm(adj(numerator), numerator) == identity, "ordinary factory flags have equal half weight")
        ordinary_factory_units += cp_equal(corrected, target_factory)
    return {"status": "passed", "full_extension_matrix_units": full_units,
            "fresh_resource_CSR_matrix_units": fresh_units,
            "client_phase_pairs": len(phases), "all_key_matrix_units": branch_units,
            "unkeyed_CSR_matrix_units_per_pair": 16, "fresh_factory_CR_matrix_units": factory_units,
            "ordinary_CH_factory_CR_matrix_units": ordinary_factory_units,
            "ordinary_CH_factory_local_controls": 2,
            "nonblank_extension_CP_witness": extension_witness,
            "scope": "exact finite fresh-resource/key/relative-phase compiler, native and ordinary local-CH factories, and a nonblank-extension counterexample; the supplied joint CCZ and local matter controls are distinct priced ports. All-angle identities, privacy/security, state-dependent source/loss/clock maps and actual hardware comparisons remain analytic or unprovided. No prior, resource optimum or physical advantage certificate."}

if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True))
