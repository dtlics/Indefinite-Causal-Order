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


def injection_rollback_guards(encoding, photon_k):
    """Finite recorded C/reference instruments, with square roots cleared.

    Resource Omega has an external factor 1/sqrt(2). Each unnormalized
    X bra below has its external factor 1/sqrt(2) kept in a CP weight.
    Only actual classical fine records are combined: their global phases
    are not asserted to agree for a coherent history register.
    """
    identity = eye(2)
    z = [[G(1), G()], [G(), G(-1)]]
    f0 = [[G(int(i == 0))] for i in range(4)]
    f1 = mm(photon_k, f0)
    require(f1 == [[G(F(1, 2))], [G(F(1, 2))],
                   [G(F(1, 2))], [G(F(-1, 2))]], "injection resource graph signs")
    require(adj(photon_k) == photon_k and mm(photon_k, photon_k) == eye(4),
            "injection joint-K correction is an involution")
    expected_encoding = zeros(8, 2)
    for c, ab in product(range(2), range(4)):
        expected_encoding[c*4+ab][c] = (f0 if c == 0 else f1)[ab][0]
    require(encoding == expected_encoding and mm(adj(encoding), encoding) == identity,
            "injection encoding includes its nonorthogonal photon overlap")
    # Registers are input C, resource c, a, b. C and c are distinct.
    incoming = kron(identity, f0+f1)
    cnot = [[G(int(row == ((col ^ 4) if col >= 8 else col)))
             for col in range(16)] for row in range(16)]
    require(mm(adj(cnot), cnot) == eye(16), "injection C-to-resource-c CNOT")
    after = mm(cnot, incoming)
    branches = []
    injection_units = 0
    for m in range(2):
        branch = [[after[c*8+m*4+ab][cin] for cin in range(2)]
                  for c, ab in product(range(2), range(4))]
        target = encoding if m == 0 else mm(kron(identity, photon_k), encoding)
        require(branch == target and mm(adj(branch), branch) == identity,
                "both injection flags preserve all C/reference amplitudes at half weight")
        injection_units += cp_equal(branch, target)
        repaired = branch if m == 0 else mm(kron(identity, photon_k), branch)
        require(repaired == encoding, "joint-K deterministic injection correction")
        branches.append(branch)
    require(add(scale(mm(adj(branches[0]), branches[0]), F(1, 2)),
                scale(mm(adj(branches[1]), branches[1]), F(1, 2))) == identity,
            "complete recorded injection is trace preserving")
    failed = branches[1]
    rollback_units = 0
    rollback_effect = zeros(2)
    always_read = []
    for s, t in product(range(2), repeat=2):
        bra = [[G((-1)**(s*a+t*b)) for a, b in product(range(2), repeat=2)]]
        sign = G((-1)**(s*t))
        require(mm(bra, f0) == [[G(1)]] and mm(bra, f1) == [[sign]],
                "X/X photon erasure overlap signs")
        raw = mm(kron(identity, bra), failed)
        require(raw == [[sign, G()], [G(), G(1)]],
                "fine X/X rollback retains its relative C phase")
        corrected = mm(z if s*t else identity, raw)
        require(corrected == scale(identity, sign),
                "local Z rollback leaves only a classical-record global sign")
        rollback_units += cp_equal(corrected, identity)
        rollback_effect = add(rollback_effect, scale(mm(adj(raw), raw), F(1, 8)))
        always_read.append((corrected, F(1, 8)))
    require(rollback_effect == scale(identity, F(1, 2)),
            "all four X/X rollback records sum to half-weight identity")
    # Adaptive b-X first: t=0 leaves a known |0>, with no a measurement.
    after_b = []
    for t in range(2):
        after_b.append([[sum((G((-1)**(t*b))*failed[c*4+a*2+b][cin]
                              for b in range(2)), G())
                         for cin in range(2)]
                        for c, a in product(range(2), repeat=2)])
    blank_a = kron(identity, [[G(1)], [G()]])
    copied_a = [[G(), G()], [G(1), G()], [G(), G(1)], [G(), G()]]
    require(after_b[0] == blank_a and after_b[1] == copied_a,
            "adaptive first flag distinguishes blank-a from the coherent C/a copy")
    adaptive_units = cp_equal(after_b[0], blank_a)
    # Removing the known blank a is safe on every C/reference matrix unit.
    erased_blank = [[after_b[0][c*2][cin] for cin in range(2)] for c in range(2)]
    require(erased_blank == identity, "unmeasured blank photon factors from C/reference")
    adaptive = [(erased_blank, F(1, 4))]
    adaptive_effect = scale(mm(adj(after_b[0]), after_b[0]), F(1, 4))
    for s in range(2):
        raw = mm(kron(identity, [[G(1), G((-1)**s)]]), after_b[1])
        corrected = mm(z if s else identity, raw)
        require(corrected == scale(identity, (-1)**s),
                "adaptive first-minus uses a-X and one local Pauli frame")
        adaptive_units += cp_equal(corrected, identity)
        adaptive_effect = add(adaptive_effect, scale(mm(adj(raw), raw), F(1, 8)))
        adaptive.append((corrected, F(1, 8)))
    require(adaptive_effect == scale(identity, F(1, 2)),
            "three adaptive rollback records sum to half-weight identity")
    require(F(1, 4)*1+2*F(1, 8)*2 == F(3, 4),
            "adaptive readouts average three halves conditional on rollback")
    # A delayed Z key commutes through future injection CNOTs. It still
    # must be known before an incompatible C use or a fixed-frame output.
    frame = kron(z, eye(8))
    require(mm(frame, cnot) == mm(cnot, frame)
            and mm(encoding, z) == mm(kron(z, eye(4)), encoding),
            "rollback phase frames can be transported through later injections")

    def fine_histories(records):
        # Multiply actual corrected fine Kraus numerators. CP tests keep
        # every input E_ij, hence arbitrary references, at every frontier.
        frontier = [(identity, F(1))]
        accepted = F()
        success_histories = rejection_histories = units = 0
        for attempt in range(1, 5):
            this_success = F()
            for prefix, weight in frontier:
                leaf = mm(branches[0], prefix)
                units += cp_equal(leaf, encoding)
                require(mm(adj(leaf), leaf) == identity,
                        "each actual success history is the normalized encoding channel")
                this_success += weight/2
                success_histories += 1
            require(this_success == F(1, 2)**attempt,
                    "actual fine histories have the first-success probability")
            accepted += this_success
            frontier = [(mm(op, prefix), weight*op_weight)
                        for prefix, weight in frontier for op, op_weight in records]
            rejected = F()
            for prefix, weight in frontier:
                units += cp_equal(prefix, identity)
                require(mm(adj(prefix), prefix) == identity,
                        "the final capped failure is also erased and corrected")
                rejected += weight
                rejection_histories += 1
            require(rejected == F(1, 2)**attempt and accepted+rejected == 1,
                    "actual fine success and restored-rejection instruments are complete")
        return {"maximum_cap": 4, "success_histories": success_histories,
                "restored_rejection_histories": rejection_histories,
                "C_reference_matrix_units": units}

    always_histories = fine_histories(always_read)
    adaptive_histories = fine_histories(adaptive)
    cap_cases = 0
    for cap in range(1, 9):
        reject = F(1, 2)**cap
        accepted = sum((F(1, 2)**j for j in range(1, cap+1)), F())
        attempts = sum((F(1, 2)**j for j in range(cap)), F())
        failures = attempts-accepted
        require(accepted == 1-reject and attempts == 2*(1-reject)
                and failures == 1-reject,
                "capped delivered/restored-rejected probability and mean resource ledger")
        require(2*attempts == 4*(1-reject)
                and 2*failures+2*accepted == 2*attempts
                and F(3, 2)*failures == F(3, 2)*(1-reject),
                "ideal two-call factories, consumed/retained photons and adaptive readouts")
        cap_cases += 1
    return {"status": "passed", "injection_C_reference_matrix_units": injection_units,
            "X_X_rollback_C_reference_matrix_units": rollback_units,
            "adaptive_rollback_C_reference_matrix_units": adaptive_units,
            "always_read_fine_histories": always_histories,
            "adaptive_fine_histories": adaptive_histories, "rational_cap_cases": cap_cases,
            "scope": "finite exact classical-record injection, full C/reference X/X and adaptive rollback, actual fine Kraus histories through cap four, and capped ideal cost ingredients through cap eight. A delivered retained independent resource and a populated-target C-to-c CNOT are premises; source/loss/readout faults, physical ports, asynchronous timing, privacy and resource optimality are not certified."}


def balanced_source_factory_guards():
    """Pure selected fresh-source fixtures; F is not a supplied channel.

    Here r0,r1 name effective selected coefficients h, not the deposited
    cavity parameter before its complex conjugation and common frame.
    This does not reconstruct the deposited source or its rejected bath.
    """
    identity, x, z = eye(2), [[G(), G(1)], [G(1), G()]], [[G(1), G()], [G(), G(-1)]]
    p0, p1 = [[G(1), G()], [G(), G()]], [[G(), G()], [G(), G(1)]]
    hn = [[G(1), G(1)], [G(1), G(-1)]]
    xm = scale(add(identity, scale(x, -1)), F(1, 2))
    ua = add(kron(kron(p0, identity), identity), kron(kron(p1, x), identity))
    ub = add(kron(kron(scale(add(identity, x), F(1, 2)), identity), identity),
             kron(kron(xm, identity), x))
    uzb = add(kron(kron(p0, identity), identity), kron(kron(p1, identity), x))
    kab = add(eye(4), scale(kron(xm, xm), -2))
    control_k = blockdiag(eye(8), kron(identity, kab))
    hfull = kron(kron(hn, identity), identity)
    ordinary_ideal = blockdiag(mm(uzb, ua), scale(mm(uzb, mm(hfull, mm(ua, hfull))), F(1, 2)))
    cab = blockdiag(eye(4), kab)
    encoding = [[cab[row][c*4] for c in range(2)] for row in range(8)]
    ctrl_xa = blockdiag(eye(4), kron(x, identity))
    extra = mm(ctrl_xa, kron(kron(identity, identity), z))
    require(mm(extra, encoding) == encoding, "extra populated C-to-a correction stabilizes E")
    jideal = [[G(int(spin == cin and photon == cin)) for cin in range(2)]
              for spin, photon in product(range(2), repeat=2)]

    def response(r0, r1, nu):
        r0, r1 = G(r0), G(r1)
        sn = add(scale(identity, r0), scale(x, r1))
        eta = (r0*r0.conj()+r1*r1.conj()).r/2
        kappa = (r0.conj()*r1).r
        require(0 <= eta <= 1 and (r0*r0.conj()).r <= 1 and (r1*r1.conj()).r <= 1,
                "fixtures admit passive spin-dependent reflection amplitudes")
        require(mm(adj(sn), sn) == scale(add(scale(identity, eta), scale(x, kappa)), 2),
                "all complex phases enter the exact response Gram")
        require(nu*nu == 2*(eta-abs(kappa)), "fixture minimum singular value")
        jz = mm(kron(identity, sn), jideal)
        jx = scale(mm(kron(hn, identity), mm(jz, hn)), F(1, 2))
        require(scale(mm(adj(jz), jz), F(1, 2)) == scale(identity, eta)
                and scale(mm(adj(jx), jx), F(1, 2)) == scale(identity, eta),
                "both fresh-source effects are scalar on unknown spin/reference")
        inverse = None
        det = r0*r0-r1*r1
        if nu:
            inverse = scale([[r0/det, -r1/det], [-r1/det, r0/det]], nu)
            require(mm(inverse, sn) == scale(identity, nu), "uniform inverse amplitude")
            q = add(identity, scale(mm(adj(inverse), inverse), -1))
            require(q == adj(q) and q[0][0].i == q[1][1].i == 0
                    and q[0][0].r >= 0 and q[1][1].r >= 0
                    and (q[0][0]*q[1][1]-q[0][1]*q[1][0]).i == 0
                    and (q[0][0]*q[1][1]-q[0][1]*q[1][0]).r >= 0,
                    "local inverse is a contraction")
        else:
            require(det == 0, "singular boundary has zero uniform inverse weight")
        return sn, eta, kappa, inverse

    mixed_plus, mixed_minus = G(F(3, 5), F(4, 5)), G(F(5, 26), F(6, 13))
    mixed = ((mixed_plus+mixed_minus)/2, (mixed_plus-mixed_minus)/2, F(1, 2))
    fixtures = [((F(3, 5), F(1, 5), F(2, 5)), (F(4, 5), F(1, 5), F(3, 5))),
                ((F(3, 5), G(0, F(4, 5)), F(1)), mixed),
                (mixed, (mixed[1], mixed[0], mixed[2])),
                ((F(3, 5), F(3, 5), F()), (F(4, 5), F(1, 5), F(3, 5))),
                ((1, 1, F()), (F(3, 5), F(1, 5), F(2, 5))),
                ((0, 0, F()), (F(3, 5), F(1, 5), F(2, 5)))]
    raw_units = native_units = ordinary_units = inverse_units = extra_units = 0
    noncontractive_sources = singular_sources = zero_sources = singular_output_cases = 0
    wrong_filter_witness = None
    for a, b in fixtures:
        fa, eta_a, ka, da = response(*a)
        fb, eta_b, kb, db = response(*b)
        for spec, eta, kappa in ((a, eta_a, ka), (b, eta_b, kb)):
            noncontractive_sources += int(eta+abs(kappa) > 1)
            singular_sources += int(spec[2] == 0)
            zero_sources += int(eta == 0)
        filters = kron(kron(identity, fa), fb)
        require(mm(kron(identity, kab), filters) == mm(filters, kron(identity, kab)),
                "accepted filters commute with the central photon commutator")
        uan = mm(kron(kron(identity, fa), identity), ua)
        ubn = mm(kron(kron(identity, identity), fb), ub)
        ordered = blockdiag(mm(ubn, uan), mm(uan, ubn))
        compiled = mm(control_k, blockdiag(mm(ubn, uan), mm(ubn, uan)))
        require(ordered == compiled, "finite-contrast accepted raw compiler including order phases")
        fresh = [[ordered[row][c*8+s*4] for c, s in product(range(2), repeat=2)] for row in range(16)]
        fresh_compiled = [[compiled[row][c*8+s*4] for c, s in product(range(2), repeat=2)] for row in range(16)]
        raw_units += cp_equal(fresh, fresh_compiled)
        require(scale(mm(adj(fresh), fresh), F(1, 4)) == scale(eye(4), eta_a*eta_b),
                "full selected C/S/reference effect")
        ordinary = mm(kron(identity, filters), ordinary_ideal)
        le = mm(kron(identity, kron(fa, fb)), encoding)
        lminus = mm(kron(identity, kron(fa, mm(z, mm(fb, z)))), encoding)
        if a[2] == 0 or b[2] == 0:
            g = [le[4+ab][1] for ab in range(4)]
            require(g[0]*g[3]-g[1]*g[2] == 0,
                    "singular local source has a product C=1 photon output")
            singular_output_cases += 1
        for h in (1, -1):
            def branch(unitary):
                return [[sum((unitary[c*8+s*4+ab][cin*8]*h**s for s in range(2)), G())
                         for cin in range(2)] for c, ab in product(range(2), range(4))]
            native_raw = branch(ordered)
            native = native_raw if h == 1 else mm(kron(kron(identity, identity), x), native_raw)
            ordinary_raw = branch(ordinary)
            ordinary_corrected = ordinary_raw if h == 1 else mm(kron(kron(identity, identity), z), ordinary_raw)
            expected = le if h == 1 else lminus
            require(native == le and ordinary_corrected == expected, "all corrected factory amplitudes")
            native_units += cp_equal(native, le)
            ordinary_units += cp_equal(ordinary_corrected, expected)
            require(scale(mm(adj(native), native), F(1, 8)) == scale(identity, eta_a*eta_b/2)
                    and scale(mm(adj(ordinary_corrected), ordinary_corrected), F(1, 8)) == scale(identity, eta_a*eta_b/2),
                    "every flag has input-independent eta-product/2 effect")
            if h == -1:
                repaired = mm(extra, ordinary_corrected)
                require(repaired == le, "paid populated C-to-a gate removes the finite-contrast flag difference")
                extra_units += cp_equal(repaired, le)
            if da is not None and db is not None:
                native_filtered = mm(kron(identity, kron(da, db)), native)
                db_flag = db if h == 1 else mm(z, mm(db, z))
                ordinary_filtered = mm(kron(identity, kron(da, db_flag)), ordinary_corrected)
                ideal = scale(encoding, a[2]*b[2])
                require(native_filtered == ordinary_filtered == ideal, "same sufficient ideal inverse-filter weight")
                inverse_units += cp_equal(native_filtered, ideal)+cp_equal(ordinary_filtered, ideal)
                if h == -1:
                    wrong_filter_witness = wrong_filter_witness or cp_difference(
                        mm(kron(identity, kron(da, db)), ordinary_corrected), ideal)
    require(wrong_filter_witness is not None, "post-Z ordinary inverse cannot ignore its conjugated frame")
    require(noncontractive_sources == 1 and singular_sources == 3 and zero_sources == 1
            and singular_output_cases == 3,
            "retain joint-valid noncontractive, nonzero singular and zero-source fixtures")
    # Two bin-resolved lost completions with identical selected amplitudes.
    r0, r1, ell0, ell1 = F(3, 5), F(5, 13), F(4, 5), F(12, 13)
    jz = mm(kron(identity, add(scale(identity, r0), scale(x, r1))), jideal)
    losses = [[[G(ell0), G()], [G(), G(ell1)]], [[G(ell1), G()], [G(), G(ell0)]]]
    effect = scale(mm(adj(jz), jz), F(1, 2))
    for loss in losses:
        effect = add(effect, scale(mm(adj(loss), loss), F(1, 2)))
    require(effect == identity, "selected reflection plus binwise loss is complete")
    distinguished = [mm(p, loss) for loss in losses for p in (p0, p1)]
    for i, j, row, col in product(range(2), repeat=4):
        coherent = sum((loss[row][i]*loss[col][j].conj()/2 for loss in losses), G())
        tagged = sum((loss[row][i]*loss[col][j].conj()/2 for loss in distinguished), G())
        if i == j:
            require(coherent == tagged, "same lost populations for either bath completion")
        elif row == i and col == j:
            require(coherent == ell0*ell1 and tagged == 0, "accepted amplitudes do not fix lost coherence")
    return {"status": "passed", "source_pairs": len(fixtures), "raw_CSR_matrix_units": raw_units,
            "native_factory_CR_matrix_units": native_units, "ordinary_factory_CR_matrix_units": ordinary_units,
            "inverse_filter_CR_matrix_units": inverse_units, "extra_populated_CNOT_CR_matrix_units": extra_units,
            "joint_valid_noncontractive_sources": noncontractive_sources,
            "singular_sources_including_zero": singular_sources, "zero_sources": zero_sources,
            "singular_product_output_cases": singular_output_cases,
            "wrong_inverse_frame_CP_witness": wrong_filter_witness,
            "scope": "finite declared pure selected-source fixtures only; physical pulses, full timed baths, retained heralds and resource costs are not certified"}


def reversed_role_cleanup_guards():
    """Conditional four-mode carrier and full repeated phase-CZ ports.

    S is photon polarization, C its retained path, and a,b stationary.
    These ports are not supplied by the Wei fresh-emission isometry.
    """
    identity = eye(2)
    x = [[G(), G(1)], [G(1), G()]]
    z = [[G(1), G()], [G(), G(-1)]]
    hn = [[G(1), G(1)], [G(1), G(-1)]]
    hs = kron(hn, eye(4))  # actual H_S has the factor 1/sqrt(2)

    # Three-wire order S,a,b; native contacts are full arbitrary-input gates.
    def cnot(which):
        bit = 1 if which == "a" else 0
        out = zeros(8)
        for s, a, b in product(range(2), repeat=3):
            col = 4*s+2*a+b
            row = col ^ ((1 << bit) if s else 0)
            out[row][col] = G(1)
        return out

    ca, cb = cnot("a"), cnot("b")
    czb = [[G(((-1)**(((i >> 2) & 1)*(i & 1))) if i == j else 0)
            for j in range(8)] for i in range(8)]
    ua = ca
    ub = scale(mm(hs, mm(cb, hs)), F(1, 2))
    ordinary_cleanup = scale(mm(hs, mm(czb, hs)), F(1, 2))
    for gate in (ca, cb, czb, ub, ordinary_cleanup):
        require(mm(adj(gate), gate) == eye(8), "full contact gate is unitary")

    xm = scale(add(identity, scale(x, -1)), F(1, 2))
    k = add(eye(4), scale(kron(xm, xm), -2))
    f0 = [[G(int(i == 0))] for i in range(4)]
    f1 = mm(k, f0)
    require(f1 == [[G(F(1, 2))], [G(F(1, 2))],
                   [G(F(1, 2))], [G(F(-1, 2))]], "graph-state signs")
    encoding = zeros(8, 2)  # output C,a,b
    wanted = zeros(16, 2)   # output C,S,a,b, with S reset to zero
    fresh = zeros(16, 2)
    for c in range(2):
        fresh[8*c][c] = G(1)
        for ab in range(4):
            encoding[4*c+ab][c] = (f0 if c == 0 else f1)[ab][0]
            wanted[8*c+ab][c] = encoding[4*c+ab][c]
    require(mm(adj(wanted), wanted) == identity, "cleaned target is an isometry")

    # Native order convention: C=0 is B after A; C=1 is A after B.
    native_u = blockdiag(mm(ub, ua), mm(ua, ub))
    native_before = mm(native_u, fresh)
    native_after = mm(kron(identity, ub), native_before)
    require(native_after == wanted, "one extra B contact coherently cleans native S")

    # Literal CH-copy-CH-copy sequence. On C=0 both CHs are I.
    # On C=1 each CH is H_S, so their two factors give exactly 1/2.
    ordinary_u = blockdiag(mm(cb, ca), scale(mm(cb, mm(hs, mm(ca, hs))), F(1, 2)))
    ordinary_before = mm(ordinary_u, fresh)
    ordinary_after = mm(kron(identity, ordinary_cleanup), ordinary_before)
    require(ordinary_after == wanted, "one extra phase-CZ contact coherently cleans ordinary S")

    pre_units = final_units = filter_units = 0
    pplus = scale(add(identity, x), F(1, 2))
    retained_filter = kron(identity, kron(pplus, eye(4)))
    forward_wanted = scale(mm(kron(identity, hs), wanted), F(1, 2))
    for before, byproduct in ((native_before, kron(identity, x)),
                              (ordinary_before, kron(identity, z))):
        for sign in (1, -1):
            # S-X bra numerator has factor 1/sqrt(2) externally.
            branch_numerator = [[before[8*c+ab][cin]+sign*before[8*c+4+ab][cin]
                                 for cin in range(2)]
                                for c, ab in product(range(2), range(4))]
            target = encoding if sign == 1 else mm(kron(identity, byproduct), encoding)
            require(branch_numerator == target, "complete coherent pre-readout branch identity")
            pre_units += cp_equal(branch_numerator, target)
        forward = mm(retained_filter, before)
        require(forward == forward_wanted
                and mm(adj(forward), forward) == scale(identity, F(1, 2)),
                "both two-contact forward polarization branches retain C at half weight")
        filter_units += cp_equal(forward, forward_wanted)
        final_units += cp_equal(native_after if before is native_before else ordinary_after, wanted)
    require(native_after == ordinary_after, "both full coherent factories agree")

    # The two coherent resets act differently on nonblank input: their
    # equality above is the intended source endpoint, not a full-W compiler.
    require(ub != ordinary_cleanup, "do not identify the distinct cleanup gates")
    return {"status": "passed", "coherent_pre_readout_matrix_units": pre_units,
            "cleaned_C_reference_matrix_units": final_units,
            "full_unitary_contact_checks": 5,
            "retained_polarization_filter_C_reference_matrix_units": filter_units,
            "contact_counts": {"native": 3, "ordinary": 3},
            "scope": "conditional ideal four-mode path/polarization carrier with full repeated phase-CZ contacts: both source endpoints clean S coherently in three contacts, and both have a retained half-weight plus-polarization branch after two. These are not Wei fresh-emission ports; no retained-herald, physical loss/route/clock, general obstruction or all-input W certificate"}


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
            "encoding_injection_rollback": injection_rollback_guards(target_factory, kab),
            "balanced_source_factories": balanced_source_factory_guards(),
            "reversed_role_coherent_cleanup": reversed_role_cleanup_guards(),
            "scope": "exact finite fresh-resource/key/relative-phase compiler, native and ordinary local-CH factories, and a nonblank-extension counterexample; the supplied joint CCZ and local matter controls are distinct priced ports. All-angle identities, privacy/security, state-dependent source/loss/clock maps and actual hardware comparisons remain analytic or unprovided. No prior, resource optimum or physical advantage certificate."}

if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True))
