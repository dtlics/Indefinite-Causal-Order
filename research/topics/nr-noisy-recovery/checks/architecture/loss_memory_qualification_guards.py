"""Exact finite loss-memory qualification and paid ordinary-recovery guards.

The shared Gaussian engine supplies rational arithmetic and explicit require
checks, active with or without Python optimization. Import is quiet and no
explicit file I/O occurs; caller -B or its existing bytecode flag also keeps
module loading cache-free. Finite maps and counterexamples do
not prove the universal decoder/concentration bounds or supply physical
vacuum, selector, parity, mode-control, bath-reset or clock interfaces.
"""
from fractions import Fraction as F
from itertools import product
import json
import sys

sys.dont_write_bytecode = True
from retained_photon_serial import G, add, adj, blockdiag, cp_equal, eye, kron, mm, require, scale, zeros

O, I = G(), G(1)


def norm2(z):
    z = G(z)
    return z.r*z.r+z.i*z.i


def outer(v, w):
    return [[a*b.conj() for b in w] for a in v]


def column(a, j):
    return [row[j] for row in a]


def trace(a):
    return sum((a[i][i] for i in range(len(a))), G())


def matrix_sum(items):
    require(bool(items), "nonempty matrix sum")
    out = zeros(len(items[0]), len(items[0][0]))
    for item in items:
        out = add(out, item)
    return out


def channel(kraus, rho):
    return matrix_sum([mm(k, mm(rho, adj(k))) for k in kraus])


def require_tp(kraus):
    require(matrix_sum([mm(adj(k), k) for k in kraus]) == eye(len(kraus[0][0])),
            "complete Kraus effect")


def unit(n, i, j):
    out = zeros(n)
    out[i][j] = I
    return out


def score(kraus):
    return sum((norm2(trace(k)) for k in kraus), F())/4


def loss_channel(k, loss_rows):
    n = len(k)
    first = eye(n+1)
    for i, j in product(range(n), repeat=2):
        first[i+1][j+1] = G(k[i][j])
    out = [first]
    for row in loss_rows:
        loss = zeros(n+1)
        loss[0][1:] = [G(x) for x in row]
        out.append(loss)
    require_tp(out)
    return out


def collective(bright):
    require(bright[0] == 0 and sum((norm2(x) for x in bright), F()) == 1,
            "normalized one-excitation bright vector")
    return [add(eye(3), scale(outer(bright, bright), F(-2, 5))),
            scale(outer([I, O, O], bright), F(4, 5))]


def switched(a, b, sign):
    return [scale(add(mm(bj, ai), scale(mm(ai, bj), sign)), F(1, 2))
            for ai in a for bj in b]


def retained(a, b, rho):
    # The stacked Kraus numerator has an external amplitude 1/sqrt(2).
    out = []
    for ai in a:
        for bj in b:
            stack = mm(bj, ai)+mm(ai, bj)
            out.append(scale(mm(stack, mm(rho, adj(stack))), F(1, 2)))
    return matrix_sum(out)


def x_flag(full, sign):
    n = len(full)//2
    blocks = [[row[n*j:n*(j+1)] for row in full[n*i:n*(i+1)]]
              for i, j in product(range(2), repeat=2)]
    return scale(matrix_sum([blocks[0], blocks[3], scale(blocks[1], sign),
                             scale(blocks[2], sign)]), F(1, 2))


def parity_flags(kraus):
    p = eye(len(kraus[0]))
    for i in range(1, len(p)):
        p[i][i] = G(-1)
    plus = [scale(add(k, mm(p, mm(k, p))), F(1, 2)) for k in kraus]
    minus = [scale(add(k, scale(mm(p, mm(k, p)), -1)), F(1, 2)) for k in kraus]
    return plus, minus


def encoding(v):
    out = zeros(len(v)+1, 2)
    out[0][0] = I
    for i, value in enumerate(v, start=1):
        out[i][1] = G(value)
    return out


def mode_decoder(u):
    """Output-mode rotation and trace of the unused one-excitation modes."""
    require(len(u) in (1, 2) and sum((norm2(z) for z in u), F()) == 1,
            "normalized decoded mode")
    first = zeros(2, len(u)+1)
    first[0][0] = I
    first[1][1:] = [G(z).conj() for z in u]
    out = [first]
    if len(u) == 2:
        w = [-G(u[1]).conj(), G(u[0]).conj()]
        other = zeros(2, 3)
        other[0][1:] = [z.conj() for z in w]
        out.append(other)
    require_tp(out)
    return out


def logical_maps(kraus, v, u):
    enc, dec = encoding(v), mode_decoder(u)
    return [mm(d, mm(k, enc)) for k in kraus for d in dec]


def active_flags(kraus, v, u):
    keep, loss = parity_flags(kraus)
    x = [[O, I], [I, O]]
    return logical_maps(keep, v, u), [mm(x, k) for k in logical_maps(loss, v, u)]


def collective_guards():
    ground, bright, dark = [I, O, O], [O, I, O], [O, O, I]
    a = collective(bright)
    b = collective([O, G(F(3, 5)), G(F(4, 5))])
    require_tp(a)
    require_tp(b)
    plus, minus = switched(a, b, 1), switched(a, b, -1)
    require_tp(plus+minus)
    for i, j in product(range(3), repeat=2):
        require(trace(add(channel(plus, unit(3, i, j)), channel(minus, unit(3, i, j))))
                == G(i == j), "complete collective qutrit matrix unit")
    expected_minus = add(scale(outer(ground, ground), F(48, 625)**2),
                         scale(outer(bright, bright), F(24, 625)**2))
    vplus = [O, G(F(-96, 625)), G(F(93, 125))]
    for i, j in product(range(2), repeat=2):
        rho = outer((ground, dark)[i], (ground, dark)[j])
        expected = expected_minus if i == j == 1 else zeros(3)
        require(channel(minus, rho) == expected, "minus has only the excited input column")
        if i == j == 0:
            ep = outer(ground, ground)
        elif i == j == 1:
            ep = add(outer(vplus, vplus), scale(outer(ground, ground),
                     F(48, 625)**2+F(16, 25)**2))
        else:
            ep = outer(ground, vplus) if i == 0 else outer(vplus, ground)
        require(channel(plus, rho) == ep, "complete encoded plus/reference map")
    require(trace(expected_minus) == G(F(576, 78125)), "full minus acceptance mass")
    require(all(column(k, 0) == [O]*3 for k in minus), "all minus loss records kill vacuum")
    # The no-jump commutator is rank two on its active excitation plane.
    comm = minus[0]
    det = comm[1][1]*comm[2][2]-comm[1][2]*comm[2][1]
    require(det != 0 and comm[0] == [O]*3, "rank-two no-jump, not vacuum-code recovery")
    for z in (F(), F(1, 5), F(1, 2), F(4, 5), F(1)):
        require(z*(1-z)/4 <= F(1, 16), "no-jump branch squared singular-value bound")
    endpoint = []
    for bc in (collective(bright), collective(dark)):
        p, m = switched(a, bc, 1), switched(a, bc, -1)
        require(all(channel(m, outer(v, w)) == zeros(3)
                    for v, w in product((ground, dark), repeat=2)), "zero-flag endpoints")
        endpoint.append(channel(p, outer(dark, dark))[2][2])
    require(endpoint == [I, G(F(9, 25))], "same flag does not identify storage quality")
    for v, w in product((ground, dark), repeat=2):
        require(channel(a, outer(v, w)) == outer(v, w), "ordinary complete dark-code channel")
    return {"status": "passed", "qutrit_input_matrix_units": 9,
            "encoded_both_flag_matrix_units": 4, "ordinary_dark_code_units": 4,
            "zero_flag_different_memory_cases": 2,
            "minus_excited_input_mass": "576/78125", "active_commutator_rank": 2,
            "scope": "finite single-excitation collective-AD maps; no shared-bath or arbitrary-code inference"}


def calibration_and_model_guards():
    u = [[G(F(3, 5)), G(0, F(4, 5))], [G(0, F(4, 5)), G(F(3, 5))]]
    v = [[G(F(3, 5)), G(F(-4, 5))], [G(F(4, 5)), G(F(3, 5))]]
    require(mm(adj(u), u) == mm(adj(v), v) == eye(2), "known mode rotations")
    k = mm(u, mm([[G(F(4, 5)), O], [O, G(F(1, 5))]], v))
    rows = [[z*F(3, 5) for z in v[0]]]
    rows += [[z*a for z in v[1]] for a in (F(4, 5), F(2, 5), F(2, 5))]
    ks = loss_channel(k, rows)
    wrong_sign_seen = False
    for j, i in product(range(2), repeat=2):
        probe = [I, O, O]
        probe[j+1] = I
        rho = channel(ks, scale(outer(probe, probe), F(1, 2)))
        x, y = zeros(3), zeros(3)
        x[0][i+1] = x[i+1][0] = I
        y[0][i+1], y[i+1][0] = G(0, -1), G(0, 1)
        ex, ey = trace(mm(rho, x)), trace(mm(rho, y))
        require(ex.i == ey.i == 0 and G(ex.r, ey.r) == k[i][j], "K equals X plus iY")
        wrong_sign_seen |= G(ex.r, -ey.r) != k[i][j]
    require(wrong_sign_seen, "a complex fixture rejects the Schur-sign substitution")
    dec = logical_maps(ks, [G(F(3, 5)), G(F(-4, 5))], column(u, 0))
    require_tp(dec)
    for i, j in product(range(2), repeat=2):
        target = zeros(2)
        if i == j == 0:
            target[0][0] = I
        elif i == j == 1:
            target[0][0], target[1][1] = G(F(9, 25)), G(F(16, 25))
        else:
            target[i][j] = G(F(4, 5))
        require(channel(dec, unit(2, i, j)) == target, "full decoded logical/reference AD map")
    require(score(dec) == F(81, 100), "decoded entanglement fidelity")
    ad = loss_channel([[G(F(3, 5))]], [[F(4, 5)]])
    # These diagonal Kraus have coherence 3/5 but keep the excited population.
    dephase = [[[I, O], [O, G(F(3, 5))]], [[O, O], [O, G(F(4, 5))]]]
    require_tp(dephase)
    require(channel(ad, unit(2, 1, 0)) == channel(dephase, unit(2, 1, 0)),
            "same vacuum/excitation coherence")
    require(channel(ad, unit(2, 1, 1)) != channel(dephase, unit(2, 1, 1)),
            "survivor records change populations despite the same K")
    require(channel(ad, unit(2, 1, 1))[1][1] == G(F(9, 25))
            and channel(dephase, unit(2, 1, 1))[1][1] == I,
            "actual population model-boundary witness")
    require(score(ad) == F(16, 25) and score(dephase) == F(4, 5), "different complete memory scores")
    return {"status": "passed", "complex_Ramsey_entries": 4,
            "decoded_reference_matrix_units": 4, "survivor_record_counterexamples": 1,
            "scope": "loss-only calibration ingredients; means alone do not certify a pure survivor record"}


def retained_and_parity_guards():
    a = loss_channel([[G(F(3, 5))]], [[F(4, 5)]])
    p, m = switched(a, a, 1), switched(a, a, -1)
    x = [[O, I], [I, O]]
    recovered = p+[mm(x, k) for k in m]
    require_tp(recovered)
    s = F(9, 25)
    for i, j in product(range(2), repeat=2):
        rho = unit(2, i, j)
        full = retained(a, a, rho)
        require(trace(full) == G(i == j), "retained control trace")
        require(x_flag(full, 1) == channel(p, rho)
                and x_flag(full, -1) == channel(m, rho), "all retained X flags")
        if (i, j) == (0, 1):
            require(full == scale(outer([I, O, I, O], [O, G(s), O, G(s)]), F(1, 2)),
                    "retained-control cross operator includes only the survivor record")
        target = zeros(2)
        if i == j == 0:
            target[0][0] = I
        elif i == j == 1:
            target[0][0], target[1][1] = G(F(512, 625)), G(F(113, 625))
        else:
            target[i][j] = G(s)
        require(channel(recovered, rho) == target, "active retained-control populations")
    whole = [mm(b, aa) for aa in a for b in a]
    keep, loss = active_flags(whole, [I], [I])
    require_tp(keep+loss)
    for i, j in product(range(2), repeat=2):
        rho = unit(2, i, j)
        target = scale(rho, 1 if i == j else s)
        require(add(channel(keep, rho), channel(loss, rho)) == target, "ordinary all-outcome dephasing")
        require(trace(channel(loss, rho)) == G(1-s*s if i == j == 1 else 0), "loss syndrome weight")
    require(score(whole) == F(289, 625) and score(recovered) == F(297, 625),
            "passive AD is not an arbitrary retained-control decoder upper bound")
    require(score(keep+loss) == F(17, 25) == (1+s)/2, "paid ordinary parity score")
    aa = loss_channel([[G(F(3, 5)), O], [O, G(F(4, 5))]], [[F(4, 5), 0], [0, F(3, 5)]])
    bb = loss_channel([[O, G(F(5, 13))], [G(F(12, 13)), O]], [[F(5, 13), 0], [0, F(12, 13)]])
    pp, qq = mm(bb[0], aa[0]), mm(aa[0], bb[0])
    require(pp != qq, "genuinely noncommuting two-mode contractions")
    stacked = scale(add(mm(adj(pp), pp), mm(adj(qq), qq)), F(1, 2))
    require(stacked == [[I, O, O], [O, G(F(72, 169)), O], [O, O, G(F(25, 338))]],
            "stacked squared singular-value normalization")
    plus, minus = switched(aa, bb, 1), switched(aa, bb, -1)
    for i, j in product(range(3), repeat=2):
        rho, full = unit(3, i, j), retained(aa, bb, unit(3, i, j))
        require(trace(full) == G(i == j) and x_flag(full, 1) == channel(plus, rho)
                and x_flag(full, -1) == channel(minus, rho), "full qutrit/control/reference instrument")
        if i == 0 and j:
            require(full == scale(outer([I, O, O, I, O, O], column(pp, j)+column(qq, j)), F(1, 2)),
                    "qutrit retained-control survivor cross map")
    amplitudes = ((F(36, 65), F(4, 13)), (F(48, 65), F(3, 13)))
    for ks, ss in zip(([mm(b, a) for a in aa for b in bb],
                       [mm(a, b) for a in aa for b in bb]), amplitudes):
        for mode, amplitude in enumerate(ss):
            v, u = ([I, O] if mode == 0 else [O, I]), ([O, I] if mode == 0 else [I, O])
            kp, km = active_flags(ks, v, u)
            require_tp(kp+km)
            for i, j in product(range(2), repeat=2):
                rho = unit(2, i, j)
                require(add(channel(kp, rho), channel(km, rho)) == scale(rho, 1 if i == j else amplitude),
                        "both orders/modes give the full corrected dephasing channel")
                require(trace(channel(km, rho)) == G(1-amplitude*amplitude if i == j == 1 else 0),
                        "both orders/modes retain the complete loss flag")
    require(F(48, 65)**2 >= F(72, 169) and F(4, 13)**2 >= F(25, 338), "best-word squared comparison")
    # Approximate collection: uncollected survivor mass cannot be called a repaired loss.
    uniform = loss_channel([[G(F(3, 5)), O], [O, G(F(3, 5))]], [[F(4, 5), 0], [0, F(4, 5)]])
    estimate = scale([[G(F(12, 13)), G(F(-5, 13))],
                      [G(F(5, 13)), G(F(12, 13))]], F(3, 5))
    defect = add(estimate, scale([[G(F(3, 5)), O], [O, G(F(3, 5))]], -1))
    require(mm(adj(defect), defect) == scale(eye(2), F(18, 325))
            and F(18, 325) <= F(1, 4)**2,
            "actual empirical operator-norm allowance, not entrywise advice")
    kp, km = active_flags(uniform, [I, O], [G(F(12, 13)), G(F(5, 13))])
    excited = add(channel(kp, unit(2, 1, 1)), channel(km, unit(2, 1, 1)))
    require(excited[1][1] == G(F(160, 169)) and excited[0][0] == G(F(9, 169)),
            "empirical output-mode mismatch leaves a real population penalty")
    require(score(kp+km) == F(2581, 3380)
            and F(4, 5)-score(kp+km) <= F(1, 4)+F(1, 4)**2/4,
            "finite calibrated-mode regret ingredient")
    return {"status": "passed", "scalar_retained_reference_units": 4,
            "scalar_ordinary_corrected_units": 4, "qutrit_retained_reference_units": 9,
            "ordinary_order_mode_reference_units": 16, "empirical_mode_population_cases": 1,
            "passive_AD_score": "289/625", "retained_control_recovery_score": "297/625",
            "paid_parity_score": "17/25", "scope": "finite all-launch recovery ingredients, not a postselection frontier or a universal decoder proof"}


def history_guards():
    # System,bath basis 00,01,10,11. The intermediate bath record is reused.
    u = eye(4)
    u[1][1], u[1][2], u[2][1], u[2][2] = G(F(3, 5)), G(F(4, 5)), G(F(-4, 5)), G(F(3, 5))
    b = eye(4)
    b[1][1] = G(-1)
    require(mm(adj(u), u) == eye(4) and mm(adj(b), b) == eye(4), "shared-bath word unitaries")

    def slice_bath(word):
        return [[[word[2*i+e][2*j] for j in range(2)] for i in range(2)] for e in range(2)]

    left, right = slice_bath(mm(b, u)), slice_bath(mm(u, b))
    require_tp(left)
    require_tp(right)
    require(left[0] == right[0] == [[I, O], [O, G(F(3, 5))]]
            and left[1] == scale(right[1], -1), "same survivor, opposite loss-history records")
    identity_port = slice_bath(b)
    fresh_a = slice_bath(u)
    require(identity_port == [eye(2), zeros(2)], "isolated second reduced port is identity")
    parity = [[I, O], [O, G(-1)]]
    mismatch = False
    for i, j in product(range(2), repeat=2):
        rho = unit(2, i, j)
        actual = matrix_sum([scale(mm(l+r, mm(rho, adj(l+r))), F(1, 2))
                             for l, r in zip(left, right)])
        pcs = matrix_sum([scale(mm(k+mm(parity, mm(k, parity)),
                                   mm(rho, adj(k+mm(parity, mm(k, parity))))), F(1, 2))
                          for k in right])
        require(actual == pcs, "actual history instrument agrees with paid parity in this fixture")
        fresh = retained(fresh_a, identity_port, rho)
        mismatch |= actual != fresh
        require(trace(actual) == G(i == j), "shared-history full-input trace")
    require(mismatch, "reduced fresh channels do not identify the coherent shared-history map")
    twice, undo = slice_bath(mm(u, u)), slice_bath(mm(adj(u), u))
    require(twice[0][1][1] == G(F(-7, 25)) and undo == [eye(2), zeros(2)],
            "reabsorption changes the complete-word survival amplitude")
    require(twice[0][1][1] != G(F(9, 25)), "do not multiply reduced survival amplitudes through a reused bath")
    return {"status": "passed", "shared_history_reference_units": 4,
            "distinct_reduced_slot_completions": 1, "reabsorption_word_cases": 1,
            "scope": "finite actual-word dilations; no reduced-map-to-selector or general timing inference"}


def dualrail_projector_route_guards():
    identity = eye(2)
    x = [[G(), G(1)], [G(1), G()]]
    y = [[G(), G(0, -1)], [G(0, 1), G()]]
    z = [[G(1), G()], [G(), G(-1)]]
    p0, p1 = [[G(1), G()], [G(), G()]], [[G(), G()], [G(), G(1)]]
    pp = scale(add(identity, x), F(1, 2))
    hn = [[G(1), G(1)], [G(1), G(-1)]]
    swap = [[G(int(row == (2*(col & 1)+(col >> 1)))) for col in range(4)] for row in range(4)]
    require(mm(adj(swap), swap) == eye(4), "four-mode known SWAP is unitary")
    initial = kron([[G(1)], [G(1)]], identity)  # actual initial C-plus factor 1/sqrt2

    def physical_slot(k, loss_root):
        require(mm(adj(k), k) == add(identity, scale(mm(adj(loss_root), loss_root), -1)),
                "full loss root completes the contraction")
        operators = [blockdiag([[G(1)]], kron(identity, k))]
        for c, row in product(range(2), repeat=2):
            jump = zeros(5)
            for d in range(2):
                jump[0][1+2*c+d] = loss_root[row][d]
            operators.append(jump)
        effect = zeros(5)
        for op in operators:
            effect = add(effect, mm(adj(op), op))
        require(effect == eye(5), "single physical vacuum full slot is trace preserving")
        return operators

    # Separate surviving-control SWITCH: numerator factors 1/sqrt2.
    a, b = p0, pp
    qa, qb = p1, scale(add(identity, scale(x, -1)), F(1, 2))
    ba, ab = mm(b, a), mm(a, b)
    n = ba+ab
    ja = [[[row[d] for d in range(2)], mm([row], b)[0]] for row in qa]
    jb = [[mm([row], a)[0], [row[d] for d in range(2)]] for row in qb]
    effect = scale(mm(adj(n), n), F(1, 2))
    require(effect == [[G(F(3, 8)), G(F(1, 8))], [G(F(1, 8)), G(F(1, 8))]],
            "full projector SWITCH survivor effect")
    for j in ja+jb:
        effect = add(effect, scale(mm(adj(j), j), F(1, 2)))
    require(effect == identity, "full separate-control instrument including all jump records")
    sep_initial = zeros(6, 2)
    for c, d in product(range(2), repeat=2):
        sep_initial[3*c+1+d][d] = G(1)

    def separate_slot(k, root):
        out = [blockdiag([[G(1)]], k)]
        for row in root:
            jump = zeros(3)
            jump[0][1:] = row[:]
            out.append(jump)
        return out

    separate_units = 0
    for ai, ao in enumerate(separate_slot(a, qa)):
        for bi, bo in enumerate(separate_slot(b, qb)):
            literal = mm(blockdiag(mm(bo, ao), mm(ao, bo)), sep_initial)
            expected = zeros(6, 2)
            if ai == bi == 0:
                for c, d in product(range(2), repeat=2):
                    expected[3*c+1+d] = n[2*c+d][:]
            elif bi == 0:
                for c in range(2):
                    expected[3*c] = ja[ai-1][c][:]
            elif ai == 0:
                for c in range(2):
                    expected[3*c] = jb[bi-1][c][:]
            require(literal == expected, "literal full SWITCH Kraus map with vacuum/control records")
            separate_units += cp_equal(literal, expected)
    minus = scale(add(ba, scale(ab, -1)), F(1, 2))
    plus = scale(add(ba, ab), F(1, 2))
    require(minus == scale([[G(), G(-1)], [G(1), G()]], F(1, 4))
            and mm(adj(minus), minus) == scale(identity, F(1, 16)),
            "minus survivor has a corrected identity weight one sixteenth")
    loss_minus = zeros(2)
    for row in qa:
        ell = scale(add([row], scale(mm([row], b), -1)), F(1, 2))
        loss_minus = add(loss_minus, mm(adj(ell), ell))
    for row in qb:
        ell = scale(add(mm([row], a), scale([row], -1)), F(1, 2))
        loss_minus = add(loss_minus, mm(adj(ell), ell))
    require(loss_minus == [[G(F(1, 16)), G(F(-1, 16))],
                           [G(F(-1, 16)), G(F(3, 16))]],
            "minus control flag also includes vacuum and is not a survival herald")
    # General projector Gram and both bounded exact-yield polynomials.
    projector_cases = 0
    for c, s in ((F(), F(1)), (F(1), F()), (F(3, 5), F(4, 5)), (F(5, 13), F(12, 13))):
        pb = [[G(c*c), G(c*s)], [G(c*s), G(s*s)]]
        nn = mm(pb, p0)+mm(p0, pb)
        gram = scale(mm(adj(nn), nn), F(1, 2))
        require(gram == scale(add(p0, pb), c*c/2), "projector-only full survivor Gram")
        low, high = c*c*(1-c)/2, c*c*(1+c)/2
        require((gram[0][0]-low)*(gram[1][1]-low)-gram[0][1]*gram[1][0] == 0
                and gram[0][0]+gram[1][1] == low+high,
                "exact smallest survivor eigenvalue")
        require(F(2, 27)-low == (3*c-2)**2*(3*c+1)/54 and low <= F(2, 27),
                "two twenty-sevenths projector bound")
        require(c*c*(1-c*c)/4 <= F(1, 16), "projector measured-minus bound")
        projector_cases += 1
    nonhermitian_a, nonhermitian_b = [[G(), G(1)], [G(), G()]], [[G(), G()], [G(1), G()]]
    require(scale(add(mm(nonhermitian_b, nonhermitian_a), scale(mm(nonhermitian_a, nonhermitian_b), -1)), F(1, 2))
            == scale(z, F(-1, 2)), "one-sixteenth bound must not include all rank-one blocks")

    # Known-bright ordinary route: full single-carrier 5D loss completion.
    aa, bb = physical_slot(p0, p1), physical_slot(pp, qb)
    # The H numerators below are restricted to this known occupied path;
    # their two external 1/sqrt2 factors are cleared together. Vacuum is
    # never populated, as the loss-annihilation checks establish. The
    # padded vacuum entry is not a literal normalized control amplitude.
    swap5, hd5 = blockdiag([[G(1)]], swap), blockdiag([[G(1)]], kron(identity, hn))
    prepared = mm(hd5, mm(swap5, [[G(), G()]]+initial))
    for loss in aa[1:]:
        require(mm(loss, prepared) == zeros(5, 2), "prepared bright mode has no A loss")
    mid = mm(hd5, mm(aa[0], prepared))
    for loss in bb[1:]:
        require(mm(loss, mid) == zeros(5, 2), "aligned bright mode has no B loss")
    known = mm(swap5, mm(bb[0], mid))
    require(known == scale([[G(), G()]]+initial, 2), "known-bright route is full identity including control reset")
    known_units = cp_equal(scale(known, F(1, 2)), [[G(), G()]]+initial)

    # Axis-blind ordinary route: two INDEPENDENT Pauli seeds, all records.
    v = [[G(F(3, 5))], [G(0, F(4, 5))]]
    pv = mm(v, adj(v))
    qv = add(identity, scale(pv, -1))
    fixtures = [(p0, p1, pp, qb), (p0, p1, p1, p0), (pp, qb, qb, pp),
                (pv, qv, pp, qb), (nonhermitian_a, p0, nonhermitian_b, p1),
                (scale(p0, F(3, 5)), add(p1, scale(p0, F(4, 5))), pp, qb)]
    all_reference_units = seed_records = full_loss_records = 0
    for ka, ra, kb, rb in fixtures:
        aops, bops = physical_slot(ka, ra), physical_slot(kb, rb)
        ta = sum((mm(adj(ka), ka)[i][i].r for i in range(2)), F())
        tb = sum((mm(adj(kb), kb)[i][i].r for i in range(2)), F())
        target_weight = ta*tb/4
        survivors, losses = [], []
        for p, q in product((identity, x, y, z), repeat=2):
            before = mm(blockdiag([[G(1)]], kron(identity, p)), mm(swap5, [[G(), G()]]+initial))
            q5 = blockdiag([[G(1)]], kron(identity, q))
            for ai, ao in enumerate(aops):
                for bi, bo in enumerate(bops):
                    output = mm(swap5, mm(bo, mm(q5, mm(ao, before))))
                    if ai == bi == 0:
                        xi = mm(kb, mm(q, mm(ka, mm(p, [[G(1)], [G(1)]]))))
                        require(output == [[G(), G()]]+kron(xi, identity),
                                "every retained seed flag factors independent junk C and unknown D/R")
                        survivors.append(output[1:])
                        seed_records += 1
                    else:
                        require(all(value == 0 for row in output[1:] for value in row),
                                "rejects lose the entire single carrier, including C")
                        losses.append(output[0])
                        full_loss_records += 1
        for i, j, row, col in product(range(2), repeat=4):
            actual = sum((op[2*c+row][i]*op[2*c+col][j].conj()/32
                          for op in survivors for c in range(2)), G())
            require(actual == target_weight*int(row == i and col == j),
                    "axis-blind all-launch retained D/reference map")
        for i, j in product(range(2), repeat=2):
            rejected = sum((bra[i]*bra[j].conj()/32 for bra in losses), G())
            require(rejected == (1-target_weight)*int(i == j),
                    "all reject records sum to input-independent single-carrier erasure")
            all_reference_units += 1
    # The loss count includes zero/nonminimal seed x Kraus-index products,
    # not that many distinct nonzero physical outcomes or readouts.
    # Same random seed is not the independently-twirled baseline.
    same_seed = F()
    for p in (identity, x, y, z):
        vec = mm(p1, mm(p, mm(p0, mm(p, [[G(1)], [G()]]))))
        same_seed += sum((n2[0]*n2[0].conj()).r for n2 in vec)/4
    require(same_seed == 0, "reusing a single Pauli seed can destroy the guarantee")
    return {"status": "passed", "projector_cases": projector_cases,
            "separate_control_full_instrument_reference_matrix_units": separate_units,
            "known_bright_reference_matrix_units": known_units,
            "twirled_filter_pairs": len(fixtures), "retained_seed_records": seed_records,
            "loss_seed_kraus_index_products": full_loss_records,
            "twirled_reference_matrix_units": all_reference_units,
            "scope": "declared common-success four-mode loss slots and supplied calibrated optical controls only; full actual router/clock/bath matching, retained survival heralds, physical costs and universal loss-memory claims are not certified"}



def multiple_survivor_collection_guards():
    def unit(d,i,j):
        a=zeros(d); a[i][j]=G(1); return a

    def trace(a): return sum((a[i][i] for i in range(len(a))),G())
    def ch(ks,rho):
        out=zeros(len(ks[0]))
        for k in ks: out=add(out,mm(k,mm(rho,adj(k))))
        return out

    def tp(ks):
        out=zeros(len(ks[0][0]))
        for k in ks: out=add(out,mm(adj(k),k))
        require(out==eye(len(out)),'channel TP')

    def column(a,j): return [[row[j]] for row in a]

    def embed0():
        return [[G(1),G()],[G(),G(1)],[G(),G()]]


    def source(a,b,ra,rb,r):
        require(a*a+ra*ra==b*b+rb*rb==1,'rational source norm')
        k0=[[G(1),G(),G()],[G(),G(a),G()],[G(),G(),G(b)]]
        k1=zeros(3); k1[0][1],k1[2][1]=G(ra*F(3,5)),G(ra*F(4,5))
        k2=zeros(3); k2[0][2],k2[1][2]=G(rb*F(4,5)),G(0,rb*F(3,5))
        ks=[mm(r,k) for k in (k0,k1,k2)]; tp(ks)
        require(column(ks[0],0)==[[G(1)],[G()],[G()]] and
                all(column(k,0)==zeros(3,1) for k in ks[1:]),'same pure vacuum record')
        require(ks[0][0][1]==ks[0][0][2]==0,'vacuum e0 orthogonality')
        return ks


    def run_collection_replay():
        rot0=[[G(1),G(),G()],[G(),G(F(3,5)),G(0,F(4,5))],
              [G(),G(0,F(4,5)),G(F(3,5))]]
        rot1=[[G(1),G(),G()],[G(),G(F(5,13)),G(F(-12,13))],
              [G(),G(F(12,13)),G(F(5,13))]]
        require(mm(adj(rot0),rot0)==mm(adj(rot1),rot1)==eye(3),'mode rotations')
        hist=[source(F(3,5),F(4,5),F(4,5),F(3,5),rot0),
              source(F(4,5),F(3,5),F(3,5),F(4,5),rot1)]
        # Output occupancy/qubit convention: [vac, t=01, other=10].
        embedding=[[G(1),G(),G()],[G(),G(1),G()],[G(),G(),G(1)],[G(),G(),G()]]
        cnot=eye(4); cnot[2][2]=cnot[3][3]=G(); cnot[3][2]=cnot[2][3]=G(1)
        require(mm(adj(cnot),cnot)==eye(4),'physical control-other CNOT-target')
        dump0=[[G(1),G(),G(),G()],[G(),G(1),G(),G()]]
        dump1=[[G(),G(),G(1),G()],[G(),G(),G(),G(1)]]
        compressor=[mm(d,mm(cnot,embedding)) for d in (dump0,dump1)]
        require(compressor==[[[G(1),G(),G()],[G(),G(1),G()]],
                             [[G(),G(),G()],[G(),G(),G(1)]]],'literal CNOT and discard Kraus')
        tp(compressor)
        z=[[G(1),G(),G()],[G(),G(-1),G()],[G(),G(),G(-1)]]
        w=blockdiag(eye(3),z)
        plus_input=eye(3)+eye(3) # stacked numerator, external 1/sqrt2
        x=[[G(),G(1)],[G(1),G()]]
        encoder=embed0()
        instrument_units=phase_entries=echo_fine=0
        naive_bias=False
        scores=[]
        for h,(ks,r) in enumerate(zip(hist,(rot0,rot1))):
            a=(F(3,5),F(4,5))[h]
            ps=sum(((mm(adj(k),k))[1][1].r for k in ks),F())
            require(ps==1,'encoded input norm')
            even=[scale(add(k,mm(z,mm(k,z))),F(1,2)) for k in ks]
            odd=[scale(add(k,scale(mm(z,mm(k,z)),-1)),F(1,2)) for k in ks]
            for sign,expected in ((1,even),(-1,odd)):
                row=[[G(int(i==j)) for j in range(3)]+[G(sign*int(i==j)) for j in range(3)] for i in range(3)]
                for k,e in zip(ks,expected):
                    literal=scale(mm(row,mm(w,mm(blockdiag(k,k),mm(w,plus_input)))),F(1,2))
                    require(literal==e,'literal helper W/channel/W/X-readout Kraus')
                    echo_fine+=1
            plus=[mm(d,mm(adj(r),mm(k,encoder))) for k in even for d in compressor]
            minus=[mm(x,mm(d,mm(adj(r),mm(k,encoder)))) for k in odd for d in compressor]
            tp(plus+minus)
            # Survivors in every bath record, not just e0, reach logical1.
            surv=sum((trace(ch(even,unit(3,1,1))).r,),F())
            loss=1-surv
            require(surv>a*a and loss>0,'nontrivial extra survivor and loss records')
            for i,j in product(range(2),repeat=2):
                rho=unit(2,i,j)
                gotplus,gotminus=ch(plus,rho),ch(minus,rho)
                want=zeros(2)
                if i==j==0: want[0][0]=G(1)
                elif i==j==1: want[1][1]=G(surv)
                else: want[i][j]=G(a)
                require(gotplus==want,'full-reference even flag')
                require(gotminus==scale(unit(2,1,1),loss*int(i==j==1)),'full-reference actively excited odd flag')
                expected=unit(2,i,j) if i==j else scale(unit(2,i,j),a)
                require(add(gotplus,gotminus)==expected,'dephasing full-reference corrected output')
                instrument_units+=1
            score=F(1,2)*(1+a); scores.append(str(score))
            # Phase-cycling cancels Ejj coherence with no model assumption about it.
            for j,i in product((1,2),repeat=2):
                ex,ey=unit(3,0,i),scale(unit(3,0,i),G(0,-1))
                ex=add(ex,unit(3,i,0)); ey=add(ey,scale(unit(3,i,0),G(0,1)))
                means=[]
                for sign in (1,-1):
                    p=scale(add(add(unit(3,0,0),unit(3,j,j)),scale(add(unit(3,0,j),unit(3,j,0)),sign)),F(1,2))
                    out=ch(ks,p)
                    means.append((trace(mm(ex,out)),trace(mm(ey,out))))
                re=(means[0][0]-means[1][0])/2
                im=(means[0][1]-means[1][1])/2
                require(re.i==im.i==0 and G(re.r,im.r)==ks[0][i][j], 'phase-cycled K sign and normalization')
                naive_bias |= G(means[0][0].r,means[0][1].r)!=ks[0][i][j]
                phase_entries+=1
        require(naive_bias,'single positive-phase Ramsey means can be biased by Ejj coherence')
        # Full retained-control selector: common e0 fixes the cross map even when
        # hidden survivor/loss records interfere differently across histories.
        def selector(ka,kb,rho):
            out=zeros(6)
            for a,b in zip(ka,kb):
                stack=a+b
                out=add(out,scale(mm(stack,mm(rho,adj(stack))),F(1,2)))
            return out
        zero=[[G(1)],[G()],[G()]]
        c0=zero+zero
        psi=column(hist[0][0],1)+column(hist[1][0],1)
        retained_units=0
        for i,j in product(range(2),repeat=2):
            r=mm(encoder,mm(unit(2,i,j),adj(encoder)))
            actual=selector(hist[0],hist[1],r)
            if (i,j)==(0,0): require(actual==scale(mm(c0,adj(c0)),F(1,2)),'retained vacuum pure')
            if (i,j)==(1,0): require(actual==scale(mm(psi,adj(c0)),F(1,2)),'retained E10 uses only e0 survivor columns')
            if (i,j)==(0,1): require(actual==scale(mm(c0,adj(psi)),F(1,2)),'retained E01 conjugate orientation')
            require(trace(actual)==G(i==j),'retained full-input trace')
            retained_units+=1
        require(trace(mm(adj(psi),psi))/2==G(F(1,2)) and F(1,2)<F(16,25),'stacked norm/order comparison ingredient')
        # A bath-record unitary fixing e0 changes the coherent selector, while
        # leaving BOTH reduced channels and their K matrices unchanged.
        kb=hist[1]
        changed=[kb[0],add(scale(kb[1],F(3,5)),scale(kb[2],F(4,5))),
                 add(scale(kb[1],F(-4,5)),scale(kb[2],F(3,5)))]
        tp(changed)
        for i,j in product(range(3),repeat=2):
            require(ch(changed,unit(3,i,j))==ch(kb,unit(3,i,j)),'same reduced history channel')
        require(selector(hist[0],changed,unit(3,1,1))!=selector(hist[0],kb,unit(3,1,1)), 'full histories not inferred from reduced channels')
        require(selector(hist[0],changed,unit(3,1,0))==selector(hist[0],kb,unit(3,1,0)), 'cross coherence independent of nonvacuum record overlap')
        return {'status':'passed','literal_echo_fine_Kraus':echo_fine,'corrected_flag_reference_units':instrument_units,
                'phase_cycled_complex_entries':phase_entries,'retained_control_reference_units':retained_units,
                'ordinary_scores':scores,'naive_Ramsey_bias_counterexample':True,'hidden_history_overlap_counterexample':True,
                'scope':'finite vacuum-preserving multi-survivor fixtures and literal paid CNOT/parity ingredients; all-history decoder upper and statistical concentration are analytic; physical gates, bath matching, phase and mode access are premises'}

    return run_collection_replay()


def unequal_vacuum_record_boundary_guards():
    def unit(d, i, j):
        out = zeros(d)
        out[i][j] = G(1)
        return out


    def rectangular_blocks(a, b):
        out = zeros(len(a) + len(b), len(a[0]) + len(b[0]))
        for i, row in enumerate(a):
            for j, value in enumerate(row):
                out[i][j] = value
        for i, row in enumerate(b):
            for j, value in enumerate(row):
                out[len(a) + i][len(a[0]) + j] = value
        return out


    def channel(ks, rho, weight=F(1)):
        out = zeros(len(ks[0]))
        for k in ks:
            out = add(out, scale(mm(k, mm(rho, adj(k))), weight))
        return out


    def run_boundary_replay():
        # System/bath output basis is |l,e>, selector/system/bath is |c,l,e>.
        v0 = zeros(4, 2)
        v1 = zeros(4, 2)
        v0[0][0] = v0[3][1] = G(1)
        v1[1][0] = v1[2][1] = G(1)
        x = [[G(), G(1)], [G(1), G()]]
        z = [[G(1), G()], [G(), G(-1)]]
        require(mm(adj(v0), v0) == mm(adj(v1), v1) == eye(2), 'isometries')
        require(v1 == mm(kron(x, eye(2)), mm(v0, x)), 'joint controlled conjugation')
        # Block isometry on arbitrary selector/logical input, before preparing C+.
        native = rectangular_blocks(v0, v1)
        fixed = rectangular_blocks(v0, v0)
        pre = blockdiag(eye(2), x)
        post = blockdiag(eye(4), kron(x, eye(2)))
        ordinary = mm(post, mm(fixed, pre))
        require(ordinary == native, 'full joint selector/logical/bath equality')
        require(mm(fixed, pre) != native, 'missing second controlled-X is detected')
        # Prepared C+ column numerator; external squared normalization is 1/2.
        prep = eye(2) + eye(2)
        w = mm(native, prep)
        projections = []
        for e in range(2):
            p = zeros(4, 8)
            for c in range(2):
                for l in range(2):
                    p[2*c+l][4*c+2*l+e] = G(1)
            projections.append(mm(p, w))
        expected = [
            [[G(1), G()], [G(), G()], [G(), G()], [G(), G(1)]],
            [[G(), G()], [G(), G(1)], [G(1), G()], [G(), G()]],
        ]
        require(projections == expected, 'retained selector bath-resolved phases')
        full_units = 0
        for i in range(4):
            for j in range(4):
                rho = unit(4, i, j)
                actual = channel([kron(k, eye(2)) for k in projections], rho, F(1, 2))
                same = channel([kron(k, eye(2)) for k in expected], rho, F(1, 2))
                require(actual == same, 'all logical/reference retained units')
                full_units += 1
        corrected = []
        visible_units = 0
        for h in range(2):
            bra = [[G(1), G() , G((-1)**h), G()],
                   [G(), G(1), G(), G((-1)**h)]]
            maps = [mm(bra, k) for k in projections]
            target = [eye(2), eye(2)] if h == 0 else [z, scale(z, -1)]
            require(maps == target, 'visible fine-record phases')
            correction = eye(2) if h == 0 else z
            corrected.append([mm(correction, k) for k in maps])
            for i in range(4):
                for j in range(4):
                    rho = unit(4, i, j)
                    got = channel([kron(k, eye(2)) for k in corrected[h]], rho, F(1, 4))
                    require(got == scale(rho, F(1, 2)), 'per-visible-flag full-reference identity')
                    visible_units += 1
        # Each isolated word is dephasing; its ground/coherence transfer is zero.
        for v in (v0, v1):
            ks = []
            for e in range(2):
                p = zeros(2, 4)
                p[0][e] = p[1][2+e] = G(1)
                ks.append(mm(p, v))
            require(channel(ks, unit(2, 1, 0)) == zeros(2), 'individual word coherence transfer zero')
            require(channel(ks, unit(2, 0, 0)) == unit(2, 0, 0), 'individual word fixes vacuum')
        return {'joint_isometry_equal': True, 'retained_reference_matrix_units': full_units,
                'corrected_flag_reference_matrix_units': visible_units,
                'scope': 'Exact two-codeword boundary witness and paid controlled-conjugation compiler; no hardware port certificate.'}


    return run_boundary_replay()


def collective_deadline_guards():
    def unit(d, i, j):
        out = zeros(d)
        out[i][j] = G(1)
        return out


    def tr(a):
        return sum((a[i][i] for i in range(len(a))), G())


    def channel(weighted, rho):
        out = zeros(len(weighted[0][1]))
        for weight, k in weighted:
            out = add(out, scale(mm(k, mm(rho, adj(k))), weight))
        return out


    def weighted_tp(weighted, d):
        out = zeros(d)
        for weight, k in weighted:
            out = add(out, scale(mm(adj(k), k), weight))
        require(out == eye(d), 'declared channel trace preserving')


    def entanglement_fidelity(weighted, d):
        return sum((G(weight) * tr(k) * tr(k).conj() for weight, k in weighted), G()) / G(d*d)


    def bitop(site, up=False):
        out = zeros(16)
        for source in range(16):
            bit = (source >> (3-site)) & 1
            if bit != int(up):
                target = source ^ (1 << (3-site))
                out[target][source] = G(1)
        return out


    def singlet_and_hopping():
        u0 = zeros(16, 1)
        for index, value in {5:1, 6:-1, 9:-1, 10:1}.items():
            u0[index][0] = G(value)
        u1 = zeros(16, 1)
        for index, value in {3:2, 5:-1, 6:-1, 9:-1, 10:-1, 12:2}.items():
            u1[index][0] = G(value)
        require(mm(adj(u0), u0) == [[G(4)]] and mm(adj(u1), u1) == [[G(12)]]
                and mm(adj(u0), u1) == [[G()]], 'singlet Gram factors')
        p = add(scale(mm(u0, adj(u0)), F(1, 4)), scale(mm(u1, adj(u1)), F(1, 12)))
        require(p == adj(p) and mm(p, p) == p and tr(p) == G(2), 'rank-two singlet projector')
        lower = [bitop(i) for i in range(4)]
        jm = zeros(16)
        for a in lower:
            jm = add(jm, a)
        require(mm(jm, p) == mm(adj(jm), p) == zeros(16), 'both thermal collective jumps annihilate code')
        # Nominal S4 two-level projection, measured Table S1 values in cycles MHz.
        couplings = {(0,1):F(586,100), (1,2):F(589,100), (2,3):F(586,100),
                     (0,2):F(60,100), (1,3):F(60,100)}
        h = zeros(16)
        for (i,j), value in couplings.items():
            hop = add(mm(adj(lower[i]), lower[j]), mm(adj(lower[j]), lower[i]))
            h = add(h, scale(hop, value))
        require(h == adj(h), 'source spin-projected Hamiltonian Hermitian')
        leakage = mm(add(eye(16), scale(p,-1)), mm(h,p))
        dvec = zeros(16,1)
        for i in (3,5,6,9,10,12):
            dvec[i][0] = G(1)
        dicke = scale(mm(dvec, adj(dvec)), F(1,6))
        require(mm(p, dicke) == zeros(16), 'Dicke complement orthogonal to singlets')
        a,b,c = F(709,100), F(1761,100), F(1292,100)
        kappa2 = (b-c)**2/F(6) + (2*a-b-c)**2/F(18)
        require(kappa2 == F(277759,15000), 'exact source cut polynomial')
        require(mm(leakage, adj(leakage)) == scale(dicke,kappa2), 'full projected leakage Gram and norm')
        require(leakage != zeros(16), 'real hopping does not preserve simple DFS')
        # For every operator supported on P, each collective dissipator is zero.
        supported_units = 0
        for ui in (u0,u1):
            for uj in (u0,u1):
                # Nonzero scalar normalization factors do not affect annihilation;
                # these four operators span the normalized logical code algebra.
                rho = mm(ui,adj(uj))
                for jump in (jm,adj(jm)):
                    jj = mm(adj(jump),jump)
                    dissipator = add(mm(jump,mm(rho,adj(jump))),
                                     scale(add(mm(jj,rho),mm(rho,jj)), F(-1,2)))
                    require(dissipator == zeros(16), 'all supported-code basis operators dark')
                supported_units += 1
        return {'projected_code_operator_checks': supported_units,
                'nominal_hopping_leakage_norm_squared_cycles_MHz': str(kappa2),
                'scope':'Exact collective-noise code limit and nominal source-H projection; not a storage fidelity or full three-level simulation.'}


    def helper_channel_fixtures():
        ident = eye(2)
        z = [[G(1),G()],[G(),G(-1)]]
        fallback = [(F(1),kron(ident,unit(2,zbit,zbit))) for zbit in range(2)]
        weighted_tp(fallback,4)
        require(entanglement_fidelity(fallback,4) == G(F(1,2)), 'one-helper classical fallback Fe4')
        units = 0
        fixtures = 0
        for p in (F(0),F(1,20),F(1,2)):
            for r in (F(0),F(3,5),F(1)):
                for eta in (F(0),F(4,5),F(1)):
                    phase = G(F(3,5),F(4,5))
                    chi = G(eta)*phase
                    phasegate = [[G(1),G()],[G(),phase]]
                    base = [
                        (1-p, [[G(1),G()],[G(),G(r)]]),
                        ((1-p)*(1-r*r), unit(2,0,1)),
                        (p, [[G(r),G()],[G(),G(1)]]),
                        (p*(1-r*r), unit(2,1,0)),
                    ]
                    weighted = []
                    for w,k in base:
                        for v,frame in (((1+eta)/2,ident),((1-eta)/2,z)):
                            weighted.append((w*v,kron(ident,mm(phasegate,mm(frame,k)))))
                    weighted_tp(weighted,4)
                    expected = [
                        add(scale(unit(2,0,0),1-p*(1-r*r)),scale(unit(2,1,1),p*(1-r*r))),
                        scale(unit(2,0,1),G(r)*chi.conj()),
                        scale(unit(2,1,0),G(r)*chi),
                        add(scale(unit(2,0,0),(1-p)*(1-r*r)),scale(unit(2,1,1),p+(1-p)*r*r)),
                    ]
                    for i in range(4):
                        for j in range(4):
                            ai,bi,aj,bj=i//2,i%2,j//2,j%2
                            desired=kron(unit(2,ai,aj),expected[2*bi+bj])
                            require(channel(weighted,unit(4,i,j))==desired,'all two-logical operator images')
                            units+=1
                    formula=(G(1+r*r)+G(2*r)*G(chi.r))/G(4)
                    require(entanglement_fidelity(weighted,4)==formula,'thermal population-independent full Fe4')
                    fixtures+=1
        return {'declared_channel_fixtures':fixtures,'full_two_logical_matrix_units':units,
                'fallback_Fe4':'1/2', 'source_fit':False,
                'scope':'Parameterized CPTP family, not a source-inferred T2* or numerical device channel.'}


    def ground_heating_normalization():
        ground = unit(16,0,0)
        number = zeros(16)
        jm = zeros(16)
        local_up = []
        for i in range(4):
            down = bitop(i)
            jm = add(jm,down)
            number = add(number,mm(adj(down),down))
            local_up.append(adj(down))
        def dissipator(jump):
            jj=mm(adj(jump),jump)
            return add(mm(jump,mm(ground,adj(jump))),
                       scale(add(mm(jj,ground),mm(ground,jj)),F(-1,2)))
        require(tr(mm(number,dissipator(jm))) == G(), 'ground downward slope zero')
        require(tr(mm(number,dissipator(adj(jm)))) == G(4), 'collective upward slope factor four')
        require(all(tr(mm(number,dissipator(up))) == G(1) for up in local_up),
                'each local upward slope factor one')
        np,nq = F(27,500),F(1,20)
        low = 4*(np*2+nq*2)
        high = 4*(np*F(5,2)+nq*F(5,2))
        e3 = 4*(np*10+nq*4)
        require((low,high,e3)==(F(104,125),F(26,25),F(74,25)), 'literal nominal slope recipes')
        require(e3>high, 'rate-normalization ambiguity is experimentally distinguishable')
        return {'A1_nominal_slope_bracket_times_2pi_kHz':[str(low),str(high)],
                'E3_literal_slope_times_2pi_kHz':str(e3),
                'scope':'Ground-heating model-disambiguation recipes, not confidence intervals or logical-memory fidelity.'}


    def run_deadline_replay():
        return {'singlet_hopping':singlet_and_hopping(), 'helper_target_family':helper_channel_fixtures(),
                'ground_heating_normalization':ground_heating_normalization()}


    return run_deadline_replay()


def protected_helper_transfer_guards():
    I2 = eye(2)
    Z = [[G(1), G()], [G(), G(-1)]]
    X = [[G(), G(1)], [G(1), G()]]
    HN = [[G(1), G(1)], [G(1), G(-1)]]


    def unit(n, i, j):
        out = zeros(n)
        out[i][j] = G(1)
        return out


    def trace(a):
        return sum((a[i][i] for i in range(len(a))), G())


    def cp(terms, rho):
        out = zeros(len(terms[0][1]))
        for weight, op in terms:
            out = add(out, scale(mm(mm(op, rho), adj(op)), weight))
        return out


    def ref_terms(terms):
        return [(weight, kron(op, I2)) for weight, op in terms]


    def physical_fixture(omit_second_parity=False):
        # Data ordering q1,q2; target site q1, collective mode 3|10>/5+4i|01>/5.
        code = zeros(4, 2)
        code[0][0] = G(1)
        code[2][1] = G(F(3, 5))
        code[1][1] = G(0, F(4, 5))
        alignment = eye(4)
        alignment[2][2] = alignment[1][1] = G(F(3, 5))
        alignment[2][1] = alignment[1][2] = G(0, F(-4, 5))
        require(mm(adj(alignment), alignment) == eye(4), "physical alignment unitary")
        aligned = mm(alignment, code)
        expected = zeros(4, 2)
        expected[0][0] = expected[2][1] = G(1)
        require(aligned == expected, "complex collective-mode alignment")

        parity = eye(4)
        parity[1][1] = parity[2][2] = G(-1)
        require(mm(alignment, parity) == mm(parity, alignment), "vacuum/parity alignment")
        cz = []
        for bit in (1, 0):
            gate = eye(8)
            for c in range(2):
                for d in range(4):
                    gate[4*c+d][4*c+d] = G((-1)**(c*((d >> bit) & 1)))
            cz.append(gate)
        controlled_parity = cz[0] if omit_second_parity else mm(cz[1], cz[0])
        if not omit_second_parity:
            expected_parity = eye(8)
            for d in range(4):
                expected_parity[4+d][4+d] = parity[d][d]
            require(controlled_parity == expected_parity, "two literal controlled-Z parity gates")
        # C+ numerator; its omitted normalization is restored by CP weights below.
        source = code + code
        encoded = mm(kron(I2, alignment), mm(controlled_parity, source))
        return encoded


    def measure_row(a, other):
        # Unnormalized X bra on q1; q2 is traced by its Kraus index 'other'.
        row = zeros(2, 8)
        for c in range(2):
            for q1 in range(2):
                row[c][4*c+2*q1+other] = G((-1)**(a*q1))
        return row


    def raw_rows(encoded, a):
        return [mm(measure_row(a, other), encoded) for other in range(2)]


    def corrected_terms(encoded, a, r=F(1), kappa=F(1), wrong_order=False):
        za = I2 if a == 0 else Z
        correction = mm(HN, za) if wrong_order else mm(za, HN)
        out = []
        for raw in raw_rows(encoded, a):
            for b in range(2):
                wb = (1+r)/2 if b == 0 else (1-r)/2
                for c in range(2):
                    wc = (1+kappa)/2 if c == 0 else (1-kappa)/2
                    op = mm(I2 if c == 0 else Z,
                            mm(correction, mm(I2 if b == 0 else Z, raw)))
                    # Source, X bra, and correction contribute 1/(2 sqrt(2)).
                    out.append((wb*wc/8, op))
        return out


    def logical_terms(r, kappa):
        out = []
        for b in range(2):
            wb = (1+r)/2 if b == 0 else (1-r)/2
            for c in range(2):
                wc = (1+kappa)/2 if c == 0 else (1-kappa)/2
                out.append((wb*wc/2, mm(I2 if c == 0 else Z, I2 if b == 0 else X)))
        return out


    def reference_equal(terms, expected, label):
        left, right = ref_terms(terms), ref_terms(expected)
        count = 0
        for i in range(4):
            for j in range(4):
                rho = unit(4, i, j)
                require(cp(left, rho) == cp(right, rho), label + " full L/R matrix unit")
                count += 1
        return count


    def measurement_terms(a, r):
        correction = mm(I2 if a == 0 else Z, HN)
        out = []
        for other in range(2):
            row = measure_row(a, other)
            for b in range(2):
                wb = (1+r)/2 if b == 0 else (1-r)/2
                out.append((wb/4, mm(correction, mm(I2 if b == 0 else Z, row))))
        return out


    def effect(terms):
        out = zeros(len(terms[0][1][0]))
        for weight, op in terms:
            out = add(out, scale(mm(adj(op), op), weight))
        return out


    def trace_data(full):
        # Full output ordering C,D,R; retained output ordering C,R.
        out = zeros(4)
        for c in range(2):
            for r in range(2):
                for cc in range(2):
                    for rr in range(2):
                        out[2*c+r][2*cc+rr] = sum(
                            (full[2*(4*c+d)+r][2*(4*cc+d)+rr] for d in range(4)), G())
        return out


    def later_target_check(encoded):
        count = 0
        target_channels = []
        # Complete reset and complete computational dephasing on discarded data.
        target_channels.append([unit(4, 0, d) for d in range(4)])
        target_channels.append([unit(4, d, d) for d in range(4)])
        for ops in target_channels:
            require(sum_effect(ops) == eye(4), "later target channel is trace preserving")
            for a in range(2):
                pxnum = [[G(1), G((-1)**a)], [G((-1)**a), G(1)]]
                projected = mm(kron(I2, kron(pxnum, I2)), encoded)
                full = mm(kron(mm(I2 if a == 0 else Z, HN), eye(4)), projected)
                terms = [(F(1, 16), kron(mm(kron(I2, op), full), I2)) for op in ops]
                for i in range(4):
                    for j in range(4):
                        rho = unit(4, i, j)
                        require(trace_data(cp(terms, rho)) == scale(rho, F(1, 2)),
                                "later independent target channel cannot affect retained C/R")
                        count += 1
        return count


    def sum_effect(ops):
        out = zeros(len(ops[0][0]))
        for op in ops:
            out = add(out, mm(adj(op), op))
        return out


    def expected_failure(action, label):
        try:
            action()
        except ValueError:
            return 1
        raise ValueError("meaningful mutant was not rejected: " + label)


    def run_transfer_replay():
        encoded = physical_fixture()
        ideal_units = 0
        for a in range(2):
            rows = raw_rows(encoded, a)
            require(rows[0] == mm(HN, I2 if a == 0 else Z), "raw H Z^a numerator")
            require(rows[1] == zeros(2), "unused data mode is vacuum")
            ideal_units += reference_equal(corrected_terms(encoded, a), [(F(1, 2), I2)], "ideal")

        noisy_units = 0
        fe_checks = 0
        phi_vec = [[G(1)], [G()], [G()], [G(1)]]
        phi = scale(mm(phi_vec, adj(phi_vec)), F(1, 2))
        complex_vec = [[G(1)], [G()], [G()], [G(0, 1)]]
        complex_rho = scale(mm(complex_vec, adj(complex_vec)), F(1, 2))
        complex_checks = 0
        for r in (F(0), F(3, 5), F(1)):
            for kappa in (F(0), F(4, 5), F(1)):
                total_phi = zeros(4)
                for a in range(2):
                    actual = corrected_terms(encoded, a, r, kappa)
                    expected = logical_terms(r, kappa)
                    noisy_units += reference_equal(actual, expected, "timed helper noise")
                    actual_complex = cp(ref_terms(actual), complex_rho)
                    require(actual_complex == cp(ref_terms(expected), complex_rho), "complex entangled input")
                    require(trace(actual_complex) == G(F(1, 2)), "state independent flag weight")
                    complex_checks += 1
                    total_phi = add(total_phi, cp(ref_terms(actual), phi))
                require(trace(mm(phi, total_phi)) == G((1+r)*(1+kappa)/4), "entanglement fidelity formula")
                fe_checks += 1

        # Initial helper Z flips and raw pre-correction Z flips have the same axis.
        initial_units = 0
        for r in (F(0), F(3, 5), F(1)):
            for a in range(2):
                actual = []
                for b in range(2):
                    wb = (1+r)/2 if b == 0 else (1-r)/2
                    initial = mm(kron(I2 if b == 0 else Z, eye(4)), encoded)
                    actual.extend((weight*wb, op) for weight, op in corrected_terms(initial, a))
                initial_units += reference_equal(actual, logical_terms(r, F(1)), "initial helper Z becomes logical X")

        # Equality of effects implies equal probabilities for arbitrary C,D,R input.
        povm_units = 0
        effects = []
        for a in range(2):
            clean = measurement_terms(a, F(1))
            noisy = measurement_terms(a, F(0))
            expected_effect = scale(kron(I2, kron(
                [[G(1), G((-1)**a)], [G((-1)**a), G(1)]], I2)), F(1, 2))
            require(effect(clean) == expected_effect == effect(noisy), "same entire X POVM on arbitrary joint C/D")
            effects.append(expected_effect)
            for i in range(8):
                for j in range(8):
                    rho = unit(8, i, j)
                    require(trace(cp(clean, rho)) == trace(cp(noisy, rho)), "same-POVM CD matrix unit")
                    povm_units += 1
        require(add(effects[0], effects[1]) == eye(8), "complete joint measurement POVM")
        require(effects[0] != scale(eye(8), F(1, 2)), "arbitrary CD flags need not be fair")

        # Entanglement-breaking raw dephasing is literally measurement/preparation in X.
        x_measure_prepare = []
        for sign in (1, -1):
            projector = scale([[G(1), G(sign)], [G(sign), G(1)]], F(1, 2))
            x_measure_prepare.append((F(1, 2), projector))
        eb_units = reference_equal(corrected_terms(encoded, 0, F(0), F(1)), x_measure_prepare,
                                   "same-POVM channel is half Delta_X")
        require(cp(corrected_terms(encoded, 0, F(0), F(1)), unit(2, 0, 0)) != scale(unit(2, 0, 0), F(1, 2)),
                "same flags do not establish identity transfer")

        later_units = later_target_check(encoded)
        mutant_count = 0
        mutant_count += expected_failure(lambda: reference_equal(
            corrected_terms(physical_fixture(True), 0), [(F(1, 2), I2)], "omitted parity coupling"),
            "omitted second controlled parity contact")
        mutant_count += expected_failure(lambda: reference_equal(
            corrected_terms(encoded, 1, wrong_order=True), [(F(1, 2), I2)], "wrong correction order"),
            "interchanged H and flag-Z correction")
        mutant_count += expected_failure(lambda: reference_equal(
            corrected_terms(encoded, 0, F(3, 5), F(1)), logical_terms(F(1), F(3, 5)), "wrong noise axis"),
            "raw spectator noise mistaken for final storage noise")
        return {
            "status": "passed",
            "physical_data_qubits": 2,
            "complex_collective_mode": "3|10>/5+4i|01>/5",
            "ideal_reference_matrix_units": ideal_units,
            "timed_noise_reference_matrix_units": noisy_units,
            "initial_helper_noise_reference_matrix_units": initial_units,
            "same_povm_joint_CD_matrix_units": povm_units,
            "complex_entangled_input_flags": complex_checks,
            "entanglement_fidelity_fixtures": fe_checks,
            "entanglement_breaking_reference_matrix_units": eb_units,
            "later_target_CPTP_reference_matrix_units": later_units,
            "meaningful_mutants_rejected": mutant_count,
            "scope": "Literal paid parity/alignment/retained-helper X-instrument; exact finite replay, no hardware or novelty claim."
        }


    return run_transfer_replay()


def verify():
    return {"status": "passed", "arithmetic": "exact Gaussian rationals",
            "collective_relaxation": collective_guards(),
            "loss_only_calibration": calibration_and_model_guards(),
            "retained_control_and_paid_parity": retained_and_parity_guards(),
            "actual_history_boundary": history_guards(),
            "dualrail_projector_routes": dualrail_projector_route_guards(),
            "multiple_survivor_collection": multiple_survivor_collection_guards(),
            "unequal_vacuum_record_boundary": unequal_vacuum_record_boundary_guards(),
            "collective_deadline_guard": collective_deadline_guards(),
            "protected_helper_transfer": protected_helper_transfer_guards(),
            "scope": "Finite full-input/reference channels, flags and model-boundary ingredients for a declared loss-only family. Universal decoder/norm/concentration proofs remain analytic; unique survivor vacuum, bath preparation, selectors, protected checks, mode/phase controls, active excitation, rejects and physical clocks are premises. No full instrument, conditional-fidelity frontier, arbitrary-code or hardware advantage certificate. Separate dual-rail fixtures use declared common-success four-mode physical loss slots and paid independent Pauli seeds; seed-index products are not distinct nonzero physical records. Distinct multiple-survivor collection fixtures assume a common pure vacuum history record and final vacuum/one-excitation support, allow other survivor records and loss/survivor coherences, and add paid non-number-preserving CNOT collection, garbage reset and active recovery; they do not replace the earlier pure-loss AD/discard family. The unequal-vacuum-record witness and exact one-word controlled-conjugation closure are separate finite code-level guards, not a physical advantage or an assumed control port. Fixed-deadline collective fixtures distinguish an ideal singlet code from nominal projected-H leakage, explicitly declared GAD/phase channels and a ground-heating normalization test; no fitted device fidelity, unknown-state encoder or native selector is certified. A separate one-bit transfer fixture assumes pre-wait alignment, a protected helper and a spectator-safe target measurement instrument; equal POVM probabilities alone do not certify that transfer. Timed helper-noise axes and finite embedded mutants are checked, without supplying those ports."}


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True))
