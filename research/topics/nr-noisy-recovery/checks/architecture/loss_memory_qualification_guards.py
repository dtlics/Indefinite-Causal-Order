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



def verify():
    return {"status": "passed", "arithmetic": "exact Gaussian rationals",
            "collective_relaxation": collective_guards(),
            "loss_only_calibration": calibration_and_model_guards(),
            "retained_control_and_paid_parity": retained_and_parity_guards(),
            "actual_history_boundary": history_guards(),
            "dualrail_projector_routes": dualrail_projector_route_guards(),
            "scope": "Finite full-input/reference channels, flags and model-boundary ingredients for a declared loss-only family. Universal decoder/norm/concentration proofs remain analytic; unique survivor vacuum, bath preparation, selectors, protected checks, mode/phase controls, active excitation, rejects and physical clocks are premises. No full instrument, conditional-fidelity frontier, arbitrary-code or hardware advantage certificate. Separate dual-rail fixtures use declared common-success four-mode physical loss slots and paid independent Pauli seeds; seed-index products are not distinct nonzero physical records."}


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True))
