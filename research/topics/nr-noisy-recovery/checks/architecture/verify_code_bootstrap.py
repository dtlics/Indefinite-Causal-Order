"""Exact finite guards for switch emulation, serial histories and code baselines.

Standard library and Gaussian rational arithmetic only. C6, coding and
all-dimension statistical statements remain analytic dependencies.
"""

from fractions import Fraction as F
from itertools import product
import json

if not __debug__:
    raise RuntimeError("Run code-bootstrap guards without -O.")


def require(test, message):
    if not test:
        raise RuntimeError(message)


class C:
    def __init__(self, real=0, imag=0):
        self.r, self.i = F(real), F(imag)

    @staticmethod
    def of(x):
        return x if isinstance(x, C) else C(x)

    def __add__(self, x):
        x = C.of(x)
        return C(self.r+x.r, self.i+x.i)

    __radd__ = __add__

    def __neg__(self):
        return C(-self.r, -self.i)

    def __sub__(self, x):
        return self + -C.of(x)

    def __rsub__(self, x):
        return C.of(x) + -self

    def __mul__(self, x):
        x = C.of(x)
        return C(self.r*x.r-self.i*x.i, self.r*x.i+self.i*x.r)

    __rmul__ = __mul__

    def __truediv__(self, x):
        x = C.of(x)
        z = x.r*x.r+x.i*x.i
        require(z > 0, "division domain")
        return self*x.conj()*F(1, z)

    def __eq__(self, x):
        x = C.of(x)
        return self.r == x.r and self.i == x.i

    def conj(self):
        return C(self.r, -self.i)

    def norm2(self):
        return self.r*self.r+self.i*self.i


def zero(d):
    return [[C() for _ in range(d)] for _ in range(d)]


def eye(d):
    return [[C(int(i == j)) for j in range(d)] for i in range(d)]


def adj(a):
    return [[a[j][i].conj() for j in range(len(a))] for i in range(len(a))]


def add(a, b, sign=1):
    return [[x+sign*y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def scale(a, x):
    return [[x*z for z in row] for row in a]


def mul(a, b):
    d = len(a)
    return [[sum((a[i][k]*b[k][j] for k in range(d)), C())
             for j in range(d)] for i in range(d)]


def trace(a):
    return sum((a[i][i] for i in range(len(a))), C())


def outer(v):
    return [[x*y.conj() for y in v] for x in v]


def tensor(a, b):
    return [[x*y for x in ar for y in br] for ar in a for br in b]


def choi(family):
    d = len(family[0][1])
    j = zero(d*d)
    for w, k in family:
        v = [x for row in k for x in row]
        for a in range(d*d):
            for b in range(d*d):
                j[a][b] += (w/d)*v[a]*v[b].conj()
    return j


def effect(family):
    d = len(family[0][1])
    result = zero(d)
    for w, k in family:
        result = add(result, scale(mul(adj(k), k), w))
    return result


def fidelity(family):
    d = len(family[0][1])
    return sum((w*trace(k).norm2()/(d*d) for w, k in family), F())


def apply(family, x):
    result = zero(len(x))
    for w, k in family:
        result = add(result, scale(mul(mul(k, x), adj(k)), w))
    return result


def frame(d):
    vectors = {2: [C(1), C(0, 2)], 3: [C(1), C(0, 2), C(2)],
               4: [C(1), C(0, 2), C(2), C(1, -1)]}
    v = vectors[d]
    norm = sum((x.norm2() for x in v), F())
    u = add(eye(d), scale(outer(v), F(2, norm)), -1)
    require(mul(adj(u), u) == eye(d), "rational complex Householder frame")
    return [outer([u[a][i] for a in range(d)]) for i in range(d)]


def power(projectors, t, k):
    d = len(projectors)
    r = (1-t)**k
    return [(r, eye(d))]+[(1-r, p) for p in projectors]


def switch_family(first, second):
    d = len(first[0][1])
    result = []
    for w, a in first:
        for v, b in second:
            ba, ab = mul(b, a), mul(a, b)
            k = zero(2*d)
            for i in range(d):
                for j in range(d):
                    k[i][j], k[d+i][d+j] = ba[i][j], ab[i][j]
            result.append((w*v, k))
    return result


def code_projector(d, k):
    return [[C(int(i == j and i < k)) for j in range(d)] for i in range(d)]


def cut(a, k):
    return [row[:k] for row in a[:k]]


def low_accepted(d, k, t):
    result = [(1-t, eye(k))]
    for a in range(k):
        for b in range(k):
            e = zero(k)
            e[a][b] = C(1)
            result.append((t/d, e))
    return result


def finite_histories(t, maximum, burst_threshold):
    leaves = []

    def visit(n, bursts, probability):
        if n == maximum or bursts == burst_threshold:
            leaves.append((n, bursts, probability))
        else:
            visit(n+1, bursts, probability*(1-t))
            visit(n+1, bursts+1, probability*t)

    visit(0, 0, F(1))
    return leaves


def compose(after, before):
    return [(w*v, mul(a, b)) for w, a in after for v, b in before]


def spin(v):
    x, y, z = map(C.of, v)
    return [[z, x-C(0, 1)*y], [x+C(0, 1)*y, -z]]


def cross(v, w):
    return [v[1]*w[2]-v[2]*w[1], v[2]*w[0]-v[0]*w[2],
            v[0]*w[1]-v[1]*w[0]]


def switch_flags(first, second):
    plus, minus = [], []
    for w, a in first:
        for v, b in second:
            ab, ba = mul(a, b), mul(b, a)
            plus.append((w*v/4, add(ab, ba)))
            minus.append((w*v/4, add(ab, ba, -1)))
    return plus, minus


def verify_framed_echo():
    axes = [([F(int(i == j)) for i in range(3)], F(1, 15))
            for j in range(3)]
    for i in range(3):
        for j in range(i+1, 3):
            for sign in (-1, 1):
                v = [F(0)]*3
                v[i], v[j] = F(1), F(sign)
                axes.append((v, F(2, 15)))
    require(sum((w for _, w in axes), F()) == 1, "nine-axis normalization")
    moments = 0
    for i in range(3):
        for j in range(3):
            second = sum((w*v[i]*v[j]/sum(x*x for x in v)
                          for v, w in axes), F())
            require(second == (F(1, 3) if i == j else 0),
                    "nine-axis second moment tensor")
            moments += 1
            for k in range(3):
                for l in range(3):
                    fourth = sum((w*v[i]*v[j]*v[k]*v[l]
                                  /sum(x*x for x in v)**2 for v, w in axes), F())
                    expected = F(int(i == j and k == l)
                                 + int(i == k and j == l)
                                 + int(i == l and j == k), 15)
                    require(fourth == expected, "nine-axis fourth moment tensor")
                    moments += 1
    paulis = [spin([F(int(i == j)) for i in range(3)]) for j in range(3)]
    for v, _ in axes:
        norm, f = sum(x*x for x in v), spin(v)
        require(mul(f, f) == scale(eye(2), norm), "known normalized involution")
        for p in paulis:
            image = scale(mul(mul(f, p), f), F(1, norm))
            require(any(image == scale(q, sign) for q in paulis for sign in (-1, 1)),
                    "each face-axis involution is a known target Clifford")
    ns = [[F(1), F(0), F(0)], [F(0), F(1), F(0)], [F(0), F(0), F(1)],
          [F(3, 5), F(4, 5), F(0)], [F(1, 3), F(2, 3), F(2, 3)],
          [F(2, 3), F(-2, 3), F(1, 3)]]
    echo_cases = native_cases = 0
    for n in ns:
        require(sum(x*x for x in n) == 1, "unknown rational unit axis")
        noise = spin(n)
        for t in (F(1, 10), F(1, 2), F(1)):
            a, b = 1-t/2, t/2
            accepted = zero(4)
            first_minus = F()
            for v, weight in axes:
                norm = sum(x*x for x in v)
                f, dot = spin(v), sum(n[i]*v[i] for i in range(3))
                conjugate = scale(mul(mul(f, noise), f), F(1, norm))
                parallel = scale(f, dot/norm)
                perpendicular = add(noise, parallel, -1)
                s2 = dot*dot/norm
                require(scale(add(noise, conjugate), F(1, 2)) == parallel
                        and scale(add(noise, conjugate, -1), F(1, 2)) == perpendicular,
                        "physical controlled-check Kraus branches")
                plus = [(a, eye(2)), (b, parallel)]
                minus = [(b, perpendicular)]
                unread = [(a, eye(2)), (b/2, noise), (b/2, conjugate)]
                require(add(choi(plus), choi(minus)) == choi(unread)
                        and add(effect(plus), effect(minus)) == eye(2),
                        "complete one-echo flagged Choi instrument")
                require(trace(choi(minus)) == b*(1-s2),
                        "first-minus probability is input independent")
                pp, pm = compose(plus, plus), compose(plus, minus)
                mp, mm = compose(minus, plus), compose(minus, minus)
                expected_pp = [(a*a+b*b*s2*s2, eye(2)), (2*a*b, parallel)]
                expected_pm = [(a*b, perpendicular),
                               (b*b, mul(parallel, perpendicular))]
                require(choi(pp) == choi(expected_pp)
                        and choi(pm) == choi(expected_pm) == choi(mp),
                        "complete repeated-echo nonaccepted branches")
                success = b*b*(1-s2)**2
                require(choi(mm) == scale(choi([(F(1), eye(2))]), success),
                        "double-minus identity channel on payload and reference")
                require(add(add(effect(pp), effect(pm)),
                            add(effect(mp), effect(mm))) == eye(2),
                        "all repeated-echo branches are TP together")
                accepted = add(accepted, scale(choi(mm), weight))
                first_minus += weight*b*(1-s2)
                echo_cases += 1
            ordinary_p = 2*t*t/15
            require(accepted == scale(choi([(F(1), eye(2))]), ordinary_p)
                    and first_minus == 2*b/3 and 1+first_minus == 1+t/3,
                    "nine-axis exact accepted map and early-stop mean cost")
            native_p = F()
            rotations = [[n[0], -n[2], n[1]], [n[2], n[1], -n[0]],
                         [-n[1], n[0], n[2]]]
            for rotated in rotations:
                c = sum(n[i]*rotated[i] for i in range(3))
                w = spin(cross(n, rotated))
                other = spin(rotated)
                first, second = [(a, eye(2)), (b, noise)], [(a, eye(2)), (b, other)]
                plus, minus = switch_flags(first, second)
                require(choi(minus) == choi([(b*b, w)])
                        and add(effect(plus), effect(minus)) == eye(2),
                        "native framed switch complete flags and commutator map")
                double_minus = compose(minus, minus)
                success = b**4*(1-c*c)**2
                require(choi(double_minus) == scale(choi([(F(1), eye(2))]), success),
                        "four-call native identity branch")
                native_p += success/3
                native_cases += 1
            require(2*b**4/3 <= native_p <= b**4
                    and ordinary_p > native_p and ordinary_p > t**4/16,
                    "ordinary success beats the actual native four-call upper bound")
    # The two-helper coherent Pauli twirl is an operator identity.
    twirl_cases = 0
    for i in range(2):
        for j in range(2):
            k = zero(2)
            k[i][j] = C(1)
            twirled = zero(2)
            for p in [eye(2)]+paulis:
                twirled = add(twirled, scale(mul(mul(adj(p), k), p), F(1, 4)))
            require(twirled == scale(eye(2), trace(k)/2),
                    "two-helper coherent Pauli twirl on a full operator basis")
            twirl_cases += 1
    return {"ordinary_echo_full_flag_cases": echo_cases,
            "native_framed_flag_cases": native_cases,
            "nine_axis_moment_coefficients": moments,
            "two_helper_twirl_operator_cases": twirl_cases}


def rect_mul(a, b):
    require(len(a[0]) == len(b), "rectangular product dimensions")
    return [[sum((a[i][k]*b[k][j] for k in range(len(b))), C())
             for j in range(len(b[0]))] for i in range(len(a))]


def rect_adj(a):
    return [[a[j][i].conj() for j in range(len(a))]
            for i in range(len(a[0]))]


def matrix_rank(a):
    a = [row[:] for row in a]
    row = 0
    for col in range(len(a[0])):
        pivot = next((i for i in range(row, len(a))
                      if a[i][col].norm2()), None)
        if pivot is None:
            continue
        a[row], a[pivot] = a[pivot], a[row]
        leading = a[row][col]
        a[row] = [x/leading for x in a[row]]
        for i in range(len(a)):
            if i != row:
                factor = a[i][col]
                a[i] = [x-factor*y for x, y in zip(a[i], a[row])]
        row += 1
        if row == len(a):
            break
    return row


def history_matrix(slot_matrices, amplitudes, gates):
    """Two mandatory slots, coherently retained rational history amplitudes."""
    result = []
    for h, amplitude in enumerate(amplitudes):
        order = (0, 1) if h % 2 == 0 else (1, 0)
        a = gates[h][0]
        for k, j in enumerate(order):
            a = mul(gates[h][k+1], mul(slot_matrices[j], a))
        result.extend(scale(a, amplitude))
    return result


def verify_history_rank():
    pattern_cases = trajectory_cases = sum_cases = recovery_cases = 0
    trace_rank_cases = saturation_cases = 0
    for d, amplitudes in ((2, [F(1)]), (3, [F(3, 5), F(4, 5)]),
                           (4, [F(1, 3), F(2, 3), F(2, 3)])):
        histories = len(amplitudes)
        require(sum((x*x for x in amplitudes), F()) == 1,
                "history amplitudes are normalized")
        ps = frame(d)
        shift = [[C(int(i == (j+1) % d)) for j in range(d)] for i in range(d)]
        phase = [[C((-1)**i if i == j else 0)
                  for j in range(d)] for i in range(d)]
        second = [mul(mul(shift, p), adj(shift)) for p in ps]
        slots = [ps, second]
        gates = [(eye(d), shift if h % 2 == 0 else phase, phase)
                 for h in range(histories)]
        clean = history_matrix([eye(d), eye(d)], amplitudes, gates)
        patterns = []
        for mask in product((False, True), repeat=2):
            family = []
            choices = [range(d) if flag else (None,) for flag in mask]
            for labels in product(*choices):
                matrices = [slots[j][labels[j]] if mask[j] else eye(d)
                            for j in range(2)]
                a = history_matrix(matrices, amplitudes, gates)
                family.append(a)
                if any(mask):
                    require(matrix_rank(a) <= histories,
                            "projector-containing history Kraus rank")
                    trajectory_cases += 1
            total = zero(d)
            for a in family:
                total = add(total, rect_mul(rect_adj(a), a))
            require(total == eye(d), "every fixed slot-type pattern is TP")
            patterns.append((mask, family))
            pattern_cases += 1
        for j in range(2):
            total = [[C() for _ in range(d)] for _ in range(histories*d)]
            for p in slots[j]:
                matrices = [eye(d), eye(d)]
                matrices[j] = p
                total = add(total, history_matrix(matrices, amplitudes, gates))
            require(total == clean, "aligned single-projector sum equals clean map")
            sum_cases += 1
        # Two explicit valid recoveries: discard the history, or postselect it.
        discard = []
        for h in range(histories):
            discard.append([[C(int(j == h*d+i)) for j in range(histories*d)]
                            for i in range(d)])
        accept = [[C(amplitudes[j//d] if j % d == i else 0)
                   for j in range(histories*d)] for i in range(d)]
        require(rect_mul(accept, rect_adj(accept)) == eye(d),
                "history projection is a contractive accepted recovery")
        for t in (F(1, 10), F(1, 2), F(1)):
            r, zeta = 1-t, min(F(histories, d), F(1))
            for recovery, tp in ((discard, True), ([accept], False)):
                family, clean_family = [], []
                for mask, paths in patterns:
                    weight = t**sum(mask)*r**(2-sum(mask))
                    for a in paths:
                        for b in recovery:
                            k = rect_mul(b, a)
                            family.append((weight, k))
                            if any(mask):
                                require(trace(k).norm2()
                                        <= histories*trace(mul(adj(k), k)).r,
                                        "rank-to-Bell trace inequality after recovery")
                                trace_rank_cases += 1
                            else:
                                clean_family.append((weight, k))
                p, q = trace(choi(family)).r, fidelity(family)
                p_clean = trace(choi(clean_family)).r
                require(p_clean <= min(p, r*r)
                        and q <= zeta*p+(1-zeta)*min(p, r*r),
                        "accepted history-rank p/q envelope")
                if tp:
                    require(effect(family) == eye(d) and p == 1
                            and q <= r*r+(1-r*r)*zeta,
                            "complete history-rank storage score")
                recovery_cases += 1
            require(fidelity(power(ps, t, 2)) == r*r+(1-r*r)/d,
                    "ordinary one-history full-space saturation")
            saturation_cases += 1
    # A retained clean/burst flag breaks the exact no-go's common-output sum.
    d, r, t = 2, F(1, 2), F(1, 2)
    clean = eye(d)+zero(d)
    error = [zero(d)+p for p in frame(d)]
    total = [[C() for _ in range(d)] for _ in range(2*d)]
    for a in error:
        total = add(total, a)
    require(total != clean, "exposed noise flags invalidate the clean/projector sum")
    accept_clean = [[C(int(j == i)) for j in range(2*d)] for i in range(d)]
    accepted = [(r, rect_mul(accept_clean, clean))]
    accepted += [(t, rect_mul(accept_clean, a)) for a in error]
    full_effect = scale(rect_mul(rect_adj(clean), clean), r)
    for a in error:
        full_effect = add(full_effect, scale(rect_mul(rect_adj(a), a), t))
    require(full_effect == eye(d)
            and choi(accepted) == scale(choi([(F(1), eye(d))]), r),
            "exposed clean/burst flag is a TP instrument with exact accepted identity")
    p, q, zeta = trace(choi(accepted)).r, fidelity(accepted), F(1, d)
    require(p == q == r and q == zeta*p+(1-zeta)*min(p, r),
            "flagged exact clean acceptance still respects the p/q envelope")
    require(matrix_rank(tensor(frame(2)[0], eye(2))) == 2,
            "protected workspace multiplies projector rank")
    return {"normalized_slot_patterns": pattern_cases,
            "error_trajectory_rank_cases": trajectory_cases,
            "single_projector_completeness_sums": sum_cases,
            "accepted_and_complete_score_cases": recovery_cases,
            "recovered_trace_rank_cases": trace_rank_cases,
            "ordinary_saturation_cases": saturation_cases,
            "exposed_flag_counterexamples": 1,
            "protected_workspace_rank_cases": 1}


def verify():
    compiler_cases = projection_cases = moment_cases = ledger_cases = 0
    truncation_cases = 0
    for d in (2, 3):
        ps = frame(d)
        for t, k, l in ((F(1, 2), 0, 1), (F(1, 2), 1, 1),
                        (F(1, 2), 1, 2), (F(1, 2), 2, 3),
                        (F(1, 10), 1, 2), (F(9, 10), 2, 1)):
            first, second = power(ps, t, k), power(ps, t, l)
            switched = switch_family(first, second)
            serial = [(w, tensor(eye(2), a)) for w, a in power(ps, t, k+l)]
            require(choi(switched) == choi(serial),
                    "complete control/target/reference self-switch compiler")
            require(effect(switched) == eye(2*d), "compiler is TP")
            compiler_cases += 1
        t = F(1, 2)
        before = fidelity(power(ps, t, 1))
        after = fidelity(power(ps, t, 2))
        require(before == 1-t+t/d and after == (1-t)**2+(1-(1-t)**2)/d
                and after < before, "full-space Petz composition is not inversion")
    for d in (3, 4):
        k, ps = 2, frame(d)
        p = code_projector(d, k)
        s2 = sum((trace(mul(p, pi)).r**2 for pi in ps), F())
        for t in (F(1, 10), F(1, 2), F(9, 10)):
            accepted = [(1-t, eye(k))]+[(t, cut(pi, k)) for pi in ps]
            j = choi(accepted)
            p_high, q_high = trace(j).r, fidelity(accepted)
            require(p_high == 1-t+t*s2/k and q_high == 1-t+t*s2/(k*k),
                    "high accepted full-Choi probability and joint Bell score")
            require(q_high <= p_high <= 1, "heralded statistics are joint probabilities")
            low = low_accepted(d, k, t)
            p_low, q_low = trace(choi(low)).r, fidelity(low)
            require(p_low == 1-t+t*k/d and q_low == 1-t+t/(k*d),
                    "low accepted probability and joint Bell score")
            # Complete either accepted map by a maximally mixed failure output.
            for family, prob, bell in ((accepted, p_high, q_high),
                                       (low, p_low, q_low)):
                f = add(eye(k), effect(family), -1)
                require(f[0][0].r >= 0 and f[1][1].r >= 0
                        and (f[0][0]*f[1][1]-f[0][1]*f[1][0]).r >= 0,
                        "two-dimensional rejection effect is positive")
                fail = [[C(int(a == c))*f[e][b]/(k*k)
                         for c in range(k) for e in range(k)]
                        for a in range(k) for b in range(k)]
                completed = add(choi(family), fail)
                require(trace(completed) == 1, "all-attempt completion is normalized")
                complete_bell = sum((completed[a*k+a][b*k+b]
                                     for a in range(k) for b in range(k)), C()).r/k
                require(complete_bell == bell+(1-prob)/(k*k),
                        "failure completion differs from conditional fidelity")
            projection_cases += 1
    # Uniform two-qubit rank-two stabilizer projectors reproduce the 2-design moment.
    single = [eye(2), [[C(), C(1)], [C(1), C()]],
              [[C(), C(0, -1)], [C(0, 1), C()]],
              [[C(1), C()], [C(), C(-1)]]]
    ps, total_s2 = frame(4), F()
    for a in range(4):
        for b in range(4):
            if a == b == 0:
                continue
            pauli = tensor(single[a], single[b])
            for sign in (-1, 1):
                p = scale(add(eye(4), scale(pauli, sign)), F(1, 2))
                require(mul(p, p) == p and trace(p) == 2, "stabilizer code projector")
                total_s2 += sum((trace(mul(p, pi)).r**2 for pi in ps), F())
                moment_cases += 1
    require(total_s2/moment_cases == F(6, 5),
            "exact random stabilizer projector second moment K(K+1)/(D+1)")
    # A flat-leverage proper code gives an exact raw-Petz success normalization.
    signs = [[1, 1, 1, 1], [1, -1, 1, -1],
             [1, 1, -1, -1], [1, -1, -1, 1]]
    ps = [scale(outer([C(x) for x in v]), F(1, 4)) for v in signs]
    p, t, k, d = code_projector(4, 2), F(2, 5), 2, 4
    e = power(ps, t, 1)
    m = apply(e, p)
    lam = t*k/d
    require(m == add(scale(p, 1-t), scale(eye(d), t*k/d)),
            "flat-leverage Petz output operator")
    filt = add(eye(d), scale(p, F(1, 2)), -1)
    raw = [(w, mul(mul(p, a), filt)) for w, a in e]
    require(effect(raw) == scale(eye(d), lam)
            and trace(choi(raw)) == lam,
            "full raw-Petz instrument has constant success tK/D")
    require(effect([(w/lam, a) for w, a in raw]) == eye(d),
            "normalized Petz channel is TP")
    tau_min, tau_max = t/d, (1-t)/k+t/d
    require(tau_max/tau_min == 1+(1-t)*d/(t*k)
            and 1/tau_min == d/t, "Petz spectral ratio versus reciprocal eigenvalue")
    for t in (F(1, 10), F(1, 2), F(9, 10)):
        for maximum in (1, 2, 3, 4):
            for threshold in (1, 2):
                leaves = finite_histories(t, maximum, threshold)
                require(sum((prob for _, _, prob in leaves), F()) == 1,
                        "finite adaptive history normalization")
                mean_calls = sum((n*prob for n, _, prob in leaves), F())
                mean_primitive = sum((2*b*prob for _, b, prob in leaves), F())
                require(mean_primitive == 2*t*mean_calls,
                        "terminal-history cost agrees with predictable Bernoulli ledger")
                for cap in (1, 2, 3):
                    tail = sum((prob for n, _, prob in leaves if n > cap), F())
                    require(tail <= mean_calls/cap, "one-sided high-mean truncation")
                    truncation_cases += 1
                ledger_cases += 1
    delta, high, low = F(215, 10000), F(7, 8), F(3, 4)
    require(high-low-delta == F(207, 2000)
            and (high-low-delta)/2 == F(207, 4000),
            "single-validation high-mean and balanced-mean constants")
    framed = verify_framed_echo()
    histories = verify_history_rank()
    return {
        "status": "passed", "complete_switch_compiler_cases": compiler_cases,
        "projection_instrument_cases": projection_cases,
        "stabilizer_second_moment_cases": moment_cases,
        "raw_petz_full_instrument_cases": 1,
        "finite_adaptive_cost_ledgers": ledger_cases,
        "one_sided_truncation_cases": truncation_cases,
        "high_mean_coefficient": "207/2000",
        "framed_qubit_guards": framed,
        "serial_history_guards": histories,
        "scope": ("Finite exact matrix and probability guards. Does not prove C6, "
                  "all-dimension coding or a general Petz decoder lower bound; "
                  "the specific framed-qubit echo comparison is not a compiler "
                  "for arbitrary framed switches or a native hardware validation. "
                  "Serial-history cases check the explicit aligned multilinear "
                  "model, not that an arbitrary device has that interface; "
                  "the universal rank and exact-herald statements remain analytic.")
    }


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True))
