"""Exact finite guards for noisy Pauli-subspace and hidden-product structure.

All-dimension concentration, moment bounds, population recovery,
model selection and physical access remain analytic in
methods/pauli-noisy-structure.md. This module performs no search,
learning simulation, floating-point feasibility or hardware certification.
"""
if not __debug__:
    raise RuntimeError("Run without -O: exact verification requires assertions")

from fractions import Fraction as F
from itertools import combinations
import json
import math


def bracket(a, b, n):
    mask = (1 << n) - 1
    return ((((a & mask) & (b >> n)).bit_count()
             + ((a >> n) & (b & mask)).bit_count()) & 1)


def sign(a, b, n):
    return 1 - 2 * bracket(a, b, n)


def eta(p, n):
    return sum((pa * pb * sign(a, b, n)
                for a, pa in p.items() for b, pb in p.items()), F(0))


def span(basis):
    out = {0}
    for b in basis:
        out |= {x ^ b for x in tuple(out)}
    return frozenset(out)


def basis_of(vectors):
    basis = {}
    for v in vectors:
        x = v
        while x:
            j = x.bit_length() - 1
            if j not in basis:
                basis[j] = x
                break
            x ^= basis[j]
    return tuple(basis[j] for j in sorted(basis))


def subspaces(n, k):
    seen = set()
    for candidate in combinations(range(1, 1 << n), k):
        if len(basis_of(candidate)) == k:
            seen.add(span(candidate))
    return tuple(sorted(seen, key=lambda s: tuple(sorted(s))))


def replay_mixtures():
    alpha, beta, gamma = F(19, 50), F(61, 100), F(1, 100)
    total_frames = fourier_margins = distinct_annihilators = 0
    total_moments = 0
    for n in (1, 2, 3):
        D = 1 << n
        spaces = subspaces(2 * n, n)
        lagrangians = [v for v in spaces
                       if all(bracket(a, b, n) == 0 for a in v for b in v)]
        assert len(lagrangians) == math.prod((1 << j) + 1 for j in range(1, n + 1))
        # Exhaust all 35 rank-two spaces; for n=3 retain each symplectic type
        # and several oriented instances, while keeping this replay small.
        if n == 3:
            chosen = list(spaces[:4]) + list(spaces[-4:])
            for target in (F(1), F(1, 4)):
                chosen.append(next(v for v in spaces
                                   if eta({a: F(1, D) for a in v}, n) == target))
            spaces = tuple(dict.fromkeys(chosen))
        for V in spaces:
            pv = {a: F(1, D) for a in V}
            ev = eta(pv, n)
            p = {a: alpha * (a == 0) + beta * F(a in V, D) + gamma / D ** 2
                 for a in range(D ** 2)}
            expected = 2 * alpha - alpha ** 2 + beta ** 2 * ev + 2 * beta * gamma / D + gamma ** 2 / D ** 2
            assert eta(p, n) == expected
            assert p[0] == alpha + beta / D + gamma / D ** 2
            xsq = xfourth = F(0)
            for M in lagrangians:
                mb = basis_of(M)
                def synd(a):
                    return sum(bracket(a, b, n) << j for j, b in enumerate(mb))
                W = frozenset(synd(a) for a in V)
                sy = {y: F(0) for y in range(D)}
                for a, pa in p.items():
                    sy[synd(a)] += pa
                assert all(sy[y] == alpha * (y == 0) + beta * F(y in W, len(W)) + gamma / D
                           for y in range(D))
                accepted = {0}
                for v in range(1, D):
                    bias = sum((prob * (1 - 2 * ((v & y).bit_count() & 1)) for y, prob in sy.items()), F(0))
                    in_kernel = all(((v & y).bit_count() & 1) == 0 for y in W)
                    assert bias == alpha + beta * in_kernel
                    if in_kernel:
                        assert bias-beta/4 > alpha+beta/2
                    else:
                        assert bias+beta/4 < alpha+beta/2
                    fourier_margins += 1
                    if bias > alpha + beta / 2:
                        accepted.add(v)
                assert accepted == span(basis_of(accepted))
                assert len(accepted) == D // len(W) == len(V & M)
                physical = set()
                for v in accepted:
                    x = 0
                    for j, b in enumerate(mb):
                        if (v >> j) & 1:
                            x ^= b
                    physical.add(x)
                assert physical == {x for x in M if all(not bracket(a, x, n) for a in V)}
                distinct_annihilators += physical != V & M
                xsq += len(accepted) ** 2
                xfourth += len(accepted) ** 4
                total_frames += 1
            mu = xsq / len(lagrangians)
            expected_mu = 1 + F(3 * (D - 1), D + 1) + F((1 + ev) * D ** 2 / 2 - 3 * D + 2, (D + 1) * (D // 2 + 1))
            assert mu == expected_mu
            assert xfourth/len(lagrangians) <= 270
            assert F(D*D, (D+1)*(D+2)) >= F(1, 3)
            total_moments += 1
    assert distinct_annihilators > 0
    return {"frames": total_frames, "subspace_moments": total_moments,
            "fourth_moment_bounds": total_moments,
            "robust_fourier_thresholds": fourier_margins,
            "annihilator_not_support_intersection": distinct_annihilators}


def weight(a, n):
    return sum(bool(((a >> i) & 1) or ((a >> (n+i)) & 1)) for i in range(n))


def law(n, q, alpha=F(19, 50)):
    beta = 1-alpha
    return [beta*(q/3)**weight(a, n)*(1-q)**(n-weight(a, n))
            + (alpha if a == 0 else 0) for a in range(1 << (2*n))]


def convolution(p, q):
    return [sum((pa*q[x ^ a] for a, pa in enumerate(p)), F(0))
            for x in range(len(p))]


def scramble(a, n, seed):
    for step in range(3*n+seed):
        i = (step+seed) % n
        if (step+seed) % 2 == 0:  # H_i
            x, z = (a >> i) & 1, (a >> (n+i)) & 1
            if x != z:
                a ^= (1 << i) | (1 << (n+i))
        if (step+2*seed) % 3 != 1:  # S_i
            a ^= ((a >> i) & 1) << (n+i)
        if n > 1:  # CNOT_i,j
            j = (i+1) % n
            a ^= ((a >> i) & 1) << j
            a ^= ((a >> (n+j)) & 1) << (n+i)
    return a


def invariants():
    scalar_cases = eigenvalues = serial_cases = 0
    alpha, beta = F(19, 50), F(31, 50)
    for n in (1, 2, 3):
        for q in (F(1, 20), F(1, 10), F(1, 3)):
            p = law(n, q)
            assert sum(p) == 1
            v = (1-q)**n
            w = ((1-q)**2+q*q/3)**n
            t = 1-4*q/3
            eta = sum((pa*pb*(1-2*bracket(a, b, n))
                       for a, pa in enumerate(p) for b, pb in enumerate(p)), F(0))
            assert eta == 1-beta*beta+beta*beta*(1-4*q*q/3)**n
            assert p[0] == alpha+beta*v
            collision = sum(pa*pa for pa in p)
            assert collision == alpha*alpha+2*alpha*beta*v+beta*beta*w
            assert (collision-p[0]*p[0])/(1-p[0])**2 == (w-v*v)/(1-v)**2
            for b in range(len(p)):
                eigen = sum((pa*(1-2*bracket(a, b, n)) for a, pa in enumerate(p)), F(0))
                assert eigen == alpha+beta*t**weight(b, n)
                eigenvalues += 1
            scalar_cases += 1
            if n <= 2:
                power = [F(a == 0) for a in range(len(p))]
                for m in range(1, 8):
                    power = convolution(power, p)
                    predicted = sum((F(math.comb(m, k))*alpha**(m-k)*beta**k
                                     *((1+3*t**k)/4)**n for k in range(m+1)), F(0))
                    assert power[0] == predicted
                    assert 0 <= power[0]-alpha**m <= v
                    serial_cases += 1
    return {"exact_scalar_cases": scalar_cases, "exact_eigenvalues": eigenvalues,
            "exact_serial_return_cases": serial_cases}


def short_window():
    beta = F(31, 50)
    margin_cases = heavy_tail_weights = extracted_frames = decoded_labels = full_probes = 0
    for n in range(1, 65):
        theta, threshold = beta/F(512*n), beta/F(64*n)
        qlo, qhi = F(1, 8*n), F(1, 4*n)
        assert (1-qhi)**(n-1) >= F(3, 4)
        lower = beta/(24*n)*(1-qhi)**(n-1)
        assert lower >= beta/(32*n)
        assert lower-theta > threshold
        upper = beta/F(144*n*n)
        assert upper+theta < threshold
        for q in (qlo, (qlo+qhi)/2, qhi):
            single = beta*q/3*(1-q)**(n-1)
            assert single >= lower
            margin_cases += 1
            for w in range(2, n+1):
                assert beta*(q/3)**w*(1-q)**(n-w) <= upper
                heavy_tail_weights += 1
    for n in (1, 2, 3, 4):
        q = F(3, 16*n)
        theta, threshold = beta/F(512*n), beta/F(64*n)
        for seed in range(4):
            p = law(n, q)
            scrambled = {scramble(a, n, seed): pa for a, pa in enumerate(p)}
            assert len(scrambled) == len(p)
            accepted = {a for a, pa in scrambled.items() if a and pa >= threshold}
            # Worst signed infinity errors still give exactly the same support.
            assert all(pa-theta > threshold for a, pa in scrambled.items() if a in accepted)
            assert all(pa+theta < threshold for a, pa in scrambled.items() if a and a not in accepted)
            assert accepted == {scramble(a, n, seed) for a in range(len(p)) if weight(a, n) == 1}
            assert len(accepted) == 3*n
            remaining, pairs = set(accepted), []
            while remaining:
                a = min(remaining)
                component = {a} | {b for b in accepted if bracket(a, b, n)}
                assert len(component) == 3
                assert all(bracket(x, y, n) == (x != y) for x in component for y in component)
                assert all(not bracket(x, y, n) for x in component for y in accepted-component)
                b = min(component-{a})
                assert component == {a, b, a ^ b}
                pairs.append((a, b))
                remaining -= component
            assert len(pairs) == n
            columns = [a for a, _ in pairs]+[b for _, b in pairs]
            inverse = {}
            for a in range(len(p)):
                physical = 0
                for j, col in enumerate(columns):
                    if (a >> j) & 1:
                        physical ^= col
                inverse[physical] = a
            assert len(inverse) == len(p)
            for a in range(len(p)):
                assert weight(inverse[scramble(a, n, seed)], n) == weight(a, n)
                decoded_labels += 1
            for q_full in (F(1, 10), F(1, 3)):
                full = {scramble(a, n, seed): pa for a, pa in enumerate(law(n, q_full))}
                for s in accepted:
                    eigen = sum((pa*(1-2*bracket(a, s, n)) for a, pa in full.items()), F(0))
                    assert eigen == 1-4*beta*q_full/3
                    assert 3*(1-eigen)/(4*beta) == q_full
                    full_probes += 1
            extracted_frames += 1
    return {"short_window_parameter_guards": margin_cases,
            "short_window_high_weight_guards": heavy_tail_weights,
            "thresholded_clifford_frames": extracted_frames,
            "recovered_frame_weight_labels": decoded_labels,
            "full_window_known_label_q_probes": full_probes}


def finite_hash_guards():
    vector_inclusions = law_pairs = 0
    for n in (1, 2, 3):
        d = 1 << n
        lags = [v for v in subspaces(2*n, n)
                if all(not bracket(a, b, n) for a in v for b in v)]
        assert len(lags) == math.prod((1 << j)+1 for j in range(1, n+1))
        for a in range(1, d*d):
            assert F(sum(a in ell for ell in lags), len(lags)) == F(1, d+1)
            vector_inclusions += 1
        cases = (({0: F(1, 3), 1: F(2, 3)}, {2: F(1, 4), 3: F(3, 4)}),
                 ({0: F(1, 2), 1: F(1, 2)}, {0: F(1, 3), 2: F(2, 3)}),
                 ({1: F(1)}, {2: F(1)}))
        for p, q in cases:
            support = set(p) | set(q)
            full_tv = sum((abs(p.get(a, 0)-q.get(a, 0)) for a in support), F(0))/2
            projected_tv = F(0)
            for ell in lags:
                generators = basis_of(ell)
                left, right = {}, {}
                for source, result in ((p, left), (q, right)):
                    for a, probability in source.items():
                        y = sum(bracket(a, b, n) << j for j, b in enumerate(generators))
                        result[y] = result.get(y, F(0))+probability
                projected_tv += sum((abs(left.get(y, 0)-right.get(y, 0))
                                     for y in set(left) | set(right)), F(0))/2
            projected_tv /= len(lags)
            assert projected_tv <= full_tv
            assert projected_tv >= (1-F(len(support)-1, d+1))*full_tv
            law_pairs += 1
    return {"hash_nonzero_vector_inclusions": vector_inclusions,
            "finite_supported_hash_tv_pairs": law_pairs}


def pcs_matrix_guards():
    # Gaussian rationals are pairs (real, imaginary); no floating point.
    def add(x, y):
        return x[0]+y[0], x[1]+y[1]

    def multiply(x, y):
        return x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0]

    def product(a, b):
        result = [[(0, 0) for _ in b[0]] for _ in a]
        for i, row in enumerate(a):
            for k, x in enumerate(row):
                if x == (0, 0):
                    continue
                for j, y in enumerate(b[k]):
                    if y != (0, 0):
                        result[i][j] = add(result[i][j], multiply(x, y))
        return result

    def adjoint(a):
        return [[(a[j][i][0], -a[j][i][1]) for j in range(len(a))]
                for i in range(len(a[0]))]

    def block(a, b):
        d = len(a)
        return [[(a[i][j] if i < d and j < d else
                  b[i-d][j-d] if i >= d and j >= d else (0, 0))
                 for j in range(2*d)] for i in range(2*d)]

    def pauli(a, n):
        d, x, z = 1 << n, a & ((1 << n)-1), a >> n
        roots = ((1, 0), (0, 1), (-1, 0), (0, -1))
        result = [[(0, 0) for _ in range(d)] for _ in range(d)]
        for v in range(d):
            phase = ((x & z).bit_count()+2*((z & v).bit_count() & 1)) % 4
            result[v ^ x][v] = roots[phase]
        return result

    unitary_cases = density_cases = mixture_cases = matrix_entries = 0
    for n in (1, 2):
        d, size = 1 << n, 1 << (2*n)
        identity = [[(int(i == j), 0) for j in range(d)] for i in range(d)]
        joint_identity = block(identity, identity)
        rho = [[(F(1, 2*d), 0) if i % d == j % d else (0, 0)
                for j in range(2*d)] for i in range(2*d)]
        outputs = {}
        for a in range(size):
            pa = pauli(a, n)
            for b in range(size):
                cb = block(identity, pauli(b, n))
                joint = product(product(cb, block(pa, pa)), cb)
                chi = sign(a, b, n)
                expected = block(pa, [[(chi*x, chi*y) for x, y in row] for row in pa])
                assert joint == expected
                assert product(joint, adjoint(joint)) == joint_identity
                unitary_cases += 1
                output = product(product(joint, rho), adjoint(joint))
                target = [[(F(chi if (i//d) != (j//d) else 1, 2*d), 0)
                           if i % d == j % d else (0, 0)
                           for j in range(2*d)] for i in range(2*d)]
                assert output == target
                outputs[a, b] = output
                density_cases += 1
                matrix_entries += (2*d)**2
        for p in pcs_laws(n):
            for b in range(size):
                average = [[(0, 0) for _ in range(2*d)] for _ in range(2*d)]
                for a, probability in p.items():
                    for i in range(2*d):
                        for j in range(2*d):
                            x, y = outputs[a, b][i][j]
                            average[i][j] = add(average[i][j], (probability*x, probability*y))
                eigen = sum((probability*sign(a, b, n) for a, probability in p.items()), F(0))
                expected = [[(F(1, 2*d)*(eigen if i//d != j//d else 1), 0)
                             if i % d == j % d else (0, 0)
                             for j in range(2*d)] for i in range(2*d)]
                assert average == expected
                mixture_cases += 1
    return {"pcs_joint_unitaries": unitary_cases, "pcs_mixed_target_density_cases": density_cases,
            "pcs_joint_density_entries": matrix_entries, "pcs_mixed_law_instruments": mixture_cases}


def pcs_laws(n):
    size = 1 << (2*n)
    raw = ({a: F(a+1, size*(size+1)//2) for a in range(size)},
           {a: F(1+(a*a+3*a) % 7) for a in range(size)},
           {0: F(2, 5), 1: F(1, 5), size-1: F(2, 5)})
    return tuple({a: probability/sum(p.values(), F(0)) for a, probability in p.items()}
                 for p in raw)


def pcs_prefix_guards():
    def normalized(p):
        total = sum(p.values(), F(0))
        return {a: value/total for a, value in p.items()}

    def prefix_mass(p, s, k):
        return sum((value for a, value in p.items() if a & ((1 << k)-1) == s), F(0))

    def tree(p, length, theta, record):
        cap = math.ceil(4/theta)
        retained, tested = [0], 0
        for k in range(1, length+1):
            candidates = [s | (bit << (k-1)) for s in retained for bit in (0, 1)]
            tested += len(candidates)
            assert tested <= 2*length*cap
            following = []
            for s in candidates:
                mass = prefix_mass(p, s, k)
                estimate = record(s, k, mass)
                if estimate >= theta/2:
                    following.append(s)
            if len(following) > cap:
                return (), tested, True
            retained = following
            assert len(retained) <= cap
        return tuple(retained), tested, False

    prefixes = branches = tree_cases = bad_caps = short_trees = 0
    for n in (1, 2):
        length = 2*n
        dual = [(1 << (n+j)) if j < n else (1 << (j-n)) for j in range(length)]
        assert all(bracket(a, g, n) == ((a >> j) & 1)
                   for a in range(1 << length) for j, g in enumerate(dual))
        for raw in pcs_laws(n):
            p = normalized(raw)
            for k in range(length+1):
                for s in range(1 << k):
                    mean = plus = F(0)
                    for z in range(1 << k):
                        b = 0
                        for j in range(k):
                            if (z >> j) & 1:
                                b ^= dual[j]
                        eigen = sum((probability*sign(a, b, n) for a, probability in p.items()), F(0))
                        signed = (1-2*((s & z).bit_count() & 1))*eigen
                        mean += signed/(1 << k)
                        plus += (1+signed)/(2*(1 << k))
                        branches += 1
                    assert mean == prefix_mass(p, s, k)
                    assert plus == (1+prefix_mass(p, s, k))/2
                    prefixes += 1
            for theta in (F(1, 2), F(1, 3), F(1, 4), F(1, 8)):
                for seed in range(4):
                    def good(s, k, mass):
                        value = mass+theta*F((-1)**(s+k+seed), 4)
                        assert abs(value-mass) <= theta/4
                        if value >= theta/2:
                            assert mass >= theta/4
                        if mass >= theta:
                            assert value >= theta/2
                        return value
                    leaves, tested, aborted = tree(p, length, theta, good)
                    assert not aborted
                    assert {a for a, value in p.items() if value >= theta} <= set(leaves)
                    assert tested <= 2*length*math.ceil(4/theta)
                    tree_cases += 1
            for theta in (F(1, 2), F(3, 4)):
                _, tested, aborted = tree(p, length, theta, lambda s, k, mass: F(1))
                assert tested <= 2*length*math.ceil(4/theta)
                bad_caps += aborted
    assert bad_caps > 0
    # The short-window leaf filter uses the same tested-node error budget.
    beta = F(31, 50)
    for n in (1, 2, 3, 4):
        theta, q = beta/F(512*n), F(3, 16*n)
        for seed in range(4):
            p = {scramble(a, n, seed): value for a, value in enumerate(law(n, q))}
            estimates = {}
            def good_short(s, k, mass):
                estimate = mass+theta*F((-1)**(s+k+seed), 4)
                estimates[k, s] = estimate
                return estimate
            leaves, _, aborted = tree(p, 2*n, theta, good_short)
            assert not aborted
            accepted = {a for a in leaves if a and estimates[2*n, a] > 8*theta}
            expected = {scramble(a, n, seed) for a in range(1 << (2*n)) if weight(a, n) == 1}
            assert accepted == expected and len(accepted) == 3*n
            short_trees += 1
    return {"pcs_signed_prefix_means": prefixes, "pcs_prefix_character_branches": branches,
            "pcs_good_record_trees": tree_cases, "pcs_bad_record_cap_aborts": bad_caps,
            "pcs_short_window_filtered_trees": short_trees}


def verify():
    return {"status": "passed", "arithmetic": "exact rational and binary linear algebra",
            "noisy_subspace_mixtures": replay_mixtures(),
            **finite_hash_guards(), **invariants(), **short_window(),
            **pcs_matrix_guards(), **pcs_prefix_guards(),
            "scope": ("Finite n=1,2,3 mixture/Fourier/rank-to-moment and hidden-product "
                      "invariants; n=1..64 short-window coefficient margins; explicit "
                      "n=1..4 hidden-frame extraction and full-window Pauli probes. "
                      "Exact small mixed-target PCS joint instruments, signed-prefix "
                      "averages and good/bad-record tree guards. General concentration, "
                      "fourth moments, population recovery, "
                      "finite-family selection, physical timing and SPAM remain analytic. "
                      "No arbitrary-noise estimator, general lower bound or native advantage.")}


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True))
