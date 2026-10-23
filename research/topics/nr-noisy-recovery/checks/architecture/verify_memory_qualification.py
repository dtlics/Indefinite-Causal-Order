"""Exact finite guards for memory qualification and amplified switch blocks.

The all-dimension capacity, query and stopping arguments are analytic.
No third-party dependencies, file writes, or import-time output.
"""

from fractions import Fraction as F
from math import comb, factorial
import json

if not __debug__:
    raise RuntimeError("Run burst guards without -O.")


def require(value, message):
    if not value:
        raise RuntimeError(message)


def bracket(a, b, n):
    mask = (1 << n) - 1
    return (((a & mask) & (b >> n)).bit_count()
            + ((b & mask) & (a >> n)).bit_count()) & 1


def weight(a, n):
    return ((a & ((1 << n) - 1)) | (a >> n)).bit_count()


def graph_lagrangian(n, edges):
    labels = []
    for x in range(1 << n):
        z = 0
        for a, b in edges:
            z ^= (((x >> a) & 1) << b) ^ (((x >> b) & 1) << a)
        labels.append(x | (z << n))
    require(len(set(labels)) == 1 << n, "graph rank")
    require(all(bracket(a, b, n) == 0 for a in labels for b in labels),
            "graph is Lagrangian")
    return labels


def mixture(size, labels, t):
    p = [F(0)] * size
    p[0] = 1 - t
    for a in labels:
        p[a] += t / len(labels)
    return p


def eta(p, q, n):
    return sum((pa * qb * (1 - 2 * bracket(a, b, n))
                for a, pa in enumerate(p) if pa
                for b, qb in enumerate(q) if qb), F(0))


def eigenvalues(p, n):
    return [sum((pa * (1 - 2 * bracket(a, b, n))
                 for a, pa in enumerate(p) if pa), F(0))
            for b in range(len(p))]


def convolution(p, q):
    result = [F(0)] * len(p)
    for a, pa in enumerate(p):
        if pa:
            for b, qb in enumerate(q):
                if qb:
                    result[a ^ b] += pa * qb
    return result


def rank(labels):
    pivots = {}
    for x in labels:
        while x:
            b = x.bit_length() - 1
            if b not in pivots:
                pivots[b] = x
                break
            x ^= pivots[b]
    return len(pivots)


def syndrome(label, generators, n):
    return sum(bracket(label, g, n) << j for j, g in enumerate(generators))


def verify_code_verification():
    cases = 0
    for k in (2, 3, 4, 5):
        # W1,W2 are unnormalized Bell embeddings; dividing by sqrt(k)
        # gives the isometries used in the general projector-norm proof.
        w1 = [{(i, i, j): F(1) for i in range(k)} for j in range(k)]
        w2 = [{(i, j, i): F(1) for i in range(k)} for j in range(k)]
        dot = lambda a, b: sum((value * b.get(key, 0) for key, value in a.items()), F(0))
        for a in range(k):
            for b in range(k):
                require(dot(w1[a], w1[b]) == (k if a == b else 0), "first Bell isometry")
                require(dot(w2[a], w2[b]) == (k if a == b else 0), "second Bell isometry")
                require(dot(w1[a], w2[b]) == (1 if a == b else 0), "Bell isometry cross Gram")
                cases += 1
        for a in range(k):
            vector = {key: w1[a].get(key, 0) + w2[a].get(key, 0)
                      for key in w1[a].keys() | w2[a].keys()}
            image = {}
            for family in (w1, w2):
                for column in family:
                    scale = dot(column, vector) / k
                    if not scale:
                        continue
                    for key, value in column.items():
                        image[key] = image.get(key, F(0)) + scale * value
            require(image == {key: F(k + 1, k) * value for key, value in vector.items()},
                    "largest Bell-projector sum eigenvalue is attained")
    # e^(319/128)>12 already follows from a finite rational Taylor sum.
    # Hoeffding then bounds each qubit-code Bell-test error by 1/12.
    require(sum((F(319, 128) ** j / factorial(j) for j in range(11)), F(0)) > 12,
            "319 independent Bell trials give the claimed confidence")
    require(F(1, 2) * (F(2, 3) * F(11, 12) + F(11, 12)) == F(55, 72) > F(2, 3),
            "successful-code training gives sufficient balanced discrimination")
    return cases


def verify_memory_qualification():
    scalar_cases = local_modes = composition_cases = syndrome_cases = 0
    coherence_cases = correlation_cases = amplification_cases = 0
    full_instrument_cases = mean_ledger_cases = 0
    rates = (F(0), F(1, 10), F(1, 3), F(1))
    for n in (1, 2, 3):
        d, size = 1 << n, 1 << (2 * n)
        edges = [(j, j + 1) for j in range(n - 1)]
        lag = graph_lagrangian(n, edges)
        full = list(range(size))
        for t in rates:
            p1, p0 = mixture(size, lag, t), mixture(size, full, t)
            e1, e0 = eta(p1, p1, n), eta(p0, p0, n)
            require(e1 == 1, "structured commuting null")
            require(e0 == 1 - t * t * (1 - F(1, size)), "depolarizing self scalar")
            require((e1 - e0) / 2 == t * t * (1 - F(1, size)) / 2,
                    "ideal minus gap")
            require(e1 - e0 >= 3 * t * t / 4, "dimension-uniform scalar gap")
            scalar_cases += 1
            for p, support in ((p1, lag), (p0, full)):
                result = convolution(p, p)
                expected = mixture(size, support, 1 - (1 - t) ** 2)
                require(result == expected, "idempotent-component composition")
                composition_cases += 1
            # Identical marginals do not fix the physical two-time switch signal.
            diagonal_eta = sum(p0)  # P(a,b)=p0(a) 1[a=b].
            require(diagonal_eta == 1, "quasistatic diagonal law has no minus events")
            correlation_cases += 1
            for ell in (1, 2, 3, 5):
                effective_t = 1 - (1 - t) ** ell
                for p, support, structured in ((p1, lag, True), (p0, full, False)):
                    power = [F(0)] * size
                    power[0] = 1
                    for _ in range(ell):
                        power = convolution(power, p)
                    require(power == mixture(size, support, effective_t),
                            "fresh-slot block amplification")
                    expected_eta = (F(1) if structured else
                                    1 - effective_t ** 2 * (1 - F(1, size)))
                    require(eta(power, power, n) == expected_eta,
                            "amplified whole-block switch scalar")
                    # Independently sum the actual flagged Pauli Kraus pairs.
                    plus, minus = [F(0)] * size, [F(0)] * size
                    for a, pa in enumerate(power):
                        for b, pb in enumerate(power):
                            branch = minus if bracket(a, b, n) else plus
                            branch[a ^ b] += pa * pb
                    s, r = effective_t, 1 - effective_t
                    if structured:
                        expected_plus = mixture(size, support, 1 - r * r)
                        expected_minus = [F(0)] * size
                    else:
                        expected_plus = [2 * r * s / size + s * s / (2 * size)
                                         + (r * r + s * s / (2 * size) if a == 0 else 0)
                                         for a in range(size)]
                        expected_minus = [s * s / (2 * size)
                                          - (s * s / (2 * size) if a == 0 else 0)
                                          for a in range(size)]
                    require(plus == expected_plus and minus == expected_minus,
                            "complete amplified flagged target channel")
                    require(min(plus + minus) >= 0 and sum(plus + minus) == 1,
                            "complete flagged CP/TP normalization")
                    full_instrument_cases += 1
                    amplification_cases += 1
            for visibility in (F(0), F(97, 100), F(1)):
                b = (1 - visibility) / 2
                observed1 = (1 - visibility * e1) / 2
                observed0 = (1 - visibility * e0) / 2
                gap = visibility * t * t * (1 - F(1, size)) / 2
                require(observed1 == b and observed0 == b + gap,
                        "independent helper visibility law")
                coherence_cases += 1
        # Two known stabilizer settings, including the computational basis.
        settings = [list(1 << (n + j) for j in range(n)),
                    list((1 << j) | (((1 << (j - 1) if j else 0)
                          ^ (1 << (j + 1) if j + 1 < n else 0)) << n)
                         for j in range(n))]
        for generators in settings:
            require(rank(generators) == n, "setting generator rank")
            image = [syndrome(a, generators, n) for a in lag]
            r = rank(image)
            require(len(set(image)) == 1 << r, "uniform syndrome image size")
            counts = {s: image.count(s) for s in set(image)}
            require(len(set(counts.values())) == 1, "uniform syndrome image multiplicity")
            for t in rates:
                law = [F(0)] * d
                law[0] = 1 - t
                for s in image:
                    law[s] += t / d
                expected = [((1 - t) if s == 0 else 0)
                            + (t / (1 << r) if s in counts else 0)
                            for s in range(d)]
                require(law == expected, "atom-plus-subspace syndrome law")
                syndrome_cases += 1
    # Finite high-distance examples: Bell graph and the five-cycle graph.
    for n, edges, w in ((2, [(0, 1)], 1),
                         (5, [(j, (j + 1) % 5) for j in range(5)], 2)):
        d, size = 1 << n, 1 << (2 * n)
        lag = graph_lagrangian(n, edges)
        require(min(weight(a, n) for a in lag if a) > w, "finite distance guard")
        for t in rates:
            p1, p0 = mixture(size, lag, t), mixture(size, range(size), t)
            # Only evaluate the low-weight characters; no large dense matrices.
            for b in range(1, size):
                if weight(b, n) <= w:
                    l1 = sum((p1[a] * (1 - 2 * bracket(a, b, n))
                              for a in lag), F(0))
                    l0 = 1 - t  # Orthogonality of the complete label group.
                    require(l1 == l0 == 1 - t, "locally identical channel eigenvalues")
                    local_modes += 1
    # A history-dependent finite stopping rule checks the predictable-coin
    # ledger independently of a fixed-length binomial identity. Each call
    # occurs before its fresh Bernoulli draw; the receiver may stop on a burst.
    for t in (F(1, 7), F(1, 2), F(1)):
        for horizon in (1, 2, 5, 9):
            for required_bursts in (1, 2, 3):
                live = {(0, 0): F(1)}
                expected_calls = expected_primitive = F(0)
                terminal_calls = terminal_primitive = terminal_mass = F(0)
                while live:
                    fresh = {}
                    for (calls, bursts), probability in live.items():
                        if calls == horizon or bursts >= required_bursts:
                            terminal_mass += probability
                            terminal_calls += calls * probability
                            terminal_primitive += 2 * bursts * probability
                            continue
                        expected_calls += probability
                        expected_primitive += 2 * probability * t
                        for event, event_probability in ((0, 1 - t), (1, t)):
                            key = (calls + 1, bursts + event)
                            fresh[key] = fresh.get(key, F(0)) + probability * event_probability
                    live = fresh
                require(terminal_mass == 1, "complete stopped-history law")
                require(terminal_calls == expected_calls and
                        terminal_primitive == expected_primitive,
                        "terminal trajectory costs equal predictable increments")
                require(terminal_primitive == 2 * t * terminal_calls,
                        "history-dependent production simulation mean ledger")
                mean_ledger_cases += 1
    require(F(2, 3) - F(1, 12) > (1 + F(215, 10000)) / 2,
            "C6 mean-cost truncation contradiction has strict margin")
    require(F(3, 32) <= (1 - F(1, 4)) / 8,
            "amplified dimension-uniform minus probability")
    code_cases = verify_code_verification()
    return {"status": "passed", "scalar_cases": scalar_cases,
            "composition_cases": composition_cases, "syndrome_laws": syndrome_cases,
            "low_weight_eigenvalue_cases": local_modes,
            "visibility_cases": coherence_cases, "quasistatic_counterexamples": correlation_cases,
            "amplified_block_cases": amplification_cases,
            "complete_flagged_instruments": full_instrument_cases,
            "adaptive_mean_ledger_cases": mean_ledger_cases,
            "code_verification_isometry_entries": code_cases,
            "scope": "Finite exact Pauli-channel instruments and stopping ledgers; general capacity/C6 reduction, coherent interface, native costs and all-dimension proofs remain analytic."}


if __name__ == "__main__":
    print(json.dumps(verify_memory_qualification(), sort_keys=True))
