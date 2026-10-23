"""Exact finite guards for ordinary Pauli-subspace scalar calibration.

The distribution-free, all-dimension and physical-resource arguments
remain analytic in methods/pauli-subspace-calibration.md.
"""
if not __debug__:
    raise RuntimeError("Run without -O: exact verification requires assertions")

from fractions import Fraction as F
import json


def bracket(a, b, n):
    mask = (1 << n) - 1
    return (((a & mask) & (b >> n)).bit_count()
            + ((b & mask) & (a >> n)).bit_count()) & 1


def subspaces(bits):
    levels = [[frozenset([0])]]
    for _ in range(bits):
        next_level = set()
        for space in levels[-1]:
            for a in range(1 << bits):
                if a not in space:
                    next_level.add(frozenset(space | {a ^ b for b in space}))
        levels.append(sorted(next_level, key=lambda s: tuple(sorted(s))))
    return levels


def basis(space):
    selected, span = [], {0}
    for a in sorted(space):
        if a not in span:
            selected.append(a)
            span |= {a ^ b for b in tuple(span)}
    assert span == space
    return selected


def syndrome(a, generators, n):
    return sum(bracket(a, b, n) << j for j, b in enumerate(generators))


def dimension(space):
    result = len(space).bit_length() - 1
    assert len(space) == 1 << result
    return result


def geometry_and_empirical_constraints():
    disjoint = injective_labels = pz_cases = all_rank_pz = 0
    pac_constraints = false_constraints = uniform_images = 0
    for n in (1, 2):
        d = 1 << n
        spaces = subspaces(2*n)
        all_spaces = [space for level in spaces for space in level]
        lags = [space for space in spaces[n]
                if all(not bracket(a, b, n) for a in space for b in space)]
        assert len(lags) == (3 if n == 1 else 15)
        syndrome_spaces = [space for level in subspaces(n) for space in level]
        for v in all_spaces:
            for m in lags:
                mb = basis(m)
                image = {syndrome(a, mb, n) for a in v}
                exact_k = {x for x in m if all(not bracket(a, x, n) for a in v)}
                assert len(image)*len(exact_k) == d
                counts = {y: sum(syndrome(a, mb, n) == y for a in v)
                          for y in image}
                assert set(counts.values()) == {len(v)//len(image)}
                uniform_images += 1
            if dimension(v) > n:
                continue
            m0 = next(m for m in lags if v & m == {0})
            decoded = {syndrome(a, basis(m0), n): a for a in v}
            assert len(decoded) == len(v)
            assert all(decoded[syndrome(a, basis(m0), n)] == a for a in v)
            disjoint += 1
            injective_labels += len(v)
            # Nonuniform weights retain the whole support, including rare labels.
            for tilt in (1, 11):
                weights = {a: F(tilt if a == 0 else 1, tilt + len(v) - 1)
                           for a in v}
                for m in lags:
                    mb = basis(m)
                    image = {syndrome(a, mb, n) for a in v}
                    coordinates = {}
                    for c in range(d):
                        x = 0
                        for j, b in enumerate(mb):
                            if (c >> j) & 1:
                                x ^= b
                        coordinates[x] = c
                    exact_k = {x for x in m
                               if all(not bracket(a, x, n) for a in v)}
                    for w in (space for space in syndrome_spaces if space <= image):
                        outside = sum((p for a, p in weights.items()
                                       if syndrome(a, mb, n) not in w), F(0))
                        k = {x for x in m if all(
                            (coordinates[x] & y).bit_count() % 2 == 0 for y in w)}
                        assert exact_k <= k
                        for x in k:
                            bad = sum((p for a, p in weights.items()
                                       if bracket(a, x, n)), F(0))
                            assert bad <= outside
                            pac_constraints += 1
                            false_constraints += x not in exact_k
        for t in all_spaces:
            for s in all_spaces:
                if not s < t:
                    continue
                missing = t - s
                values = [len(missing & m) for m in lags]
                mu = F(sum(values), len(lags))
                second = F(sum(y*y for y in values), len(lags))
                probability = F(sum(y > 0 for y in values), len(lags))
                c = max(0, n-dimension(t))
                assert mu == F(len(missing), d+1) >= F(1, 3*(1 << c))
                assert second <= mu+2*mu*mu
                assert probability >= mu*mu/second >= F(1, 5*(1 << c))
                all_rank_pz += 1
                if dimension(t) >= n:
                    pz_cases += 1
    assert (disjoint, pz_cases, pac_constraints, false_constraints) == (
        55, 438, 11340, 4692)
    return {"injective_subspaces": disjoint,
            "injectively_decoded_labels": injective_labels,
            "proper_span_expansion_cases": pz_cases,
            "all_rank_span_expansion_cases": all_rank_pz,
            "empirical_annihilator_constraints": pac_constraints,
            "false_but_bounded_constraints": false_constraints,
            "uniform_syndrome_fibers": uniform_images}


def uniform_and_affine_identities():
    linear_pairs = affine_pairs = negative_affine = zero_affine = cutoffs = 0
    for n in (1, 2):
        size = 1 << (2*n)
        spaces = [space for level in subspaces(2*n) for space in level]
        chars = [[1-2*bracket(a, b, n) for b in range(size)] for a in range(size)]
        perps = {v: frozenset(x for x in range(size)
                             if all(chars[x][a] == 1 for a in v)) for v in spaces}
        cosets = {v: sorted({tuple(sorted(a ^ x for x in v)) for a in range(size)})
                  for v in spaces}
        for v in spaces:
            for w in spaces:
                kernel = v & perps[w]
                pairing_rank = dimension(v)-dimension(kernel)
                assert len({syndrome(a, basis(w), n) for a in v}) == 1 << pairing_rank
                assert pairing_rank >= dimension(v)+dimension(w)-2*n
                direct = F(sum(chars[a][b] for a in v for b in w), len(v)*len(w))
                assert direct == F(1, 1 << pairing_rank)
                linear_pairs += 1
                for va in cosets[v]:
                    a0 = min(va)
                    for wb in cosets[w]:
                        b0 = min(wb)
                        total = sum(chars[a][b] for a in va for b in wb)
                        eta = F(total, len(v)*len(w))
                        # Sum the second affine law's character first.
                        surviving = set(va) & perps[w]
                        signed = sum(chars[a][b0] for a in surviving)
                        assert eta == F(signed, len(v))
                        if surviving:
                            x0 = min(surviving)
                            assert surviving == {x0 ^ k for k in kernel}
                            expected = (F(chars[x0][b0], 1 << pairing_rank)
                                        if all(chars[k][b0] == 1 for k in kernel)
                                        else F(0))
                        else:
                            expected = F(0)
                        assert eta == expected
                        assert abs(eta) <= F(1, 1 << pairing_rank)
                        # A signed affine average still obeys the zero-return guard.
                        for c in range(n+1):
                            if dimension(v) > n+c and dimension(w) > n+c:
                                assert abs(eta) <= F(1, 1 << (2*c))
                                cutoffs += 1
                        affine_pairs += 1
                        negative_affine += eta < 0
                        zero_affine += eta == 0
    return {"uniform_subspace_pairs": linear_pairs,
            "affine_coset_pairs": affine_pairs,
            "negative_affine_averages": negative_affine,
            "zero_affine_averages": zero_affine,
            "high_rank_affine_cutoff_cases": cutoffs}


def verify_pauli_subspace():
    return {"status": "passed", "arithmetic": "exact rational and binary linear algebra",
            **geometry_and_empirical_constraints(), **uniform_and_affine_identities(),
            "scope": ("Exhaustive n=1,2 disjoint-Lagrangian, syndrome, moment, "
                      "empirical false-constraint, uniform-rank and signed affine guards; "
                      "all-n geometry, distribution-free concentration, algorithmic cost, "
                      "reference embedding and physical access remain analytic. "
                      "No arbitrary high-rank nonuniform, contamination or SPAM guarantee.")}


if __name__ == "__main__":
    print(json.dumps(verify_pauli_subspace(), sort_keys=True))
