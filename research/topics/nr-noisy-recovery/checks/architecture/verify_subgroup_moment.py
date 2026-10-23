"""Exact finite checks for NR-R08 random-stabilizer subgroup-moment estimation.

All Lagrangians are enumerated for n=2,3,4. Universal sampling, access
and moment inequalities remain analytic in architecture-baselines.md.
"""

from fractions import Fraction as F
import json

if not __debug__:
    raise RuntimeError("Run exact subgroup-moment checks without -O.")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def bracket(a, b, n):
    mask = (1 << n) - 1
    return (((a & mask) & (b >> n)).bit_count() + ((b & mask) & (a >> n)).bit_count()) & 1


def span(basis):
    result = (0,)
    for v in basis:
        require(v not in result, "dependent supplied basis")
        result = tuple(sorted(result + tuple(v ^ u for u in result)))
    return result


def lagrangians(n):
    spaces = {(0,)}
    ambient = 1 << (2 * n)
    for _ in range(n):
        next_spaces = set()
        for space in spaces:
            present = set(space)
            # Check all members; spans are tiny and this avoids a basis convention.
            for v in range(1, ambient):
                if v in present or any(bracket(v, u, n) for u in space):
                    continue
                extension = tuple(sorted(space + tuple(v ^ u for u in space)))
                next_spaces.add(extension)
        spaces = next_spaces
    expected = 1
    for j in range(1, n + 1):
        expected *= (1 << j) + 1
    require(len(spaces) == expected, "Lagrangian enumeration count")
    return sorted(spaces)


def standard_subspace(n, symplectic_pairs):
    basis = []
    for j in range(symplectic_pairs):
        basis.extend((1 << j, 1 << (n + j)))
    for j in range(symplectic_pairs, n - symplectic_pairs):
        basis.append(1 << j)
    require(len(basis) == n, "rank-n subspace")
    return span(basis)


def check_case(n, s, all_l):
    d = 1 << n
    v = standard_subspace(n, s)
    vset = set(v)
    eta = F(sum(1 - 2 * bracket(a, b, n) for a in v for b in v), d * d)
    require(eta == F(1, 1 << (2 * s)), "symplectic-rank incompatibility")
    sum_second = sum_fourth = 0
    for ell in all_l:
        x = len(vset.intersection(ell))
        sum_second += x * x
        sum_fourth += x**4
        # The observable syndrome annihilator is L intersect V-perp.
        annihilator = sum(all(bracket(a, b, n) == 0 for a in v) for b in ell)
        require(annihilator == x, "equal rank-n intersection dimensions")
    second, fourth = F(sum_second, len(all_l)), F(sum_fourth, len(all_l))
    predicted = 1 + F(3 * (d - 1), d + 1) + (
        (1 + eta) * d * d / 2 - 3 * d + 2
    ) / ((d + 1) * (F(d, 2) + 1))
    require(second == predicted, "second-moment eta formula")
    require(fourth <= 270, "uniform fourth moment")
    return {"n": n, "symplectic_rank": 2 * s, "eta": str(eta), "second_moment": str(second), "fourth_moment": str(fourth)}


def verify_subgroup_moment():
    cases, counts = [], {}
    for n in (2, 3, 4):
        all_l = lagrangians(n)
        counts[str(n)] = len(all_l)
        d = 1 << n
        contain_one = sum(1 in ell for ell in all_l)
        contain_pair = sum(1 in ell and 2 in ell for ell in all_l)
        require(F(contain_one, len(all_l)) == F(1, d + 1), "one-vector containment")
        require(F(contain_pair, len(all_l)) == F(1, (d + 1) * (d // 2 + 1)), "isotropic-plane containment")
        for s in range(n // 2 + 1):
            cases.append(check_case(n, s, all_l))
    require(1 + 15 + 70 + 120 + 64 == 270, "Gaussian-binomial moment sum")
    return {"status": "passed", "lagrangian_counts": counts, "cases": cases,
            "scope": "Finite exact subspace/annihilator/moment guards; all-n moment and sampling proofs remain analytic."}


if __name__ == "__main__":
    print(json.dumps(verify_subgroup_moment(), sort_keys=True))
