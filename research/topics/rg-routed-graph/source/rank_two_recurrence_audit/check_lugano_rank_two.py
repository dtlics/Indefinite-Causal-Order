"""Independent exact rank/edge/pair calibration for the rank-two obstruction.

No proof dependency or previous check script is imported.  Matrices have
integer entries and dimension eight; all comparisons are exact.
"""
from itertools import product, combinations
from pathlib import Path
import json
import numpy as np

ROOT = Path(__file__).parent
BITS = list(product(range(2), repeat=3))
LABS = [("L", i, x) for i, x in product(range(3), range(2))]
I = np.eye(2, dtype=np.int64)
I8 = np.eye(8, dtype=np.int64)
ZERO = np.zeros((2, 2), dtype=np.int64)

def w(o):
    a, b, c = o
    return b * (1-c), (1-a) * c, a * (1-b)

def status(o):
    return frozenset([("H", *o), ("D",), *[("L", i, w(o)[i]) for i in range(3)]])

def native(tup):
    out = np.zeros((8, 8), dtype=np.int64)
    for r, o in enumerate(BITS):
        for q, p in enumerate(BITS):
            out[r, q] = np.prod([tup[i][w(o)[i]][o[i], p[i]] for i in range(3)])
    return out

BASE = [[I, I] for _ in range(3)]
assert np.array_equal(native(BASE), I8)
units = []
for x, r, q in product(range(2), range(2), range(2)):
    a = np.zeros((2, 2), dtype=np.int64)
    a[r, q] = 1
    units.append((x, [a if x == y else ZERO for y in range(2)]))

def single(i, a):
    t = BASE.copy()
    t[i] = a
    return native(t)

def pair(i, j, a, b):
    t = BASE.copy()
    t[i], t[j] = a, b
    return native(t)

P = {(i, x): single(i, [I if y == x else ZERO for y in range(2)])
     for i, x in product(range(3), range(2))}
for p in P.values():
    assert np.array_equal(p @ p, p) and np.array_equal(p.T, p)

# Full forward native choice vectors include every dormant branch choice.
forward = {}
for choices in product(range(2), repeat=6):
    solutions = [o for o in BITS if all(o[i] == choices[2*i+w(o)[i]] for i in range(3))]
    assert len(solutions) == 1
    forward[choices] = solutions[0]
edges = set()
for choices, o in forward.items():
    for k, source in enumerate(LABS):
        flipped = list(choices)
        flipped[k] ^= 1
        p = forward[tuple(flipped)]
        # Own status is invariant, including dormant input coordinates.
        assert (source in status(o)) == (source in status(p))
        if source not in status(o):
            assert o == p
        for target in status(o) ^ status(p):
            assert source in status(o) and source in status(p)
            edges.add((source, target, "green"))
# Decoder's complete reverse choice is the full tuple o; all other reverse
# choice domains are singleton. Each reverse choice determines one section.
for o, p in product(BITS, repeat=2):
    for changed in status(o) ^ status(p):
        edges.add((changed, ("D",), "red"))

def recurrent_components(es):
    nodes = set().union(*(status(o) for o in BITS))
    reach = {n: {n} for n in nodes}
    for a, b, _ in es:
        reach[a].add(b)
    for k in nodes:
        for a in nodes:
            if k in reach[a]:
                reach[a] |= reach[k]
    components = {frozenset(b for b in nodes if b in reach[a] and a in reach[b]) for a in nodes}
    recurrent = []
    for component in components:
        internal = [(a,b,c) for a,b,c in es if a in component and b in component]
        if len(component) > 1 or any(a == b for a,b,c in internal):
            colors = {c for a,b,c in internal}
            assert colors in [{"green"}, {"red"}]
            recurrent.append((component, next(iter(colors))))
    return recurrent

cycles = recurrent_components(edges)
assert cycles == [(frozenset(("L", i, 0) for i in range(3)), "green")]
reverse_edges = {(b,a,{"green":"red","red":"green"}[c]) for a,b,c in edges}
reverse_cycles = recurrent_components(reverse_edges)
assert reverse_cycles == [(cycles[0][0], "red")]
branch_report = []
for i,x in product(range(3), range(2)):
    rank = int(np.trace(P[i,x]))
    recurrent = ("L",i,x) in cycles[0][0]
    assert rank == (6 if x == 0 else 2)
    assert not (rank == 2 and recurrent)
    branch_report.append({"branch":["L",i,x],"rank":rank,"native_dimension":2,"green_recurrent":recurrent,"red_reversed_recurrent":recurrent})

# Each whole-vertex pair has a commuting two-order comparison. Exhaust the
# two natural spectator-bit sectors and verify on all 64 direct-sum matrix
# coefficient pairs, rather than just unitary or phase samples.
pair_report = []
for i,j in combinations(range(3),2):
    k = next(t for t in range(3) if t not in (i,j))
    candidates = [np.diag([int(o[k] == bit) for o in BITS]) for bit in range(2)]
    good = []
    for bit,K in enumerate(candidates):
        valid = True
        for _,a in units:
            alpha = single(i,a)
            valid &= np.array_equal(K @ alpha, alpha @ K)
            for _,b in units:
                beta = single(j,b)
                valid &= np.array_equal(K @ beta, beta @ K)
                valid &= np.array_equal(pair(i,j,a,b), alpha @ beta @ K + beta @ alpha @ (I8-K))
        if valid:
            good.append(bit)
    assert len(good) == 1
    K = candidates[good[0]]
    # Reversal transposes physical contraction and every local matrix;
    # taking I-K is the correct comparison for the opposite order.
    for _,a in units:
        for _,b in units:
            ar,br = [z.T for z in a],[z.T for z in b]
            red = pair(i,j,ar,br).T
            alpha,beta = single(i,ar).T,single(j,br).T
            assert np.array_equal(red,alpha @ beta @ (I8-K) + beta @ alpha @ K)
    # Same-SCC status can vary conditional on a losing branch because its
    # support has multiplicity three. The rank-two branch is not recurrent.
    assert int(np.trace(P[i,0] @ P[j,0])) == 4
    assert int(np.trace(P[i,0] @ (I8-P[j,0]))) == 2
    pair_report.append({"vertices":[i,j],"comparison_spectator":k,"comparison_bit":good[0],"whole_native_coefficient_pairs":64,"same_scc_intersection_rank":4,"same_scc_negative_rank":2})

report = {"status":"PASS","boundary_dimension":8,"complete_forward_choices":len(forward),"complete_reverse_choices":8,"consistent_sections":8,"dormant_and_own_choice_independence":True,"green_and_red_reversed_weak_loops":True,"rank_two_native_branches_all_acyclic":True,"branch_supports":branch_report,"whole_native_pair_comparisons":pair_report,"scope":"Exact calibration of both colors and all native pair coefficients. The general theorem is proved in the accompanying audit, not inferred from this finite example."}
(ROOT / "lugano_rank_two_checks.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(report,indent=2))
