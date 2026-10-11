"""Exact all-no-path calibration in the literal binary Lugano host and reverse.

Checks native full-matrix coefficient identities at nonidentity rational
baselines, including both native lab siblings and all auxiliary vertices.
The theorem is proved in no_path_future_marker_proof.md; this is calibration.
"""
from itertools import product
from pathlib import Path
import json
import sympy as s

ROOT = Path(__file__).parent
BITS = list(product((0, 1), repeat=3))
def w(o):
    a, b, c = o
    return (b*(1-c), (1-a)*c, a*(1-b))
def idx(o): return 4*o[0] + 2*o[1] + o[2]
LABS = [('L', i, x) for i, x in product(range(3), (0, 1))]
HUBS = [('H', *o) for o in BITS]
D = ('D',)
NODES = LABS + HUBS + [D]
def vertex(b): return (b[0], b[1]) if b[0] == 'L' else b[0]
def status(o): return frozenset([D, ('H', *o), *(('L', i, w(o)[i]) for i in range(3))])

forward = {}
for f in product((0, 1), repeat=6):
    sols = [o for o in BITS if all(o[i] == f[2*i+w(o)[i]] for i in range(3))]
    assert len(sols) == 1
    forward[f] = sols[0]
# In reverse the only sector-choice coordinate is the decoder's input o.
# Each o gives precisely its section. All hub branches are scalar.
edges = set()
for f, o in forward.items():
    for k in range(6):
        ff = list(f); ff[k] ^= 1
        for b in status(o) ^ status(forward[tuple(ff)]):
            edges.add((LABS[k], b, 'green'))
for o, p in product(BITS, repeat=2):
    for b in status(o) ^ status(p): edges.add((b, D, 'red'))
# Strong parent test: enumerate the three types of internal links. Each
# sector is one-dimensional, and conditioned on a co-occurring pair its
# index tuple is singleton. No solid branch edge is present.
links = []
for i in range(3):
    links.append((("L", i), "H", lambda o, i=i: (o[i],)))
    links.append(("H", ("L", i), lambda o, i=i: (w(o)[i],)))
links.append(("H", "D", lambda o: o))
for src, dst, link_value in links:
    for a, b in product(NODES, repeat=2):
        if vertex(a) != src or vertex(b) != dst: continue
        values = {link_value(o) for o in BITS if a in status(o) and b in status(o)}
        assert len(values) <= 1
reach = {a: {a} for a in NODES}
for a, b, col in edges: reach[a].add(b)
for k in NODES:
    for a in NODES:
        if k in reach[a]: reach[a] |= reach[k]
comps = {frozenset(b for b in NODES if b in reach[a] and a in reach[b]) for a in NODES}
recurrent = []
for cc in comps:
    ee = [e for e in edges if e[0] in cc and e[1] in cc]
    if len(cc)>1 or any(a == b for a, b, col in ee):
        assert {col for a, b, col in ee} == {'green'}
        recurrent.append(cc)
assert recurrent == [frozenset(('L', i, 0) for i in range(3))]
assert set().union(*(status(o) for o in BITS)) == set(NODES)

R = s.Matrix([[3, -4], [4, 3]])/5
U = {(i, x): R**(1+2*i+x) for i, x in product(range(3), (0, 1))}
h = {o: s.Integer((-1)**(idx(o)%3)) for o in BITS}
Dec = s.kronecker_product(R, R.T, R**2)

def accepts(b, o):
    return b is None or b in status(o)

def raw(mark_b=None, mark_c=None, mat=None):
    uu = dict(U); hh = dict(h); dd = Dec
    if mark_c is not None:
        if mark_c[0] == 'L': uu[mark_c[1], mark_c[2]] = mat
        elif mark_c[0] == 'H': hh[tuple(mark_c[1:])] = mat[0, 0]
        else: dd = mat
    middle = s.Matrix(8, 8, lambda a, p: (
        hh[BITS[a]] * s.prod(uu[i, w(BITS[a])[i]][BITS[a][i], BITS[p][i]] for i in range(3))
        if accepts(mark_b, BITS[a]) and accepts(mark_c, BITS[a]) else 0))
    return dd * middle

def dim(b): return 2 if b[0] == 'L' else 1 if b[0] == 'H' else 8
G0 = raw()
assert G0.T*G0 == s.eye(8) and G0*G0.T == s.eye(8)
coeff = {}
for c in NODES:
    for i, j in product(range(dim(c)), repeat=2):
        mat = s.zeros(dim(c)); mat[i, j] = 1
        coeff[c, i, j] = raw(mark_c=c, mat=mat)
marks = {b: raw(mark_b=b) for b in NODES}

out = {'status': 'PASS', 'boundary_dimension': 8,
       'full_forward_choice_count': len(forward), 'reverse_choice_count': len(BITS),
       'globally_reachable_branch_count': len(NODES), 'solid_edges': 0,
       'green_edges': sum(col == 'green' for _, _, col in edges),
       'red_edges': sum(col == 'red' for _, _, col in edges),
       'nonidentity_rational_native_baselines': True, 'cases': []}
for rev in (False, True):
    pair_count = 0; basis_count = 0; failures_on_reachable = []
    for b, c in product(NODES, repeat=2):
        if vertex(b) == vertex(c): continue
        has_path = b in reach[c] if rev else c in reach[b]
        pb = G0*marks[b].T if rev else G0.T*marks[b]
        assert pb.T == pb and pb*pb == pb
        if not has_path: pair_count += 1
        for i, j in product(range(dim(c)), repeat=2):
            mat = s.zeros(dim(c)); mat[i, j] = 1
            bc_raw = raw(mark_b=b, mark_c=c, mat=mat)
            rhoc = G0*coeff[c, i, j].T if rev else G0.T*coeff[c, i, j]
            bc = G0*bc_raw.T if rev else G0.T*bc_raw
            defect = bc - pb*rhoc
            if not has_path:
                basis_count += 1
                assert defect == s.zeros(8), (rev, b, c, i, j)
            elif defect != s.zeros(8) and not failures_on_reachable:
                failures_on_reachable.append({'b': list(b), 'c': list(c),
                    'matrix_unit': [i, j], 'squared_HS_defect': str(s.trace(defect.T*defect))})
    out['cases'].append({'direction': 'reverse' if rev else 'forward',
        'distinct_vertex_no_path_pairs': pair_count, 'matrix_unit_identities': basis_count,
        'reachable_pair_negative_control': failures_on_reachable})
    print(out['cases'][-1], flush=True)
# The reverse recurrent SCC must furnish a negative control: falsely
# removing the path hypothesis would claim fixed future markers there.
assert out['cases'][1]['reachable_pair_negative_control']
(ROOT/'no_path_lugano_checks.json').write_text(json.dumps(out, indent=2)+'\n')
print(json.dumps(out, indent=2), flush=True)
