"""Exact checks for the full complex safe-product variety and scalar orbit-hub obstruction.

Run from this directory with Python/SymPy. The mathematical necessity argument is in
continuous_product_classification.md. All calculations use the portable quartet
fixtures; no floating-point tolerance, enlarged interface, or merged filler is used.
"""
from itertools import product, combinations
from pathlib import Path
from fractions import Fraction
import json
import sympy as s
from exact_fixtures import E, I16, I2, X, Z, WORDS, tensor, local

ROOT = Path(__file__).parent
ZERO = s.zeros(16)
RAYS = {'0': s.Matrix([1, 0]), '1': s.Matrix([0, 1]),
        '+': s.Matrix([1, 1]), '-': s.Matrix([1, -1])}
LINES = ['0*01', '1*-+', '0*10', '1*+-', '01*0', '011*',
         '11+*', '11*-', '*1+0']
POINT = '-1-1'
Vs = [I16 - 2 * sum((o[i] * E[i] for i in range(4)), ZERO) for o in WORDS]
D0 = I16 - 2 * sum((local(i, s.diag(0, 1)) * E[i] for i in range(4)), ZERO)

def expanded_zero(matrix):
    return all(s.expand(z) == 0 for z in matrix)

def word(w, free=None):
    return tensor([free if x == '*' else RAYS[x] for x in w])

def minors(v):
    """All one-vs-rest flattening minors; their vanishing is equivalent to productness."""
    for i in range(4):
        inds0 = [j for j, w in enumerate(WORDS) if w[i] == 0]
        inds1 = [j for j, w in enumerate(WORDS) if w[i] == 1]
        for j, k in combinations(range(8), 2):
            yield s.expand(v[inds0[j]] * v[inds1[k]] - v[inds0[k]] * v[inds1[j]])

def is_product_integer(v):
    """Exact rank-one tensor test by reconstruction from any nonzero pivot."""
    p = next((j for j, z in enumerate(v) if z), None)
    assert p is not None
    anchor = v[p]
    local_flips = [v[p ^ (1 << i)] for i in range(4)]
    for j, z in enumerate(v):
        diff = j ^ p
        positions = [i for i in range(4) if diff & (1 << i)]
        if len(positions) > 1:
            rhs = 1
            for i in positions:
                rhs *= local_flips[i]
            if z * anchor ** (len(positions)-1) != rhs:
                return False
    return True

def proportional(u, v):
    return u[0] * v[1] == u[1] * v[0]

fixed = {'0': (1, 0), '1': (0, 1), '+': (1, 1), '-': (1, -1)}
def in_classification(xs):
    a, b, c, d = xs
    h = 2*a[0]*c[0]*d[1] + a[1]*(c[0]-c[1])*(d[0]+d[1])
    if b[1] == 0 and h == 0:
        return True
    for pat in LINES + [POINT]:
        if all(t == '*' or proportional(x, fixed[t]) for x, t in zip(xs, pat)):
            return True
    return False

assert all(e == e.H and e*e == e and e.rank() == 2 for e in E)
assert all(E[i]*E[j] == ZERO for i, j in combinations(range(4), 2))
assert D0 == D0.H and D0*D0 == I16

# Exact symbolic sufficiency for every point of all nine projective lines.
x, y = s.symbols('x y')
line_minor_count = 0
for pat in LINES:
    v = word(pat, s.Matrix([x, y]))
    for V in Vs:
        mm = list(minors(V*v))
        assert all(z == 0 for z in mm), pat
        line_minor_count += len(mm)
assert all(z == 0 for V in Vs for z in minors(V*word(POINT)))

# Exact symbolic sufficiency for the whole projective surface b=0, h=0.
# Every flattening minor belongs to its principal ideal (h), including base loci
# that a single rational parametrization would omit.
a0,a1,c0,c1,d0,d1 = vars6 = s.symbols('a0 a1 c0 c1 d0 d1')
a = s.Matrix([a0,a1]); c = s.Matrix([c0,c1]); d = s.Matrix([d0,d1])
h = 2*a0*c0*d1 + a1*(c0-c1)*(d0+d1)
v = tensor([a, RAYS['0'], c, d])
G = s.groebner([h], *vars6, domain=s.QQ)
surface_minor_count = 0
for V in Vs:
    for z in minors(V*v):
        assert G.reduce(z)[1] == 0
        surface_minor_count += 1
# Its defining polynomial is irreducible over C: linear in a, with coprime
# coefficient forms. The check establishes the required coprimality exactly.
assert s.gcd(2*c0*d1, (c0-c1)*(d0+d1)) == 1

# E1's active b=0 transformation is product on every c,d, without imposing h.
swap_perp = tensor([a, RAYS['0'], s.Matrix([d1,-d0]), s.Matrix([-c1,c0])])
assert expanded_zero((I16-2*E[0])*v - swap_perp)

# The only E2-active safe families, with arbitrary complex b, are exchanged.
b = s.Matrix([x,y]); g0 = tensor([RAYS['0'],b,RAYS['0'],RAYS['1']])
g1 = tensor([RAYS['1'],b,RAYS['-'],RAYS['+']])
assert expanded_zero((I16-2*E[1])*g0 + g1/2)
assert expanded_zero((I16-2*E[1])*g1 + 2*g0)
for i in [0,2,3]:
    assert expanded_zero(E[i]*g0) and expanded_zero(E[i]*g1)
# Their changing local rays cannot share a single orthonormal frame.
c_overlap_squared = s.Rational(1,2)
d_overlap_squared = s.Rational(1,2)
assert (RAYS['0'].H*RAYS['-'])[0] == 1
assert (RAYS['1'].H*RAYS['+'])[0] == 1

# Verify the normalization and exact raw active coefficients at ports 3/4.
us = [s.Matrix(2, 2, s.symbols(f'u{i}_0:4')) for i in range(4)]
W = tensor(us)
Fraw = W - 2*sum((local(i,s.diag(0,1))*W*E[i] for i in range(4)), ZERO)
for i in [2,3]:
    assert D0*E[i] == E[i]*D0
    assert expanded_zero(Fraw*E[i] - local(i,Z)*W*E[i])
# Verify the coefficient identity behind scalar-marker rigidity directly.
for oi,o in enumerate(WORDS):
    assert expanded_zero(Fraw[oi,:] - (W*Vs[oi])[oi,:])

# A supplementary complete rational-grid census checks the analytic
# classification against all sixteen V_o, not merely the individual generators.
grid = [(1,0),(0,1),(1,1),(1,-1),(1,2),(2,1)]
E8 = [[[int(8*e[r,c]) for c in range(16)] for r in range(16)] for e in E]
def tensor_int(xs):
    out = [1]
    for x in xs:
        out = [u*z for u in out for z in x]
    return out
checked = safe_count = 0
for xs in product(grid, repeat=4):
    v = tensor_int(xs)
    ev = [[sum(row[j]*v[j] for j in range(16)) for row in e] for e in E8]
    okay = True
    for o in WORDS:
        out = [8*v[j]-2*sum(o[i]*ev[i][j] for i in range(4)) for j in range(16)]
        if not is_product_integer(out):
            okay = False
            break
    assert okay == in_classification(xs), xs
    checked += 1
    safe_count += int(okay)
pauli_safe = [''.join(w) for w in product('01+-', repeat=4)
              if in_classification([fixed[x] for x in w])]
previous = json.loads((ROOT/'safe_pauli_orbit_table.json').read_text())['safe_rays']
assert pauli_safe == previous
surface_pauli = [w for w in pauli_safe if w[1]=='0' and
                 2*fixed[w[0]][0]*fixed[w[2]][0]*fixed[w[3]][1] +
                 fixed[w[0]][1]*(fixed[w[2]][0]-fixed[w[2]][1])*
                 (fixed[w[3]][0]+fixed[w[3]][1]) == 0]
assert s.Matrix.hstack(*[word(w) for w in surface_pauli]).rank() == 7
assert s.Matrix.hstack(*[word(w) for w in pauli_safe]).rank() == 16

report = {
    'result': 'One irreducible projective surface, nine projective lines, one isolated point',
    'surface': {'equations': ['b1=0', '2*a0*c0*d1+a1*(c0-c1)*(d0+d1)=0'],
                'complex_dimension': 2, 'linear_span_dimension': 7,
                'all_orbit_minors_verified_modulo_surface_ideal': surface_minor_count},
    'projective_lines': LINES,
    'all_line_orbit_minors_verified_identically': line_minor_count,
    'isolated_point': POINT,
    'rational_grid': {'tested': checked, 'safe': safe_count, 'classification_mismatches': 0},
    'original_pauli_census_reproduced': len(pauli_safe),
    'full_safe_variety_linear_span_dimension': 16,
    'E2_active_families': ['0*01','1*-+'],
    'E2_active_reflection_unnormalized': ['0b01 -> -(1b-+)/2', '1b-+ -> -2*(0b01)'],
    'E2_active_families_annihilated_by_E1_E3_E4': True,
    'port3_changing_rays_overlap_squared': str(c_overlap_squared),
    'port4_changing_rays_overlap_squared': str(d_overlap_squared),
    'raw_normalization_and_symbolic_port3_port4_active_coefficients_verified': True,
    'no_hub_result': 'Every direct scalar orbit-table hub from a full safe product basis fails independent native validity, even with arbitrary complex local frames',
    'scope': 'Fixed dimension-16 boundary; complete independent original-qubit inclusions; the stated product-orbit-table architecture. No claim about arbitrary routed hosts.'
}
(ROOT/'continuous_product_classification_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
