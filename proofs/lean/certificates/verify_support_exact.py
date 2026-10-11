"""Replay the paper's 25-dimensional qubit-support certificate exactly.

Python 3 standard library only. No floating point, numerical rank tolerance,
external theorem prover, or recorded PASS flag is used in the verification.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import math
import time

HERE = Path(__file__).resolve().parent
START = time.time()
data = json.loads((HERE / 'integer_support_constraints.json').read_text())
left = json.loads((HERE / 'support_left_inverse.json').read_text())
modular = json.loads((HERE / 'modular_support_inverse.json').read_text())
Z = (F(0), F(0))

def add(a, b):
    return a[0] + b[0], a[1] + b[1]

def mul(a, b):
    return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]

def conj(a):
    return a[0], -a[1]

def total(xs):
    s = Z
    for x in xs:
        s = add(s, x)
    return s

def gate(q):
    w, x, y, z = q
    return [[(F(w), F(z)), (F(y), F(x))],
            [(-F(y), F(x)), (F(w), -F(z))]]

def matmul(A, B):
    return [[total(mul(A[i][k], B[k][j]) for k in range(2))
             for j in range(2)] for i in range(2)]

def state(A, B):
    BA, AB = matmul(B, A), matmul(A, B)
    return [[BA, AB][c][t][p] for p, c, t in product(range(2), repeat=3)]

indices = list(product(range(2), repeat=7))
E = []
for p, ai, ao, bi, bo, c, t in indices:
    row = [0]*25
    row[8*ai+4*ao+2*bi+bo] = int(p == t)
    row[16+2*bi+bo] = int(p == ai and ao == t)
    row[20+2*ai+ao] = int(p == bi and bo == t)
    row[24] = int((c == 0 and p == ai and ao == bi and bo == t)
                  or (c == 1 and p == bi and bo == ai and ao == t))
    E.append(row)

R = [[tuple(map(F, x)) for x in row] for row in data['constraint_rows']]
assert len(R) == len(data['records']) == 103
assert all(len(row) == 128 for row in R)
I = gate((1, 0, 0, 0))

for n, (row, record) in enumerate(zip(R, data['records'])):
    U, V = gate(record['u']), gate(record['v'])
    for q, G in [(record['u'], U), (record['v'], V)]:
        norm_sq = sum(x*x for x in q)
        assert norm_sq > 0
        # Each supplied Gaussian-integer gate becomes unitary after division
        # by sqrt(norm_sq); these nonzero column factors do not change spans.
        for i in range(2):
            for j in range(2):
                assert total(mul(conj(G[k][i]), G[k][j]) for k in range(2)) == (
                    F(norm_sq if i == j else 0), F(0))
    ann = [tuple(map(F, x)) for x in record['annihilator']]
    assert len(ann) == 8 and any(x != Z for x in ann)
    for vector in [state(I, I), state(U, I), state(I, V), state(U, V)]:
        assert total(mul(a, x) for a, x in zip(ann, vector)) == Z, n
    linked = [mul(ann[4*p+2*c+t], mul(U[ao][ai], V[bo][bi]))
              for p, ai, ao, bi, bo, c, t in indices]
    denominator = math.lcm(*(x.denominator for a in linked for x in a))
    integral = [(int(a*denominator), int(b*denominator)) for a, b in linked]
    divisor = math.gcd(*(abs(x) for a in integral for x in a))
    assert divisor > 0
    assert [(F(a//divisor), F(b//divisor)) for a, b in integral] == row, n
    for k in range(25):
        assert total((a*E[i][k], b*E[i][k]) for i, (a, b) in enumerate(row)) == Z

L = []
for sparse in left['rows']:
    row = [0]*128
    for index, coefficient in sparse:
        row[index] += coefficient
    L.append(row)
assert len(L) == 25
for i in range(25):
    for j in range(25):
        assert sum(L[i][k]*E[k][j] for k in range(128)) == int(i == j)

G = R + [[(F(c), F(0)) for c in row] for row in L]
assert G == [[tuple(map(F, x)) for x in row] for row in modular['gaussian_matrix']]
inverse = modular['inverse_mod_five']
assert len(inverse) == 128 and all(len(row) == 128 for row in inverse)
assert all(isinstance(x, int) and 0 <= x < 5 for row in inverse for x in row)
G5 = [[(int(a)+2*int(b)) % 5 for a, b in row] for row in G]
for i in range(128):
    for j in range(128):
        assert sum(G5[i][k]*inverse[k][j] for k in range(128)) % 5 == int(i == j)

report = dict(result='PASS', arithmetic='exact integers and rational fractions',
              support_shape=[128, 25], linked_annihilator_rows=103,
              left_inverse_identity='L E = I_25',
              stacked_identity='G E = vertical_stack(0_(103,25), I_25)',
              modular_inverse='G(i -> 2) B = I_128 (mod 5)',
              characteristic_zero_rank=128, forced_support_dimension=25,
              distinct_gate_pairs=len({(tuple(r['u']), tuple(r['v'])) for r in data['records']}),
              seconds=time.time()-START)
(HERE / 'support-replay-result.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report, indent=2))
