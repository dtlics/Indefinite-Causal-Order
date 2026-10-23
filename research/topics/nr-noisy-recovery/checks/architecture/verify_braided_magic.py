"""Exact finite braid/magic algebra for NR-R17; standard library, stdout only.

General protected-resource closure, native trajectory interfaces, complete
physical phases and factory costs are proved/scoped in braided-magic.md.
"""
from fractions import Fraction as F
import json

if not __debug__:
    raise RuntimeError("Exact checks reject -O execution.")


def q(a=0, b=0):
    return F(a), F(b)


def add(a, b):
    return a[0]+b[0], a[1]+b[1]


def mul(a, b):
    return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]


def conj(a):
    return a[0], -a[1]


def scale(a, r):
    return [[mul(x, q(r)) for x in row] for row in a]


def matrix_sum(*matrices):
    n, m = len(matrices[0]), len(matrices[0][0])
    return [[sum_q(a[i][j] for a in matrices) for j in range(m)] for i in range(n)]


def sum_q(xs):
    value = q()
    for x in xs:
        value = add(value, x)
    return value


def product(a, b):
    return [[sum_q(mul(x,y) for x,y in zip(row,col))
             for col in zip(*b)] for row in a]


def adjoint(a):
    return [[conj(x) for x in col] for col in zip(*a)]


def outer(a, b):
    return [[mul(x,conj(y)) for y in b] for x in a]


def trace(a):
    return sum_q(a[i][i] for i in range(len(a)))


def tensor(a, b):
    return [[mul(x,y) for x in row_a for y in row_b]
            for row_a in a for row_b in b]


def flagged(a, b, visibility, sign, weight):
    return scale(matrix_sum(outer(a,a), outer(b,b),
                 scale(matrix_sum(outer(a,b),outer(b,a)),sign*visibility)),weight)


I = [[q(1),q()],[q(),q(1)]]
X = [[q(),q(1)],[q(1),q()]]
Y = [[q(),q(0,-1)],[q(0,1),q()]]
Z = [[q(1),q()],[q(),q(-1)]]
NX = matrix_sum(I, [[mul(q(0,-1),x) for x in row] for row in X])
NZ = matrix_sum(I, [[mul(q(0,-1),x) for x in row] for row in Z])
VU = scale(product(NZ,NX),F(1,2))
UV = scale(product(NX,NZ),F(1,2))
MP = scale(matrix_sum(VU,UV),F(1,2))
MM = scale(matrix_sum(VU,scale(UV,-1)),F(1,2))
assert product(adjoint(MP),MP) == scale(I,F(3,4))
assert product(adjoint(MM),MM) == scale(I,F(1,4))
assert MP == scale(matrix_sum(I,[[mul(q(0,-1),x) for x in row]
                               for row in matrix_sum(X,Z)]),F(1,2))
assert MM == [[mul(q(0,F(-1,2)),x) for x in row] for row in Y]

target = scale(outer([row[0] for row in MP],[row[0] for row in MP]),F(4,3))
stabilizers = []
for p in (X,Y,Z):
    for sign in (1,-1):
        stabilizers.append(scale(matrix_sum(I,scale(p,sign)),F(1,2)))
assert max(trace(product(target,s))[0] for s in stabilizers) == F(5,6)

checked_flags = 0
for nu in map(F, (0,F(1,7),F(1,2),F(97,100),1)):
    for sign in (1,-1):
        switched = flagged([row[0] for row in VU], [row[0] for row in UV],
                           nu, sign, F(1,4))
        # Ordinary data arms after fixed S-dagger; omitted common sqrt(2)
        # is included in the weight 1/8 rather than 1/4.
        ordinary = flagged([q(1),q(0,-1)], [q(1),q(1)],nu,sign,F(1,8))
        assert switched == ordinary
        probability = F(2+sign*nu,4)
        assert trace(switched) == q(probability)
        if sign == 1:
            x = 2*switched[0][1][0]/probability
            y = -2*switched[0][1][1]/probability
            z = (switched[0][0][0]-switched[1][1][0])/probability
            assert (x,y,z) == ((1+nu)/(2+nu),-(1+nu)/(2+nu),nu/(2+nu))
            assert x-y+z == 1+2*nu/(2+nu)
            assert trace(product(target,switched))[0]/probability == (5+4*nu)/(6+3*nu)
        checked_flags += 1

# Two retained same-sign impurity outcomes each have half the amplitude of
# a clean two-arm X outcome. Their combined map is half the clean outcome.
clean_plus = flagged([q(1),q(0,-1)],[q(1),q(1)],F(1),1,F(1,8))
two_impurity_plus = scale(clean_plus,F(1,2))
assert trace(two_impurity_plus) == q(F(3,8))
assert scale(two_impurity_plus,F(8,3)) == target
assert F(1)/F(3,8) == F(2)/F(3,4) == F(8,3)

loop_cases = 0
for p in (I,X,Y,Z):
    for r in (I,X,Y,Z):
        rp, pr = product(r,p), product(p,r)
        sign = 1 if rp == pr else -1
        assert pr == scale(rp,sign)
        w = [[q() for _ in range(4)] for _ in range(4)]
        for a in range(2):
            for b in range(2):
                w[a][b] = rp[a][b]
                w[2+a][2+b] = pr[a][b]
        assert w == tensor(I if sign == 1 else Z,rp)
        loop_cases += 1

print(json.dumps({
    "status":"passed", "arithmetic":"Gaussian rational fractions",
    "quarter_braid_gate_probabilities":["3/4","1/4"],
    "best_stabilizer_target_fidelity":"5/6",
    "full_flagged_state_comparisons":checked_flags,
    "physical_S_two_impurity_magic_yield":"3/8",
    "matching_mean_slot_exchange_exposure":"8/3",
    "pauli_full_loop_order_closures":loop_cases,
    "scope":"Finite exact operator and raw-state identities. Native routers, full physical Abelian phases, noise models, fault tolerance and hardware cost remain analytic assumptions; no architecture advantage certificate."
},indent=2))
