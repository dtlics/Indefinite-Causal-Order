"""Exact linear-span obstruction for instantaneous moving TIP encoding.

This is a finite declared-star identity, not a bound on compiled gates.
"""
from fractions import Fraction as F
from pathlib import Path
import json

if not __debug__:
    raise RuntimeError("Run the exact moving-encoding fixture without -O.")

def eye(n):
    return [[F(i==j) for j in range(n)] for i in range(n)]
def unit(n,i,j):
    return [[F(r==i and c==j) for c in range(n)] for r in range(n)]
def transpose(a):
    return [list(x) for x in zip(*a)]
def mm(a,b):
    return [[sum((a[i][k]*b[k][j] for k in range(len(b))),F(0))
             for j in range(len(b[0]))] for i in range(len(a))]
def kron(a,b):
    return [[x*y for x in ar for y in br] for ar in a for br in b]
def add(a,b):
    return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def scale(a,s):
    return [[s*x for x in row] for row in a]

def verify():
    # Ordering: star b,u,v, each tensored with D0,D1.
    i3,i2=eye(3),eye(2)
    pb=unit(3,0,0)
    p0=add(unit(3,1,1),unit(3,2,2))
    u0=i2
    u1=[[F(3,5),F(-4,5)],[F(4,5),F(3,5)]]
    c=add(kron(p0,u0),kron(pb,u1))
    assert mm(c,transpose(c))==eye(6)
    hj=scale(add(kron(unit(3,1,0),i2),kron(unit(3,0,1),i2)),F(1,2))
    actual=mm(mm(c,hj),transpose(c))
    lower=mm(u0,transpose(u1))
    expected=scale(add(kron(unit(3,1,0),lower),
                       kron(unit(3,0,1),transpose(lower))),F(1,2))
    assert actual==expected
    row,col=3,0  # u,D1 <- b,D0
    assert actual[row][col]==F(-2,5)
    # A generous complex linear span: arbitrary scalar star diagonals,
    # arbitrary common helper matrices, number-number interaction, and
    # both independent scalar pump directions for u and v.
    available=[kron(unit(3,j,j),i2) for j in range(3)]
    available += [kron(i3,unit(2,k,l)) for k in range(2) for l in range(2)]
    available += [kron(pb,unit(2,1,1))]
    available += [kron(unit(3,j,0),i2) for j in (1,2)]
    available += [kron(unit(3,0,j),i2) for j in (1,2)]
    assert all(a[row][col]==0 for a in available)
    # Derivative and retained-chi terms remain star-block-diagonal.
    conditional=[kron(p,unit(2,k,l)) for p in (p0,pb)
                 for k in range(2) for l in range(2)]
    assert all(a[row][col]==0 for a in conditional)
    nd=unit(2,1,1)
    transformed_chi=mm(mm(c,kron(pb,nd)),transpose(c))
    assert transformed_chi==kron(pb,mm(mm(u1,nd),transpose(u1)))
    assert transformed_chi[row][col]==0
    overlap=u1[0][0]
    return {"status":"passed","codeword_distinguishability":str(1-overlap*overlap),
            "edge_lower_block":[[str(x) for x in r] for r in lower],
            "missing_matrix_element":"<u,D1|H|b,D0>",
            "required_element_at_unit_pump":str(actual[row][col]),
            "available_span_generators":len(available),
            "all_available_and_conditional_terms_have_zero_element":True,
            "scope":"Exact instantaneous declared-star linear-span obstruction only; no finite-control synthesis, minimum gate time, noise-model or physical-device certification."}

if __name__=="__main__":
    print(json.dumps(verify(),indent=2))
