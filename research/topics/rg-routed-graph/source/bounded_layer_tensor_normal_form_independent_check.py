"""Independent exact calibrations for the bounded necessary layer normal form.

Uses only the portable quartet fixtures for the original tensor. Checks arbitrary
nonunitary inputs (including zero and singular), and a genuinely noncommuting
private-qubit extension. The general proof is in the accompanying audit.
"""
from pathlib import Path
from itertools import product
import json
import sympy as s
from exact_fixtures import E, R, I16, I2, X, Z, WORDS, local

ROOT=Path(__file__).parent
ZERO=s.zeros(16)
# Independent support construction from spanning physical vectors.
def support(i, vectors):
    spectators=[j for j in range(4) if j!=i]
    cols=[]
    for bit in (0,1):
        for vec in vectors:
            cols.append(s.Matrix([vec[int(''.join(str(w[j]) for j in spectators),2)] if w[i]==bit else 0 for w in WORDS]))
    basis=s.Matrix.hstack(*cols)
    return basis*(basis.H*basis).inv()*basis.H
S=[support(0,[[1,0,1,0,0,0,0,0],[1,0,0,1,0,0,0,0]]),
   support(1,[[0,1,0,0,0,0,0,0],[0,0,0,0,1,1,-1,-1]]),E[2],E[3]]
def options(i):
    return [(E[i],ZERO),(E[i],E[i]),(S[i],ZERO),(S[i],E[i]),(S[i],S[i]-E[i]),(S[i],S[i])]
patterns=list(product(options(0),options(1)))

def check_tuple(U, ancilla_dim=1, verify_unitary=False):
    n=16*ancilla_dim
    eye=s.eye(n); zero=s.zeros(n)
    lift=lambda a:s.kronecker_product(a,s.eye(ancilla_dim))
    Ee=list(map(lift,E)); Rr=list(map(lift,R)); Zz=[lift(local(i,Z)) for i in range(4)]
    alpha=[Rr[i]*U[i]*Rr[i] for i in range(4)]
    W=eye
    for u in U: W=W*u
    bars=[]
    for i in range(4):
        bar=eye
        for j,u in enumerate(U):
            if i!=j:bar=bar*u
        bars.append(bar)
    # Direct physical normalized quartet, independent of Q or T.
    F=W+sum((bars[i]*(Zz[i]*U[i]*Zz[i]-U[i])*Ee[i] for i in range(4)),zero)
    count=0
    for p,q in patterns:
        Q=list(map(lift,[p[0],q[0],E[2],E[3]]))
        T=list(map(lift,[p[1],q[1],E[2],E[3]]))
        C=[a-b for a,b in zip(Q,T)]
        residual=eye-sum(Q,zero)
        A=eye-sum(T,zero)+sum((alpha[i]*T[i] for i in range(4)),zero)
        B=W*residual+sum((bars[i]*(T[i]+alpha[i]*C[i]) for i in range(4)),zero)
        assert (B*A-F).applyfunc(s.expand)==zero
        for i in range(4):assert (B*T[i]-bars[i]*T[i]).applyfunc(s.expand)==zero
        if verify_unitary:
            assert (A.H*A-eye).applyfunc(s.expand)==zero and (B.H*B-eye).applyfunc(s.expand)==zero and (F.H*F-eye).applyfunc(s.expand)==zero
        count+=1
    return count

# Dense, singular, and zero ordinary inputs are all included. No inverse is used.
ordinary=[
 [s.Matrix([[1,2],[3,4]]),s.Matrix([[2,-1],[1,3]]),s.Matrix([[1,1],[2,2]]),s.Matrix([[0,1],[-2,3]])],
 [s.zeros(2),s.Matrix([[s.I,2],[3,-s.I]]),s.Matrix([[1,0],[0,0]]),s.Matrix([[1,2],[0,1]])],
]
ordinary_checks=sum(check_tuple([local(i,a) for i,a in enumerate(t)]) for t in ordinary)

# Physical qubit 0 and its private qubit interact through an exact signed
# permutation with noncommuting 2x2 entry blocks. Layout: physical four, private.
def private_embed(gate):
    out=s.zeros(32)
    for r,w in enumerate(WORDS):
        for c,v in enumerate(WORDS):
            if w[1:]!=v[1:]:continue
            for a,b in product(range(2),repeat=2):out[2*r+a,2*c+b]=gate[2*w[0]+a,2*v[0]+b]
    return out
# SWAP times a private-controlled physical NOT. Blocks include |0><1| and
# |1><0|; their order is observable.
gate=s.zeros(4)
for physical,private in product(range(2),repeat=2):
    middle=(physical^private,private)
    dest=(middle[1],middle[0])
    gate[2*dest[0]+dest[1],2*physical+private]=1
blocks=[gate[2*a:2*a+2,2*b:2*b+2] for a,b in product(range(2),repeat=2)]
assert any(a*b!=b*a for a in blocks for b in blocks)
private_inputs=[private_embed(gate),s.kronecker_product(local(1,X),I2),
                s.kronecker_product(local(2,(3*I2+4*s.I*X)/5),I2),
                s.kronecker_product(local(3,Z),I2)]
private_checks=check_tuple(private_inputs,2,True)

# Arithmetic bound proof: for k>=1 branches, sum d_b^2+epsilon <=257^k.
# Maximal LHS has all d_b=16 and epsilon=1.
assert all(256*k+1<=257**k for k in range(1,33))
assert 16*(2**32)==2**36
result={
 'status':'PASS',
 'aggregate_patterns':len(patterns),
 'ordinary_nonunitary_BA_checks':ordinary_checks,
 'noncommuting_private_qubit_BA_and_unitarity_checks':private_checks,
 'original_source_branches_max':10,
 'retained_layers_max':7,
 'retained_branch_incidences_loose_max':224,
 'complex_coefficients_per_layer_loose_bound':'256*257^32',
 'real_layer_coefficients_total_loose_bound':'3584*257^32',
 'recurrent_exchange_dimension_bound':2**36,
 'scope':'Exact finite calibrations only; neither a graph realization nor a finite complete-unitarity ancilla cutoff.'
}
(ROOT/'bounded_layer_tensor_normal_form_independent_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
