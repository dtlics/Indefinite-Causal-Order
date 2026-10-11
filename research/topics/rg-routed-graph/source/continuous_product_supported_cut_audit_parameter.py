"""Parameter proof certificate for the exact quartet cut K_{1,2}, and a native auxiliary extension."""
from pathlib import Path
import json
import sympy as s
from exact_fixtures import E,I16,I2,X,Y,Z,WORDS,tensor,local
ROOT=Path(__file__).parent
zero=s.zeros(16)
Vs=[I16-2*sum((o[i]*E[i] for i in range(4)),zero) for o in WORDS]
D0=s.Matrix.vstack(*[Vs[k][k,:] for k in range(16)])

def F(us):
    W=tensor(us)
    return s.Matrix.vstack(*[(W[k,:]*Vs[k]) for k in range(16)])*D0

def zero_poly(m):return all(s.expand(x)==0 for x in m)

us=[s.Matrix(2,2,s.symbols(f't{i}_0:4')) for i in range(4)]
W=tensor(us)
FF=F(us)
deltas=[Z*u*Z-u for u in us]
normal=W+sum((tensor([I2 if j==i else us[j] for j in range(4)])*local(i,deltas[i])*E[i]
              for i in range(4)),zero)
assert zero_poly(FF-normal)
Q=tensor([I2,I2,s.Matrix([[1,-1],[-1,1]])/2,s.diag(0,1)])
assert Q==Q.H and Q*Q==Q and Q.rank()==4
assert E[2]*Q==zero and E[3]*Q==zero
WL=tensor([us[0],us[1],I2,I2]);WR=tensor([I2,I2,us[2],us[3]])
FL=F([us[0],us[1],I2,I2]);FR=F([I2,I2,us[2],us[3]])
assert zero_poly(Q*WL-WL*Q)
for j in [2,3]:
    assert zero_poly(FL*E[j]-WL*E[j])
assert zero_poly(FR*Q-WR*Q)
correction=sum((tensor([I2 if k==j else us[k] for k in range(4)])*local(j,deltas[j])*E[j]
                for j in [2,3]),zero)
assert zero_poly(FF-WR*FL-correction)
print('Structural all-parameter identities PASS.',flush=True)

# A separate determinant-cleared direct check of F F_L† Q=F_R Q.
# Every F_L entry is degree one in each of U1,U2. Replacing conjugate entries
# by transposed adjugate entries therefore multiplies F_L† by det(U1)det(U2).
sub={s.conjugate(us[i][r,c]):us[i].adjugate()[c,r]
     for i in [0,1] for r in range(2) for c in range(2)}
FL_adj_cleared=FL.H.xreplace(sub)
assert not any(e.has(s.conjugate) for e in FL_adj_cleared)
K=tensor([I2,I2,s.Matrix([1,-1]),s.Matrix([0,1])])
assert K.shape==(16,4) and K.rank()==4
assert Q*K==K
DD=us[0].det()*us[1].det()
assert zero_poly(FF*FL_adj_cleared*K-DD*FR*K)
print('Direct determinant-cleared four-query cut identity PASS.',flush=True)

# The exact Pauli upper-bound space is this same cylinder, not only the same rank.
ref=next(x for x in json.loads((ROOT/'auxiliary_supported_cut_spaces_checks.json').read_text())
         if x['before_queries']==[1,2])
old=s.Matrix.hstack(*[s.Matrix([s.sympify(x) for x in col]) for col in ref['basis']])
assert old.row_join(K).rank()==4

# Concrete independent auxiliary-ancilla exercise of the new M4 direct-sum C
# interface. The active M4 block is fully coupled to its own qubit ancilla via
# an 8x8 SWAP; the passive scalar block receives an independent Pauli Y there.
rot=[(3*I2+4*s.I*p)/5 for p in [X,Y,Z,X]]
f=F(rot).applyfunc(s.expand);fl=F([rot[0],rot[1],I2,I2]).applyfunc(s.expand);fr=F([I2,I2,rot[2],rot[3]]).applyfunc(s.expand)
assert (f.H*f).applyfunc(s.expand)==I16
assert (f*fl.H*Q-fr*Q).applyfunc(s.expand)==zero
print('Exact mixed-rotation scalar cut check PASS.',flush=True)
B=K/s.sqrt(2)
assert B.H*B==s.eye(4) and B*B.H==Q
swap=s.zeros(8)
for i in range(8):
    a,b,c=(i>>2)&1,(i>>1)&1,i&1
    j=(c<<2)+(b<<1)+a
    swap[j,i]=1
lift=s.kronecker_product(B,I2)
active=lift*swap*lift.H
amplified=s.kronecker_product(fr,I2)*active*s.kronecker_product(fl,I2)+s.kronecker_product(f-fr*Q*fl,Y)
amplified=amplified.applyfunc(s.expand)
assert (amplified.H*amplified-s.eye(32)).applyfunc(s.expand)==s.zeros(32)
print('Independent auxiliary private-ancilla 32x32 exact test PASS.',flush=True)

report={'status':'PASS','partition':{'before':[1,2],'after':[3,4]},
        'all_context_cut_space':'I_1 tensor I_2 tensor |-1><-1| on factors 3,4 (normalized projector)',
        'all_context_cut_space_rank':4,
        'parameter_proof':'Structural physical-cylinder identities plus a separate determinant-cleared symbolic cut identity',
        'generic_complex_query_matrix_entries':16,
        'direct_cut_columns_verified_symbolically':4,
        'matches_exact_Pauli_upper_bound_subspace':True,
        'native_auxiliary_algebra':'M4 direct-sum C',
        'auxiliary_extension':'G(a direct-sum b,U)=F_R a F_L + b*(F-F_R Q F_L)',
        'origin_auxiliary_representation':'a+b*(I-Q)',
        'active_auxiliary_multiplicity':1,
        'passive_scalar_multiplicity':12,
        'independent_auxiliary_private_ancilla_exact_test_dimension':32,
        'moving_input_support':'F_L^dagger Q F_L',
        'moving_output_support':'F_R Q F_R^dagger',
        'scope':'A genuine completely unitary process-tensor extension. No routed graph or arbitrary-host conclusion.'}
(ROOT/'continuous_product_supported_cut_audit_parameter_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2),flush=True)
