"""Independent exact audit of the multiplicity-free auxiliary classification.

Carriers are reconstructed from partial-trace kernels, not the author's choices
formula. Both derivative systems are built from generic before-set membership.
"""
from pathlib import Path
from itertools import product
import json
import sympy as s
from exact_fixtures import E,I16,I2,X,Y,Z,WORDS,tensor,local,R,choices
ROOT=Path(__file__).parent
zero=s.zeros(16); before_sets=[(0,),(1,),(2,),(3,),(0,1)]

def idx(w):return sum(x<<(3-i) for i,x in enumerate(w))
def merge(L,l,Rr,r):
    out=[0]*4
    for i,x in zip(L,l):out[i]=x
    for i,x in zip(Rr,r):out[i]=x
    return tuple(out)

def cylinder_basis(L):
    Rr=tuple(i for i in range(4) if i not in L)
    lw=list(product(range(2),repeat=len(L)));rw=list(product(range(2),repeat=len(Rr)))
    H=s.zeros(len(rw))
    for j in Rr:
        for a,p in enumerate(rw):
            for b,q in enumerate(rw):
                H[a,b]+=sum(E[j][idx(merge(L,l,Rr,p)),idx(merge(L,l,Rr,q))] for l in lw)
    ns=H.nullspace();columns=[]
    for l in lw:
        for v in ns:
            c=s.zeros(16,1)
            for r,w in enumerate(rw):c[idx(merge(L,l,Rr,w))]=v[r]
            columns.append(c)
    B=s.Matrix.hstack(*columns)
    Q=B*(B.H*B).inv()*B.H
    assert Q==Q.H and Q*Q==Q
    assert all(E[j]*Q==zero for j in Rr)
    assert all(Q*local(i,p)==local(i,p)*Q for i in L for p in [X,Y,Z])
    return B,Q

pairs=[cylinder_basis(L) for L in before_sets]
Bs=[b for b,q in pairs];Qs=[q for b,q in pairs]
assert [b.cols for b in Bs]==[4,4,2,2,4]
assert all(Qs[i]*Qs[j]==zero for i in range(4) for j in range(i))
assert all(Qs[i]*(R[i]*local(i,p)*R[i])==(R[i]*local(i,p)*R[i])*Qs[i]
           for i in range(4) for p in [X,Y,Z])

# Check equality to the author's support definitions, only after independently
# constructing them. Basis vectors are deliberately different.
qC=choices[0,1][0].extract(range(4),range(4))
assert Qs[0]==tensor([I2,s.diag(1,0),s.eye(4)-qC])
g0=tensor([s.Matrix([1,0]),s.Matrix([1,0]),s.Matrix([0,1])])
g1=tensor([s.Matrix([0,1]),s.Matrix([1,-1]),s.Matrix([1,1])])/2
spect=g0*g0.H+g1*g1.H
S2=s.Matrix(16,16,lambda r,c: spect[4*WORDS[r][0]+2*WORDS[r][2]+WORDS[r][3],
                                    4*WORDS[c][0]+2*WORDS[c][2]+WORDS[c][3]]
             if WORDS[r][1]==WORDS[c][1] else 0)
assert Qs[1]==S2 and Qs[2]==E[2] and Qs[3]==E[3]
assert Qs[4]==tensor([I2,I2,s.Matrix([[1,-1],[-1,1]])/2,s.diag(0,1)])

# Matrix-operator embeddings and explicit invertible coordinate changes.
operator_bases=[];groups=[];author_bases=[];transforms=[]
for g,(B,Q) in enumerate(pairs):
    A=s.Matrix.hstack(*Q.columnspace())
    T=(A.H*A).inv()*A.H*B
    assert A*T==B and T.det()!=0
    transforms.append(s.kronecker_product(T,s.conjugate(T)))
    for i in range(B.cols):
        for j in range(B.cols):
            operator_bases.append(B[:,i]*B[:,j].H);groups.append(g)
            author_bases.append(A[:,i]*A[:,j].H)
T=s.diag(*transforms)
assert T.shape==(56,56) and T.det()!=0
embedded=s.Matrix.hstack(*[b.reshape(256,1) for b in operator_bases])
author_embedded=s.Matrix.hstack(*[b.reshape(256,1) for b in author_bases])
assert embedded==author_embedded*T

def equations(mode,ops):
    rows=[]
    for i in range(4):
        for p in [X,Y,Z]:
            h=R[i]*local(i,p)*R[i] if mode=='past' else local(i,p)
            if p==Y:h=h/s.I
            cols=[]
            for b,g in zip(ops,groups):
                included=i in before_sets[g] if mode=='past' else i not in before_sets[g]
                cols.append((h*b-b*h).reshape(256,1) if included else s.zeros(256,1))
            rows.append(s.Matrix.hstack(*cols))
    return s.Matrix.vstack(*rows)

def rational_kernel(M):
    assert all(x.is_Rational for x in M)
    return s.polys.matrices.DomainMatrix.from_Matrix(M).convert_to(s.QQ).nullspace().to_Matrix().T

results={};systems={};kernels={}
for mode in ['past','future']:
    M=equations(mode,operator_bases);A=equations(mode,author_bases)
    assert M==A*T
    N=rational_kernel(M)
    assert M*N==s.zeros(M.rows,N.cols)
    systems[mode]=M;kernels[mode]=N
    dimensions=[]
    for g in range(5):
        ids=[k for k,x in enumerate(groups) if x==g]
        dimensions.append(N.extract(ids,list(range(N.cols))).rank())
    results[mode]={'exact_rank':M.cols-N.cols,'exact_kernel_dimension':N.cols,
                   'component_image_dimensions':dimensions,
                   'independent_embedding_coordinate_change_exactly_verified':True}
    print(mode,results[mode],flush=True)
assert results['past']['exact_rank']==46 and results['past']['component_image_dimensions']==[4,4,1,1,0]
assert results['future']['exact_rank']==56

# Independently build the claimed direct sum of supported original commutants.
desired=[];commutant_dims=[]
for g in range(4):
    ids=[k for k,x in enumerate(groups) if x==g]
    local_cols=[operator_bases[k] for k in ids]
    C=s.Matrix.vstack(*[s.Matrix.hstack(*[((R[g]*local(g,p)*R[g])*b-b*(R[g]*local(g,p)*R[g])).reshape(256,1)
                                        for b in local_cols]) for p in [X,Y,Z]])
    # This matrix may have imaginary Y entries; a complex nullspace is exact.
    nn=C.nullspace();commutant_dims.append(len(nn))
    for v in nn:
        w=s.zeros(56,1)
        for j,k in enumerate(ids):w[k]=v[j]
        desired.append(w)
D=s.Matrix.hstack(*desired)
assert commutant_dims==[4,4,1,1] and D.rank()==10
assert systems['past']*D==s.zeros(systems['past'].rows,10)
assert D.row_join(kernels['past']).rank()==10

# Full coefficient span: each output-row coefficient frame is V_o D0.
Vs=[I16-2*sum((o[i]*E[i] for i in range(4)),zero) for o in WORDS]
D0=s.Matrix.vstack(*[Vs[k][k,:] for k in range(16)])
assert D0*D0==I16
assert all((V*D0).H*(V*D0)==I16 for V in Vs)

# Converse exercise: all sixteen auxiliary simple blocks are scalar, each of
# multiplicity one. Group 3 contains two individual blocks that do NOT reduce
# alpha_3, while their sum Q3=E3 does. Give each scalar block its own independent
# 2x2 private-ancilla filling and verify the full 32-dimensional result.
def F(us):
    W=tensor(us)
    return s.Matrix.vstack(*[(W[k,:]*Vs[k]) for k in range(16)])*D0
us=[(3*I2+4*s.I*p)/5 for p in [X,Y,Z,X]]
f=F(us).applyfunc(s.expand)
active_indices=[4,6] # |0100>, |0110>, whose sum is E3
ps=[]
for p in range(16):
    P=s.zeros(16);P[p,p]=1;ps.append(P)
assert ps[4]+ps[6]==E[2]
alphaX=R[2]*local(2,X)*R[2]
assert ps[4]*alphaX!=alphaX*ps[4]
aux=[I2,X,Y,Z]
Aactive=sum((s.kronecker_product(ps[p],aux[p%4]) for p in active_indices),s.zeros(32))
Apassive=sum((s.kronecker_product(ps[p],aux[p%4]) for p in range(16) if p not in active_indices),s.zeros(32))
bar=tensor([us[0],us[1],I2,us[3]]).applyfunc(s.expand)
alpha=R[2]*local(2,us[2])*R[2]
G=(s.kronecker_product(f,I2)*Apassive+s.kronecker_product(bar,I2)*Aactive*s.kronecker_product(alpha,I2)).applyfunc(s.expand)
assert (G.H*G-s.eye(32)).applyfunc(s.expand)==s.zeros(32)
print('Non-reducing individual-block ancillary converse test PASS.',flush=True)

report={'status':'PASS','carrier_construction':'Independent partial-trace kernel cylinders',
        'support_ranks':[4,4,2,2,4],'complex_operator_coordinate_count':56,
        'exact_coordinate_change_rank':56,'derivative_systems':results,
        'past_kernel_equals_direct_sum_of_supported_commutants':True,
        'supported_commutant_dimensions':commutant_dims,
        'full_coefficient_span_dimension':256,
        'full_coefficient_span_certificate':'Sixteen unitary row frames V_o D0; matrix-unit inputs isolate each row',
        'converse_ancillary_test':{'dimension':32,'auxiliary_algebra':'C^16, all multiplicities one',
                                  'serial_group':3,'individual_blocks_reduce_alpha3':False,
                                  'group_projection_reduces_alpha3':True,'unitarity':'exact PASS'},
        'scope':'One actual auxiliary vertex with every used simple summand represented with multiplicity one. No graph deletion or repeated-multiplicity classification.'}
(ROOT/'auxiliary_multiplicity_free_independent_audit_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2),flush=True)
