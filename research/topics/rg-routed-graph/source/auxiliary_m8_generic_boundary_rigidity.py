"""Exact quartet fixtures for the generic M8/multiplicity-two boundary theorem.

The theorem and cocycle proof are in the companion Markdown file. These checks
certify its explicit nonempty open-set witness and describe aligned exceptions;
none constructs or varies an independent multiplicity-sector native filler.
"""
from pathlib import Path
import json
import sympy as s
from exact_fixtures import E,I16,I2,X,Y,Z,R,WORDS,local,tensor
ROOT=Path(__file__).parent
P=[X,Y,Z]
alpha=[[R[i]*local(i,p)*R[i] for p in P] for i in range(4)]
# Exact distinctness: Z_i belongs to alpha_i but is orthogonal to alpha_j for i!=j.
for i in range(4):
    assert alpha[i][2]==local(i,Z)
    for j in range(4):
        if i==j:continue
        assert s.trace(local(i,Z))==0
        assert all(s.trace(local(i,Z)*b)==0 for b in alpha[j])

def joint_kernel(nbasis,i):
    M=s.Matrix.vstack(*[s.Matrix.hstack(*[(n*a-a*n).reshape(256,1) for n in nbasis])
                       for a in alpha[i]])
    ns=M.nullspace()
    return 3-len(ns),ns

aligned=[]
for k in range(4):
    row=[]
    for i in range(4):
        rank,ns=joint_kernel(alpha[k],i)
        row.append({'original_query':i+1,'traceless_joint_commutant_dimension':len(ns),
                    'axes_in_alpha_k_XYZ_coordinates':[[str(x) for x in v] for v in ns]})
    aligned.append({'auxiliary_commutant':'alpha_'+str(k+1)+'(M2)',
                    'original_joint_commutants':row,
                    'boundary_theorem_hypothesis_holds':all(x['traceless_joint_commutant_dimension']==0 for x in row)})
assert [x['boundary_theorem_hypothesis_holds'] for x in aligned]==[False,False,True,False]
# The explicit witness N=alpha3(M2) has four full-rank 3-column constraints.
assert all(joint_kernel(alpha[2],i)[0]==3 for i in range(4))

# A second dense rationally conjugated factor, independent of alpha3 alignment.
v=s.Matrix(range(1,17));H=I16-2*v*v.T/(v.T*v)[0]
assert H.T*H==I16
nbasis=[H*local(3,p)*H.T for p in P]
householder_ranks=[joint_kernel(nbasis,i)[0] for i in range(4)]
assert householder_ranks==[3,3,3,3]

# Boundary-only conclusion invokes the established absence of any proper full
# group factorization. Recheck all twelve supplied ordered-pair defects through
# the independent normalized orthogonal-support formula.
def F(us):
    return tensor(us)+sum((tensor([I2 if k==i else us[k] for k in range(4)])*
                           local(i,Z*us[i]*Z-us[i])*E[i] for i in range(4)),s.zeros(16))
witnesses=json.loads((ROOT/'auxiliary_full_boundary_checks.json').read_text())
pa={'X':X,'Y':Y,'Z':Z}
for w in witnesses:
    i,j=w['before']-1,w['after']-1
    us=[I2]*4;us[i]=pa[w['before_query']];us[j]=pa[w['after_query']]
    defect=F(us)-(R[j]*local(j,us[j])*R[j])*(R[i]*local(i,us[i])*R[i])
    assert s.trace(defect.H*defect)==s.sympify(w['defect_HS_squared'])>0

out={'status':'PASS',
     'theorem_scope':'Unital full M8 auxiliary on C16 with scalar origin joint commutants against every original factor',
     'explicit_canonical_witness':'B=alpha_3(M2) commutant, N=alpha_3(M2)',
     'canonical_witness_constraint_ranks':[3,3,3,3],
     'dense_rational_householder_witness_constraint_ranks':householder_ranks,
     'original_factor_images_pairwise_distinct':True,
     'ordered_pair_obstructions_rechecked':12,
     'canonical_aligned_cases':aligned,
     'genericity':'Nonempty open dense hypothesis in unitary-conjugacy coordinates for the multiplicity qubit algebra N',
     'unresolved':'Exceptional aligned factors admitting rank-eight origin comparison directions; no interior quartet extension found or ruled out there',
     'no_hidden_refinement':'The multiplicity qubit is never treated as independently fillable native branches'}
(ROOT/'auxiliary_m8_generic_boundary_rigidity_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
