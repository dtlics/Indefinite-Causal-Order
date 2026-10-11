"""Exact independent kernels and rational minors for the forbidden K12 cut.

Builds canonical carriers independently and uses the full complex End(K12)
unknown; neither Hermiticity nor projection equations are needed for the
linear contradiction. No modular or numerical rank is used.
"""
from pathlib import Path
from itertools import product
import json
import sympy as s
from exact_fixtures import E,R,I16,I2,X,Z,WORDS,local
ROOT=Path(__file__).parent
# Unnormalised rational K12 frame; B^*B=2I4. Scaling unknown coefficients
# does not change the complex support-space span.
B=s.kronecker_product(s.eye(4),s.Matrix([1,-1]),s.Matrix([0,1]))
assert B.T*B==2*s.eye(4)
K=B*B.T/2
assert K*K==K and K.trace()==4

def cylinder(i,vecs):
 cols=[];other=[j for j in range(4) if j!=i]
 for bit in (0,1):
  for v in vecs:
   cols.append(s.Matrix([v[sum(w[j]<<(2-k) for k,j in enumerate(other))] if w[i]==bit else 0 for w in WORDS]))
 M=s.Matrix.hstack(*cols);return M*(M.T*M).inv()*M.T
S=[cylinder(0,[[1,0,1,0,0,0,0,0],[1,0,0,1,0,0,0,0]]),
   cylinder(1,[[0,1,0,0,0,0,0,0],[0,0,0,0,1,1,-1,-1]]),E[2],E[3]]
assert all(K*E[j]==s.zeros(16) for j in (2,3))
assert B.T*local(2,Z)*B==s.zeros(4)
assert B.T*local(3,X)*B==s.zeros(4)
geom=[]
for j in range(4):
 A=B.T*(I16-S[j])*B
 minors=[A[:k,:k].det() for k in range(1,5)]
 assert all(x>0 for x in minors)
 geom.append({'query':j+1,'K12_intersection_Sj_zero':True,
              'complement_Gram_leading_minors':[str(x) for x in minors]})
HB=[]
for a,b in product(range(4),repeat=2):
 h=s.zeros(4);h[a,b]=1;HB.append(B*h*B.T)

def build(i,Qi):
 matrices=[];labels=[]
 for name,x in [('X',X),('Z',Z)]:
  al=R[i]*local(i,x)*R[i]
  columns=[((q*al-al*q)*(I16-Qi)).reshape(256,1) for q in HB]
  block=s.Matrix.hstack(*columns)
  matrices.append(block)
  labels += [{'query':i+1,'Pauli':name,'output_row':r,'input_column':c} for r,c in product(range(16),repeat=2)]
 return s.Matrix.vstack(*matrices),labels

def minor_certificate(A,labels,rank):
 _,cols=A.rref();assert len(cols)==rank
 _,rows=A.T.rref();assert len(rows)==rank
 M=A.extract(rows,cols);det=M.det();assert det!=0
 # The explicit selected rows/columns are the small independently checkable
 # rational lower-bound certificate; kernel identities supply upper bounds.
 return {'rank':rank,'row_indices':list(rows),'row_labels':[labels[r] for r in rows],
         'column_indices':list(cols),'minor_determinant':str(det),
         'minor_matrix':[[str(x) for x in M.row(r)] for r in range(rank)]}
# Exact proposed two-dimensional kernel spaces on the 12 input-qubit frame.
e0=s.Matrix([1,0]);e1=s.Matrix([0,1]);minus=e0-e1
kernels=[ [s.kronecker_product(I2,e1*v.T) for v in (e0,e1)],
          [s.kronecker_product(minus*v.T,I2) for v in (e0,e1)] ]
spaces=[s.Matrix.hstack(*(h.reshape(16,1) for h in hs)) for hs in kernels]
assert s.Matrix.hstack(*spaces).rank()==4
single=[];systems={}
for i in (0,1):
 for nm,Qi in [(f'E{i+1}',E[i]),(f'S{i+1}',S[i])]:
  A,labels=build(i,Qi);N=spaces[i]
  assert N.rank()==2 and A*N==s.zeros(A.rows,2)
  cert=minor_certificate(A,labels,14)
  cert.update({'Q_i':nm,'kernel_basis_H':[[[str(x) for x in h.row(r)] for r in range(4)] for h in kernels[i]],
               'kernel_formula':'I1 tensor |1><v|2' if i==0 else '|minus><w|1 tensor I2'})
  single.append(cert);systems[nm]=A,labels
combined=[]
for n1,n2 in product(('E1','S1'),('E2','S2')):
 A1,l1=systems[n1];A2,l2=systems[n2];A=A1.col_join(A2)
 cert=minor_certificate(A,l1+l2,16);cert.update({'Q1':n1,'Q2':n2,'only_solution':'Q=0'})
 combined.append(cert)
out={'status':'PASS','unknown_complex_dimension':16,
 'frame_Gram':'2 I4','cut_orthogonal_to_E3_E4':True,
 'nonzero_cut_projection_cannot_commute_with_Z3_or_X4':True,
 'K12_disjoint_from_every_Sj':geom,'single_systems':single,
 'two_single_kernel_spaces_have_zero_intersection':True,'combined_systems':combined,
 'scope':'Exact rational certificate for necessary native-branch cut equations. The graph/order reduction is proved in core_group_cut_branch_independent_audit.md.'}
(ROOT/'core_group_cut_branch_independent_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: all four single systems rank14 with displayed exact kernels; all four combined systems rank16')
for c in combined:print(c['Q1'],c['Q2'],'minor determinant',c['minor_determinant'])
