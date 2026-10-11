import sympy as s,json
from exact_fixtures import E,I2,I16,X,Y,Z,local,tensor,R,choices,WORDS
qC=choices[0,1][0].extract(range(4),range(4));S1=tensor([I2,s.diag(1,0),s.eye(4)-qC])
g0=s.zeros(8,1);g0[1]=1;g1=s.Matrix([0,0,0,0,1,1,-1,-1])/2
A=g0*g0.H+g1*g1.H;S2=s.zeros(16)
for i,p in enumerate(WORDS):
 for j,q in enumerate(WORDS):
  if p[1]==q[1]:S2[i,j]=A[4*p[0]+2*p[2]+p[3],4*q[0]+2*q[2]+q[3]]
Q12=tensor([I2,I2,s.Matrix([[1,-1],[-1,1]])/2,s.diag(0,1)])
Ss=[S1,S2,E[2],E[3],Q12];bs=[];groups=[]
for g,S in enumerate(Ss):
 B=s.Matrix.hstack(*S.columnspace())
 for i in range(B.cols):
  for j in range(B.cols):bs.append(B[:,i]*B[:,j].H);groups.append(g)
print('variables',len(bs),flush=True)
out={}
for mode in ['past','future']:
 blocks=[]
 for i in range(4):
  for pa in [X,Y,Z]:
   op=R[i]*local(i,pa)*R[i] if mode=='past' else local(i,pa)
   if pa==Y:op=op/s.I
   chosen=([i,4] if i<2 else [i]) if mode=='past' else ([g for g in range(5) if g!=i and not(g==4 and i<2)])
   blocks.append(s.Matrix.hstack(*[(op*b-b*op).reshape(256,1) if g in chosen else s.zeros(256,1) for b,g in zip(bs,groups)]))
 M=s.Matrix.vstack(*blocks);ns=s.polys.matrices.DomainMatrix.from_Matrix(M).convert_to(s.QQ).nullspace().to_Matrix()
 print(mode,'nullity',ns.rows,flush=True)
 vals=[]
 for rr in range(ns.rows):
  v=ns.row(rr);mats=[sum((v[k]*b for k,(b,g) in enumerate(zip(bs,groups)) if g==j),s.zeros(16)) for j in range(5)]
  vals.append(mats)
 # Projection of solution space to each group.
 ranks=[]
 for g in range(5):
  cols=s.Matrix.hstack(*[m[g].reshape(256,1) for m in vals]) if vals else s.zeros(256,0)
  ranks.append(cols.rank())
 print('component dims',ranks,flush=True)
 out[mode]={'first_derivative_constraint_rank':M.cols-ns.rows,'first_derivative_solution_dimension':ns.rows,'component_image_dimensions':ranks,'all_coefficients_rational':all(v.is_Rational for v in M)}
 if mode=='past':
  assert ns.rows==10 and ranks==[4,4,1,1,0]
  assert all(m[4]==s.zeros(16) and all(m[i]*(R[i]*local(i,p)*R[i])==(R[i]*local(i,p)*R[i])*m[i] for i in range(4) for p in [X,Y,Z]) for m in vals)
 else:assert ns.rows==0
json.dump(out,open('auxiliary_multiplicity_free_exact_checks.json','w'),indent=2)
