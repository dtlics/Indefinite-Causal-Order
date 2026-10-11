"""Exact rational checks: physical non-clique point and a matching completion."""
from pathlib import Path
import json, sympy as s
I=s.eye(2);X=s.Matrix([[0,1],[1,0]]);Z=s.diag(1,-1)
kron=s.kronecker_product
H1=kron(X,X,Z,I);H2=kron(Z,Z,X,I);H=H1+H2;n=16
assert H1*H1==s.eye(n) and H2*H2==s.eye(n)
assert H1*H2+H2*H1==s.zeros(n)
assert H*H==2*s.eye(n)
B=3*s.eye(n)+2*H # W=B/48, rational and strictly positive
assert (3*s.eye(n)-2*H)*B==s.eye(n) # positivity: eigenvalues 3 +/- 2sqrt(2)>0
assert s.trace(B)==48
# R is zero on angle-off-diagonal factors; the opposite factors are angle-diagonal and globally trace zero.
assert s.trace(kron(Z,I))==0 and s.trace(kron(Z,Z))==0
# All 16 classical-label blocks coincide; each is W. This proves the complete P constraint.
# Verify it directly in exact rational arrays using the literal R_A,D_A,R_B,D_B definitions.
W={(l,m):B/s.Integer(48) for l in range(4) for m in range(4)}
def RA(W):
 out={}
 for l in range(4):
  for m in range(4):
   Q=s.zeros(n)
   for a in range(4):
    for b in range(4):
     for c in range(4):
      for d in range(4):
       if a//2==c//2:Q[4*a+b,4*c+d]=sum(W[t,m][4*a+b,4*c+d] for t in range(4))/4
   out[l,m]=Q
 return out
def DA(W):
 out={}
 for l in range(4):
  for m in range(4):
   Q=s.zeros(n)
   for a in range(4):
    for b in range(4):
     for d in range(4):Q[4*a+b,4*a+d]=sum(W[t,m][4*c+b,4*c+d] for t in range(4) for c in range(4))/16
   out[l,m]=Q
 return out
S=s.zeros(n)
for a in range(4):
 for b in range(4):S[4*a+b,4*b+a]=1
def swap(W):return {(l,m):S*W[m,l]*S for l in range(4) for m in range(4)}
def RB(W):return swap(RA(swap(W)))
def DB(W):return swap(DA(swap(W)))
A=RA(W);C=RB(W);AC=RA(C);e=DA(W);ec=DA(C);f=DB(W);fa=DB(A)
for lm in W:assert A[lm]+C[lm]-AC[lm]-e[lm]+ec[lm]-f[lm]+fa[lm]==W[lm]
# Every row/column clique compression H_C has square I. Thus I-H_C is PSD.
for axis in (0,1):
 for j in (0,1):
  ids=[4*a+b for a in range(4) for b in range(4) if (a//2 if axis==0 else b//2)==j]
  HC=H.extract(ids,ids)
  assert HC*HC==s.eye(8)
ratio=s.trace(H*W[0,0])/s.trace(W[0,0]);assert ratio==s.Rational(4,3)
# Exact dual completion from w=[[1/2,1/3],[1/3,1/2]], a convex mixture of two matchings and the empty matching.
lam=[s.Integer(2),s.Integer(3),s.Integer(3),s.Integer(2)]
probs=[(s.Rational(1,2),[0,3]),(s.Rational(1,3),[1,2]),(s.Rational(1,6),[])]
M=s.zeros(4)
for p,edges in probs:
 h=s.Matrix([lam[i]*int(i in edges)-1 for i in range(4)])
 M+=p*h*h.T
assert M==s.Matrix([[1,-1,-1,1],[-1,2,2,-1],[-1,2,2,-1],[1,-1,-1,1]])
assert [M[i,i] for i in range(4)]==[x-1 for x in lam]
for i in range(4):
 for j in range(4):
  if i!=j and (i//2==j//2 or i%2==j%2):assert M[i,j]==-1
# Exact sharp scalar example q=[[4/9,1/9],[1/9,4/9]].
v=s.Matrix([s.Rational(2,3),s.Rational(1,3)]);u=s.Matrix([s.Rational(1,3),s.Rational(2,3)])
Q=s.diag(v*v.T,u*u.T);lam2=[s.Rational(3,2),s.Integer(3),s.Integer(3),s.Rational(3,2)]
assert sum(Q)==2
assert sum(Q[i,i]*lam2[i] for i in range(4))==2
out={'scope':'Exact structural checks, not an unrestricted GYNI value or finite-support theorem','physical_K2_normalization_pass':True,'H_squared':2,'strict_positive_W':'eigenvalues (3 +/- 2 sqrt(2))/48','each_block_trace':1,'row_column_clique_witness_bound':1,'physical_witness_value':str(ratio),'matching_completion_pass':True,'sharp_scalar_example_value':2}
Path(__file__).with_name('rook_exact_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
