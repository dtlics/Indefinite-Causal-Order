"""Integer-only replay of a full physical lower versus a row/column cone upper."""
from pathlib import Path
import sys,json,gzip
from fractions import Fraction as Q
import numpy as np,scipy.sparse as sp
HERE=Path(__file__).parent
K=2;d=4;N=16;L=64;DEN=10**8

def forbidden():
 R=sp.lil_matrix((L,L),dtype=np.int64);D=sp.lil_matrix((L,L),dtype=np.int64)
 ix=lambda l,i,j:(l*d+i)*d+j
 for l in range(4):
  for i in range(d):
   for j in range(d):
    if i//2==j//2:
     for m in range(4):R[ix(l,i,j),ix(m,i,j)]=4
    if i==j:
     for m in range(4):
      for t in range(d):D[ix(l,i,j),ix(m,t,t)]=1
 R=R.tocsr();D=D.tocsr();F=16*sp.eye(L,dtype=np.int64)-R
 return (sp.kron(F,F)+sp.kron(F,D)+sp.kron(D,F)).tocsr()
B=forbidden();perm=np.arange(4096).reshape(4,4,4,4,4,4).transpose(0,2,4,1,3,5).ravel()
def forbid_num(A):
 out=np.empty(4096,dtype=np.int64);out[perm]=np.asarray(B@A.ravel()[perm]).ravel();return out.reshape(4,4,16,16)
I=np.broadcast_to(np.eye(16,dtype=np.int64),(4,4,16,16)).copy()
assert np.all(forbid_num(I)==0)

def pd_pivots(M):
 A=np.array(M,dtype=object).copy();prev=1;piv=[];n=len(A)
 assert np.array_equal(A,A.T)
 for k in range(n):
  p=int(A[k,k]);assert p>0,('nonpositive pivot',k,p);piv.append(p)
  if k==n-1:break
  for i in range(k+1,n):
   for j in range(k+1,n):
    z=A[i,j]*p-A[i,k]*A[k,j];assert z%prev==0;A[i,j]=z//prev
  prev=p
 return piv

def objective():
 vs={(0,0):[17,0,17,0],(0,1):[0,17,0,17],(1,0):[15,8,8,15],(1,1):[-8,15,-15,8]};G=np.zeros((4,4,16,16),dtype=object)
 for x in [0,1]:
  for y in [0,1]:
   v=np.kron(vs[x,y],vs[y,x]).astype(object);G[2*x+y,2*y+x]=np.outer(v,v)
 return G,4*17**4
G,GD=objective()
if '--make' in sys.argv:
 w=np.load(HERE/'physical_K2_cliques0.npz')['W'];f=np.load(HERE/'physical_K2_cliques1.npz')['F'];data={'denominator':DEN,'physical_round':np.rint(DEN*w).astype(np.int64).tolist(),'clique_dual_round':np.rint(DEN*f).astype(np.int64).tolist()}
 with gzip.open(HERE/'clique_gap_data.json.gz','wt') as z:json.dump(data,z,separators=(',',':'))
with gzip.open(HERE/'clique_gap_data.json.gz','rt') as z:data=json.load(z)
assert data['denominator']==DEN
w=np.array(data['physical_round'],dtype=np.int64);f=np.array(data['clique_dual_round'],dtype=np.int64)
assert np.array_equal(w,w.transpose(0,1,3,2)) and np.array_equal(f,f.transpose(0,1,3,2))
# P_aff at scale 256 DEN. For K=2, the affine white-noise denominator is also 256.
tr=int(np.trace(w,axis1=-2,axis2=-1).sum());wn=256*w-forbid_num(w)+(16*DEN-tr)*I
assert np.all(forbid_num(wn)==0)
assert int(np.trace(wn,axis1=-2,axis2=-1).sum())==16*256*DEN
# Add 10^-5 identity and renormalize. All integer leading principal minors are positive.
wn=100000*wn.astype(object)+(256*DEN)*I;WD=256*DEN*100016
pmin=[]
for l in range(4):
 for m in range(4):pmin.append(str(pd_pivots(wn[l,m])[-1]))
assert sum(np.trace(wn,axis1=-2,axis2=-1).ravel())==16*WD
assert all(t==WD for t in np.trace(wn,axis1=-2,axis2=-1).ravel())
lower=Q(int(np.sum(wn*G)),WD*GD)
# Orthogonally repair the dual normalization, and choose the rational clique upper 0.6183.
upper=Q(6183,10000);FD=256*DEN
assert FD%160000==0
fn=forbid_num(f).astype(object)+6183*(FD//160000)*I
# F=(I-P)(rounded F)+upper/16 I, so P(F)=upper/16 I exactly.
# Direct integer check using int64 before multiplying by G denominator.
Fint=np.array(fn,dtype=np.int64);assert np.array_equal(256*Fint-forbid_num(Fint),256*6183*(FD//160000)*I)
slack=fn*GD-G*FD
clique_count=0
for l in range(4):
 for m in range(4):
  for axis in [0,1]:
   for t in range(2):
    ids=[i*4+j for i in range(4) for j in range(4) if (i//2 if axis==0 else j//2)==t]
    pd_pivots(slack[l,m][np.ix_(ids,ids)]);clique_count+=1
assert lower>upper
out={'status':'integer_only_replay_pass','angles_rational_cos_sin':[['15/17','8/17'],['8/17','15/17']],'full_physical_lower':str(lower),'full_physical_lower_decimal':float(lower),'normalized_row_column_clique_upper':str(upper),'normalized_row_column_clique_upper_decimal':float(upper),'strict_gap':str(lower-upper),'strict_gap_decimal':float(lower-upper),'physical_positive_blocks':16,'positive_clique_slacks':clique_count,'scope':'Same exact two-angle support. Excludes a common row/column clique lift preserving full normalization and at least this GYNI score; does not exclude arbitrary finite-angle optimizer replacement.'}
(HERE/'clique_gap_replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
