"""Numerical scout only; any failure requires an exact certificate."""
import numpy as np,itertools,json
from exact_fixtures import E,R,I16,local,Z
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),I16*0)
Es=[np.kron(np.array(e,dtype=complex),np.eye(16)) for e in E];D=np.kron(np.array(D0,dtype=complex),np.eye(16));Zs=[np.kron(np.array(local(i,Z)-I16,dtype=complex),np.eye(16)) for i in range(4)]
Q0=np.kron(np.eye(4),np.outer([1,-1],[1,-1])/2);Q0=np.kron(Q0,np.diag([0,1]));Q=np.kron(Q0,np.eye(16));I=np.eye(256)
def emb(A,ids):
 out=np.zeros((256,256),complex)
 for k in range(256):
  w=list(map(int,f'{k:08b}'));c=2*w[ids[0]]+w[ids[1]]
  for r in range(4):
   ww=w.copy();ww[ids[0]]=r//2;ww[ids[1]]=r%2;j=int(''.join(map(str,ww)),2);out[j,k]=A[r,c]
 return out
swap=np.array([[1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,1]])
cnot=np.array([[1,0,0,0],[0,1,0,0],[0,0,0,1],[0,0,1,0]])
gates=[np.eye(4),swap,cnot,swap@cnot]
ops=[[emb(g,[i,4+i]) for g in gates] for i in range(4)]
def F(us):
 W=np.eye(256,dtype=complex)
 for u in us:W=W@u
 return (W+sum((Zs[i]@W@Es[i] for i in range(4)),np.zeros((256,256),complex)))@D
out=[]
for aa in [[1,1,1,1],[1,1,0,0],[0,0,1,1],[2,2,2,2],[3,3,3,3],[1,2,3,1]]:
 us=[ops[i][a] for i,a in enumerate(aa)];l=us[:2]+[I,I];r=[I,I]+us[2:];C=(F(r).conj().T@F(us)@F(l).conj().T-I)@Q
 n=float(np.vdot(C,C).real);print(aa,n,flush=True);out.append({'gates':aa,'defect_squared':n})
json.dump(out,open('auxiliary_cut_private_ancilla_scout_checks.json','w'),indent=2)
