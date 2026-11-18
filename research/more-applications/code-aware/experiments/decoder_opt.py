"""Small numerical recovery SDPs without an external conic solver.
A log-det dual solver returns a feasible dual bound and a normalized primal decoder.
These are floating-point diagnostics, not interval/exact certificates.
"""
from __future__ import annotations
import numpy as np
from scipy.optimize import minimize
from nonpauli_qec import compress,invsqrt
from core import vec


def herm_basis(d):
 out=[]
 for i in range(d):
  E=np.zeros((d,d),complex);E[i,i]=1;out.append(E)
 for i in range(d):
  for j in range(i):
   E=np.zeros((d,d),complex);E[i,j]=E[j,i]=1/np.sqrt(2);out.append(E)
   E=np.zeros((d,d),complex);E[i,j]=1j/np.sqrt(2);E[j,i]=-1j/np.sqrt(2);out.append(E)
 return np.array(out)


def objective_matrix(L):
 dim=L[0].shape[1]
 V=np.column_stack([vec(l.conj().T) for l in L])
 return V@V.conj().T/dim**2


def solve(L,tol=1e-7):
 L=compress(L)
 if not L:return {'lower':0.,'upper':0.,'decoder':[],'dual_min_eig':0.,'gap':0.}
 n,D=L[0].shape;H=objective_matrix(L);Bs=herm_basis(n)
 tr=np.trace(Bs,axis1=1,axis2=2).real
 A=np.array([np.kron(b,np.eye(D)) for b in Bs])
 # Identity starting point strictly dominates H.
 y=tr*(np.linalg.eigvalsh(H)[-1]+1.)
 mus=[.1,.02,.004,.0008,.00016,3.2e-5,6.4e-6,1.28e-6,tol/(n*D)]
 for mu in mus:
  for iteration in range(80):
   M=np.einsum('i,iab->ab',y,A)-H
   w,V=np.linalg.eigh((M+M.conj().T)/2)
   if w[0]<=0:raise RuntimeError('lost dual feasibility')
   inv=(V*(1/w))@V.conj().T
   f=float(tr@y-mu*np.log(w).sum())
   grad=tr-mu*np.einsum('iab,ba->i',A,inv).real
   B=np.einsum('ab,ibc->iac',inv,A)
   hess=mu*np.einsum('iab,jba->ij',B,B).real
   hess=(hess+hess.T)/2
   try: step=np.linalg.solve(hess,-grad)
   except np.linalg.LinAlgError: step=np.linalg.lstsq(hess,-grad,rcond=1e-13)[0]
   slope=float(grad@step)
   if -slope<max(1e-14,mu*1e-7):break
   change=np.einsum('i,iab->ab',step,A)
   length=1.
   for back in range(80):
    trial=M+length*change
    tw=np.linalg.eigvalsh((trial+trial.conj().T)/2)
    if tw[0]>0:
     nf=float(tr@(y+length*step)-mu*np.log(tw).sum())
     if nf<=f+1e-2*length*slope:break
    length*=.5
   if length<1e-18:break
   y+=length*step

 Y=np.einsum('i,iab->ab',y,Bs);M=np.kron(Y,np.eye(D))-H
 w,V=np.linalg.eigh((M+M.conj().T)/2)
 # A margin makes the final dual numerically feasible.
 margin=max(0.,1e-11-float(w[0]));Y+=margin*np.eye(n);M+=margin*np.eye(n*D)
 inv=np.linalg.inv(M);J=mus[-1]*inv;J=(J+J.conj().T)/2
 S=np.einsum('aibi->ab',J.reshape(n,D,n,D))
 T=np.kron(invsqrt(S),np.eye(D));J=T@J@T.conj().T;J=(J+J.conj().T)/2
 vals,U=np.linalg.eigh(J);R=[np.sqrt(v)*U[:,i].reshape(D,n,order='F') for i,v in enumerate(vals) if v>1e-12]
 lower=float(np.trace(H@J).real);upper=float(np.trace(Y).real)
 assert lower<=upper+1e-7,(lower,upper)
 return {'lower':lower,'upper':upper,'decoder':R,'dual_min_eig':float(np.linalg.eigvalsh(M)[0]),'gap':upper-lower,
         'tp_error':float(np.linalg.norm(sum((r.conj().T@r for r in R),np.zeros((n,n),complex))-np.eye(n)))}

if __name__=='__main__':
 from core import amplitude,PAULI
 for p in [.01,.1,.5,.9]:
  a=solve(amplitude(p),tol=1e-6);print(p,{k:v for k,v in a.items() if k!='decoder'},flush=True)
