"""Full-channel tests for an ordinary simulator of code retractions."""
from __future__ import annotations
import json
import numpy as np
from core import choi, effect

def retraction(d,k,rng):
 q=d-k;rank=q+1
 M=rng.normal(size=(rank*k,q))+1j*rng.normal(size=(rank*k,q));V,_=np.linalg.qr(M)
 P=np.diag([1]*k+[0]*q).astype(complex);K=[P]
 for a in range(rank):
  x=np.zeros((d,d),complex);x[:k,k:]=V[a*k:(a+1)*k,:];K.append(x)
 assert np.linalg.norm(effect(K)-np.eye(d))<1e-12
 return K,P

def switch(A,B):
 d=len(A[0]);out=[]
 for a in A:
  for b in B:
   x=np.zeros((2*d,2*d),complex);x[:d,:d]=b@a;x[d:,d:]=a@b;out.append(x)
 return out

def ordinary(A,B,P):
 d=len(P);Q=np.eye(d)-P;out=[np.kron(np.eye(2),P)]
 for K,c in [(A,0),(B,1)]:
  for a in K:
   x=np.zeros((2*d,2*d),complex);x[c*d:(c+1)*d,c*d:(c+1)*d]=a@Q;out.append(x)
 return out

def main():
 rng=np.random.default_rng(19031);rows=[]
 for d,k in [(3,1),(4,2),(8,2),(8,4),(12,4)]:
  for rep in range(12):
   A,P=retraction(d,k,rng);B,_=retraction(d,k,rng)
   U,_=np.linalg.qr(rng.normal(size=(d,d))+1j*rng.normal(size=(d,d)))
   A=[U@a@U.conj().T for a in A];B=[U@b@U.conj().T for b in B];P=U@P@U.conj().T
   residual=np.linalg.norm(choi(switch(A,B))-choi(ordinary(A,B,P)))
   rows.append({'d':d,'k':k,'full_choi_residual':float(residual)})
 assert max(x['full_choi_residual'] for x in rows)<1e-11
 partial=[]
 for a in [.01,.2,.8,1]:
  for b in [.01,.2,.8,1]:
   k=2;d=4
   U,_=np.linalg.qr(rng.normal(size=(k,k))+1j*rng.normal(size=(k,k)))
   V,_=np.linalg.qr(rng.normal(size=(k,k))+1j*rng.normal(size=(k,k)))
   def pump(rate,W):
    z=np.zeros((d,d),complex);z[:k,k:]=np.sqrt(rate)*W
    return [np.diag([1]*k+[np.sqrt(1-rate)]*k),z]
   A=pump(a,U);B=pump(b,V);minus=[(bb@aa-aa@bb)/2 for aa in A for bb in B]
   weight=(a*(1-np.sqrt(1-b))**2+b*(1-np.sqrt(1-a))**2)/4
   res=np.linalg.norm(effect(minus)-np.diag([0]*k+[weight]*k))
   partial.append({'a':a,'b':b,'p_minus_on_error_sector':float(weight),'residual':float(res)})
 assert max(x['residual'] for x in partial)<1e-12
 ans={'seed':19031,'retraction_cases':rows,'partial_cases':partial}
 open('retraction_results.json','w').write(json.dumps(ans,indent=2))
 print('PASS',len(rows),'full-channel comparisons; max residual',max(x['full_choi_residual'] for x in rows))
if __name__=='__main__':main()
