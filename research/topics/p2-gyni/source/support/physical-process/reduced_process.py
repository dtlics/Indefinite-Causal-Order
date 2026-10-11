"""Exact finite-algebra process reduction and CP output-repair lift.
Numerical implementation; mathematical derivation in reduced_process_theorem.md.
"""
import sys,json,time
from pathlib import Path
import numpy as np
ROOT=Path(str(Path(__file__).resolve().parents[1]/'foundations'));sys.path.insert(0,str(ROOT))
from charged_grid_admm import ChargeModel

class ReducedProcess:
 def __init__(self,K):self.K=K;self.n=4*K;self.N=self.n*self.n
 def eye(self,scale=1):return np.tile((scale*np.eye(self.N))[None],(4,1,1))
 def trace(self,W):return np.trace(W,axis1=1,axis2=2).sum()
 def swap(self,W):
  n=self.n
  return W.reshape(2,2,n,n,n,n).transpose(1,0,3,2,5,4).reshape(4,n*n,n*n)
 def RA(self,W):
  K,n=self.K,self.n;z=W.reshape(2,2,n,n,n,n);out=np.zeros_like(z)
  for j in range(K):
   s=slice(4*j,4*j+4);v=z[:,:,s,:,s,:].reshape(2,2,2,2,n,2,2,n)
   t=np.einsum('xyiobjoc->yibjc',v)/4
   e=np.einsum('yibjc,op->yiobjpc',t,np.eye(2)).reshape(2,4,n,4,n)
   out[:,:,s,:,s,:]=e[None]
  return out.reshape(W.shape)
 def DA(self,W):
  n=self.n;z=W.reshape(2,2,n,n,n,n);t=np.einsum('xyabac->ybc',z)/(2*n)
  return np.broadcast_to(np.einsum('ybc,ad->yabdc',t,np.eye(n))[None],z.shape).copy().reshape(W.shape)
 def RB(self,W):return self.swap(self.RA(self.swap(W)))
 def DB(self,W):return self.swap(self.DA(self.swap(W)))
 def linear(self,W):
  A=self.RA(W);B=self.RB(W);AB=self.RA(B)
  return A+B-AB-self.DA(W)+self.DA(B)-self.DB(W)+self.DB(A)
 def affine(self,W):return self.linear(W)+(16-self.trace(W))/(4*self.N)*np.eye(self.N)[None]
 def tangent(self,W):return self.linear(W)-self.trace(W)/(4*self.N)*np.eye(self.N)[None]
 def objective(self,angles):return ChargeModel(self.K).objective(angles)[0,0]
 def lift(self,W):
  """Each leakage sector has output maximally mixed repair, adjointed.
  Retain all zero/nonzero phase-charge sectors of the full physical process.
  """
  m=ChargeModel(self.K);out=m.zeros();out[0,0]=W.copy();n=self.n
  def addA(out,bs):
   for i in range(self.K):
    for b in bs:
     db=m.sizes[b]
     z=out[0,b].reshape(4,n,db,n,db)[:,4*i:4*i+4,:,4*i:4*i+4,:].reshape(4,2,2,db,2,2,db)
     t=np.einsum('xiobjoc->xibjc',z)/2
     emb=np.einsum('xibjc,op->xiobjpc',t,np.eye(2)).reshape(4,4*db,4*db)
     for j in range(self.K):
      if j!=i:out[m.sectors.index((i,j)),b]=emb.copy()
   return out
  out=addA(out,[0]);out=m.swap(addA(m.swap(out),range(len(m.sectors))))
  return out

def test():
 rng=np.random.default_rng(921887);reports=[]
 for K in [1,2,3]:
  r=ReducedProcess(K);m=ChargeModel(K);W=r.eye(0);W[:]=rng.normal(size=W.shape);W=(W+W.transpose(0,2,1))/2
  P=r.linear(W);Z=r.affine(W);lift=r.lift(Z)
  rows={'K':K,'projector_idempotence':float(np.linalg.norm(r.linear(P)-P)),'projector_selfadjoint':float(abs(np.sum(P*P)-np.sum(P*W))),'RA_idempotence':float(np.linalg.norm(r.RA(r.RA(W))-r.RA(W))),'DA_RA':float(np.linalg.norm(r.DA(r.RA(W))-r.DA(W))),'lift_affine_error':m.norm(m.combine((1,lift),(-1,m.affine_project(lift)))),'lift_trace':float(m.trace(lift)),'expected_trace':4*m.d*m.d}
  assert max(rows[k] for k in ['projector_idempotence','projector_selfadjoint','RA_idempotence','DA_RA','lift_affine_error'])<1e-9,rows
  # Strictly positive reduced point repaired by uniform shift; CP lift stays PSD.
  shift=max(0,-float(np.linalg.eigvalsh(Z).min()))+.1;Z=(Z+shift*np.eye(r.N)[None])/(1+r.K*r.K*4*shift)
  lift=r.lift(Z);rows['positive_lift_min_eigenvalue']=min(float(np.linalg.eigvalsh(z).min()) for z in lift.values())
  assert rows['positive_lift_min_eigenvalue']>0
  th=np.linspace(0,np.pi/2,K);rows['score_lift_error']=abs(float(np.sum(r.objective(th)*Z))-m.dot(m.objective(th),lift));assert rows['score_lift_error']<1e-12
  reports.append(rows)
 old=np.load(ROOT/'added_angle_K6_snapshot.npz');r=ReducedProcess(6);z=old['Z_0_0'];reports.append({'K':6,'existing_reduced_affine_error':float(np.linalg.norm(z-r.affine(z))),'zero_zero_trace':r.trace(z)})
 assert reports[-1]['existing_reduced_affine_error']<1e-9
 Path(__file__).with_name('reduced_process_checks.json').write_text(json.dumps(reports,indent=2)+'\n');print(json.dumps(reports,indent=2))
if __name__=='__main__':test()
