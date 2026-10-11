#!/usr/bin/env python3
"""Phase-twirled fixed-grid process SDP; NumPy only.

Keeps every local charge sector. In particular it does not discard unequal
input/output angle labels, whose traces constrain the zero-charge block.
"""
import argparse,json,time
from pathlib import Path
import numpy as np
from grid_process_admm import objective,linear_project as full_project

class ChargeModel:
    def __init__(self,K):
        self.K=K;self.d=2*K
        self.sectors=[None]+[(i,j) for i in range(K) for j in range(K) if i!=j]
        self.groups=[];self.indices=[];self.sizes=[]
        for s in self.sectors:
            pairs=[(i,i) for i in range(K)] if s is None else [s]
            self.groups.append([(i,j,4*k) for k,(i,j) in enumerate(pairs)])
            inds=[(2*i+a)*self.d+(2*j+b) for i,j in pairs for a in range(2) for b in range(2)]
            self.indices.append(np.array(inds));self.sizes.append(len(inds))
        self.keys=[(a,b) for a in range(len(self.sectors)) for b in range(len(self.sectors))]
        self.bysize={}
        for a,b in self.keys:self.bysize.setdefault(self.sizes[a]*self.sizes[b],[]).append((a,b))
    def zeros(self,dtype=float):return {(a,b):np.zeros((4,self.sizes[a]*self.sizes[b],self.sizes[a]*self.sizes[b]),dtype=dtype) for a,b in self.keys}
    def eye(self,scale=1):return {(a,b):np.repeat((scale*np.eye(self.sizes[a]*self.sizes[b]))[None,:,:],4,axis=0) for a,b in self.keys}
    def trace(self,W):return sum(np.trace(v,axis1=1,axis2=2).sum() for v in W.values())
    def dot(self,W,V):return sum(float(np.sum(W[k]*V[k])) for k in self.keys)
    def norm(self,W):return np.sqrt(self.dot(W,W))
    def combine(self,*terms):return {k:sum(c*A[k] for c,A in terms) for k in self.keys}
    def swap(self,W):
        out={}
        for a,b in self.keys:
            da,db=self.sizes[a],self.sizes[b]
            out[b,a]=W[a,b].reshape(2,2,da,db,da,db).transpose(1,0,3,2,5,4).reshape(4,da*db,da*db)
        return out
    def replace_A(self,W,port,normalize=True):
        # port=1 traces/replaces A_O, including the setting flag;
        # port=0 traces/replaces A_I and preserves both setting flags.
        dtype=object if next(iter(W.values())).dtype==object else float
        T={(i,b):np.zeros((4,2*self.sizes[b],2*self.sizes[b]),dtype=dtype) for i in range(self.K) for b in range(len(self.sectors))}
        for a,b in self.keys:
            da,db=self.sizes[a],self.sizes[b]
            ww=W[a,b].reshape(4,da,db,da,db)
            for i,j,start in self.groups[a]:
                ss=ww[:,start:start+4,:,start:start+4,:].reshape(4,2,2,db,2,2,db)
                tr=np.einsum('xiobjoc->xibjc',ss) if port else np.einsum('xiobipc->xobpc',ss)
                T[(i if port else j),b]+=tr.reshape(4,2*db,2*db)
        for k,t in T.items():
            if port:
                z=t.reshape(2,2,*t.shape[1:]).sum(axis=0)
                if normalize:z=z/(2*self.d)
                T[k]=np.stack([z,z]).reshape(t.shape)
            elif normalize:T[k]=t/self.d
        out=self.zeros(dtype);eye=np.eye(2,dtype=dtype)
        for a,b in self.keys:
            da,db=self.sizes[a],self.sizes[b];oo=out[a,b].reshape(4,da,db,da,db)
            for i,j,start in self.groups[a]:
                t=T[(i if port else j),b].reshape(4,2,db,2,db)
                emb=np.einsum('xibjc,op->xiobjpc',t,eye) if port else np.einsum('xobpc,ij->xiobjpc',t,eye)
                oo[:,start:start+4,:,start:start+4,:]=emb.reshape(4,4,db,4,db)
        return out
    def replace_B(self,W,port,normalize=True):return self.swap(self.replace_A(self.swap(W),port,normalize))
    def linear_project(self,W):
        A=self.replace_A(W,1);B=self.replace_B(W,1);AB=self.replace_A(B,1)
        AI_A=self.replace_A(A,0);AI_AB=self.replace_A(AB,0)
        BI_B=self.replace_B(B,0);BI_AB=self.replace_B(AB,0)
        return self.combine((1,A),(1,B),(-1,AB),(-1,AI_A),(1,AI_AB),(-1,BI_B),(1,BI_AB))
    def affine_project(self,W):
        out=self.linear_project(W)
        shift=(4*self.d*self.d-self.trace(W))/(4*self.d**4)
        for k,z in out.items():z+=shift*np.eye(len(z[0]))[None,:,:]
        return out
    def psd(self,W):
        out={};minv=0.
        for size,keys in self.bysize.items():
            stack=np.concatenate([W[k] for k in keys],axis=0)
            vals,vecs=np.linalg.eigh(stack);minv=min(minv,float(vals.min()))
            arr=np.matmul(vecs*np.maximum(vals,0)[:,None,:],vecs.transpose(0,2,1))
            for j,k in enumerate(keys):out[k]=arr[4*j:4*j+4].copy()
        return out,minv
    def from_full(self,W):
        out={}
        for a,b in self.keys:
            idx=(self.indices[a][:,None]*self.d**2+self.indices[b][None,:]).ravel()
            out[a,b]=W[:,idx[:,None],idx[None,:]].copy()
        return out
    def to_full(self,W):
        out=np.zeros((4,self.d**4,self.d**4))
        for a,b in self.keys:
            idx=(self.indices[a][:,None]*self.d**2+self.indices[b][None,:]).ravel()
            out[:,idx[:,None],idx[None,:]]=W[a,b]
        return out
    def objective(self,angles):
        # Objective is supported entirely in the zero/zero charge block.
        K=self.K;d=self.d;ps=[]
        for x in range(2):
            vec=[]
            for t in angles:
                if x==0:P=np.diag([1.,0.])
                elif abs(t)<1e-14:P=np.diag([1.,0.])
                elif abs(t-np.pi/2)<1e-14:P=np.diag([0.,1.])
                elif abs(t-np.pi/4)<1e-14:P=np.full((2,2),.5)
                else:
                    v=np.array([np.cos(t),np.sin(t)]);P=np.outer(v,v)
                vec.append(P.reshape(-1))
            v0=np.concatenate(vec);v1=np.tile(np.eye(2).reshape(-1),K)-v0
            ps.append([v0,v1])
        G=self.zeros()
        for x in range(2):
            for y in range(2):
                v=np.kron(ps[x][y],ps[y][x]);G[0,0][2*x+y]=np.outer(v,v)/4
        return G

def test_model():
    model=ChargeModel(2);rng=np.random.default_rng(90311);W=model.zeros()
    for k,z in W.items():
        z[:]=rng.normal(size=z.shape);z[:]=(z+z.transpose(0,2,1))/2
    P=model.linear_project(W);full=model.to_full(W)
    residual=np.max(np.abs(model.to_full(P)-full_project(full,model.d)))
    assert residual<1e-12,residual
    assert abs(model.dot(P,P)-model.dot(W,P))<1e-9
    for angles in ([0,np.pi/2],[.1,.9]):
        assert np.max(np.abs(model.to_full(model.objective(angles))-objective(angles)))<1e-12
    return residual

def solve(L,iterations,tol,stem):
    testres=test_model();K=L+1;model=ChargeModel(K);angles=list(np.linspace(0,np.pi/2,K));G=model.objective(angles)
    Z=model.eye(1/model.d**2);U=model.zeros();tau=1.;logs=[];start=time.time()
    for it in range(1,iterations+1):
        X,_=model.psd(model.combine((1,Z),(-1,U)))
        old=Z;Z=model.affine_project(model.combine((1,X),(1,U),(tau,G)))
        U=model.combine((1,U),(1,X),(-1,Z))
        rp=model.norm(model.combine((1,X),(-1,Z)));rd=model.norm(model.combine((1,Z),(-1,old)))/tau
        if it==1 or it%50==0 or (rp<tol and rd<tol):
            _,mn=model.psd(U);delta=max(0,-mn)/tau
            primal=model.dot(G,Z);dual=(model.trace(G)+model.trace(U)/tau)/model.d**2+delta*4*model.d**2
            row={'iteration':it,'primal_value':primal,'repaired_dual_value_float':dual,'primal_residual':rp,'dual_residual':rd,'dual_psd_repair':delta,'seconds':time.time()-start}
            logs.append(row);print(json.dumps(row),flush=True)
        if it%100==0 or it==iterations or (rp<tol and rd<tol):
            arrays={f'Z_{a}_{b}':Z[a,b] for a,b in model.keys};arrays.update({f'U_{a}_{b}':U[a,b] for a,b in model.keys})
            arrays['angles']=np.array(angles);arrays['tau']=np.array(tau)
            np.savez_compressed(str(stem)+'.npz',**arrays)
            Path(str(stem)+'.json').write_text(json.dumps({'status':'exploratory','intervals':L,'input_dimension':model.d,'output_dimension':2*model.d,'largest_PSD_block':16*K*K,'projection_test_residual':testres,'logs':logs,'warning':'Floating diagnostics; use exact certificate plus analytic grid error for a universal bound.'},indent=2)+'\n')
        if rp<tol and rd<tol:break

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--intervals',type=int,required=True);p.add_argument('--iterations',type=int,default=3000);p.add_argument('--tol',type=float,default=1e-8);p.add_argument('--stem',required=True)
    a=p.parse_args();solve(a.intervals,a.iterations,a.tol,a.stem)
