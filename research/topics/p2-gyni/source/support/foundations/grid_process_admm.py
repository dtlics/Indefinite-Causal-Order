#!/usr/bin/env python3
"""Fixed-instrument process SDP, using only NumPy.

Exploratory solver, not a numerical claim of an unrestricted optimum.
The exact affine projector and the canonical labelled instruments implement
the structural grid reduction in jordan_grid_reduction.md.
"""
import argparse,json,time
from pathlib import Path
import numpy as np

def embed_rho(rho,d):
    return np.einsum('ikjl,ab,cd->iakcjbld',rho.reshape((d,)*4),np.eye(d),np.eye(d)).reshape(d**4,d**4)

def linear_project(W,d):
    blocks=W.reshape((2,2)+(d,)*8)
    rho=np.zeros((d,)*4)
    for x in range(2):
        for y in range(2):rho+=np.einsum('iakcjalc->ikjl',blocks[x,y])/(4*d*d)
    xr=[];yr=[];eye=np.eye(d)
    for y in range(2):
        z=sum(np.einsum('iakcjald->ikcjld',blocks[x,y]) for x in range(2))/(2*d)
        z-=np.einsum('ikjl,cd->ikcjld',rho,eye)
        z-=np.einsum('kcld,ij->ikcjld',np.einsum('ikcild->kcld',z),eye/d)
        xr.append(z)
    for x in range(2):
        z=sum(np.einsum('iakcjblc->iakjbl',blocks[x,y]) for y in range(2))/(2*d)
        z-=np.einsum('ikjl,ab->iakjbl',rho,eye)
        z-=np.einsum('iajb,kl->iakjbl',np.einsum('iakjbk->iajb',z),eye/d)
        yr.append(z)
    base=embed_rho(rho,d);out=np.empty_like(W)
    for x in range(2):
        for y in range(2):
            out[2*x+y]=base+np.einsum('ikcjld,ab->iakcjbld',xr[y],eye).reshape(d**4,d**4)+np.einsum('iakjbl,cd->iakcjbld',yr[x],eye).reshape(d**4,d**4)
    return out

def homogeneous_project(W,d):
    out=linear_project(W,d)
    scalar=sum(np.trace(a) for a in W)/(4*d**4)
    return out-scalar*np.eye(d**4)[None,:,:]

def affine_project(W,d):
    return homogeneous_project(W,d)+np.eye(d**4)[None,:,:]/d**2

def instruments(angles):
    K=len(angles);d=2*K
    P=np.zeros((d,d));Q=np.zeros((d,d))
    for j,t in enumerate(angles):
        P[2*j,2*j]=1
        if abs(t)<1e-14:block=np.diag([1.,0.])
        elif abs(t-np.pi/2)<1e-14:block=np.diag([0.,1.])
        elif abs(t-np.pi/4)<1e-14:block=np.full((2,2),.5)
        else:
            v=np.array([np.cos(t),np.sin(t)]);block=np.outer(v,v)
        Q[2*j:2*j+2,2*j:2*j+2]=block
    ps=[[P,np.eye(d)-P],[Q,np.eye(d)-Q]]
    return [[np.outer(z.reshape(-1),z.reshape(-1)) for z in row] for row in ps]

def objective(angles):
    M=instruments(angles)
    return np.stack([np.kron(M[x][y],M[y][x])/4 for x in range(2) for y in range(2)])

def solve(angles,iterations,tol,stem):
    d=2*len(angles);D=d**4;G=objective(angles)
    rng=np.random.default_rng(1991)
    r=rng.normal(size=(4,D,D));r=(r+r.transpose(0,2,1))/2
    pr=linear_project(r,d)
    assert np.max(np.abs(linear_project(pr,d)-pr))<1e-10
    assert abs(np.sum(r*pr)-np.sum(pr*pr))<1e-8
    Z=np.repeat((np.eye(D)/d**2)[None,:,:],4,axis=0);U=np.zeros_like(Z);tau=1.
    logs=[];start=time.time()
    for it in range(1,iterations+1):
        vals,vecs=np.linalg.eigh(Z-U)
        X=np.matmul(vecs*np.maximum(vals,0)[:,None,:],vecs.transpose(0,2,1))
        old=Z;Z=affine_project(X+U+tau*G,d);U+=X-Z
        rp=np.linalg.norm(X-Z);rd=np.linalg.norm(Z-old)/tau
        if it==1 or it%100==0 or (rp<tol and rd<tol):
            Y=G+U/tau;S=U/tau
            minS=min(np.linalg.eigvalsh(S).ravel());delta=max(0.,-minS)
            primal=float(np.sum(G*Z))
            dual=float(sum(np.trace(y) for y in Y)/d**2+delta*4*d*d)
            row={'iteration':it,'primal_value':primal,'repaired_dual_value_float':dual,'primal_residual':float(rp),'dual_residual':float(rd),'dual_psd_repair':float(delta),'seconds':time.time()-start}
            logs.append(row);print(json.dumps(row),flush=True)
        if rp<tol and rd<tol:break
    Path(stem).parent.mkdir(parents=True,exist_ok=True)
    np.savez_compressed(str(stem)+'.npz',Z=Z,U=U,G=G,X=X,angles=np.array(angles),tau=np.array(tau))
    result={'status':'exploratory','angles':angles,'input_dimension':d,'output_dimension':2*d,'flag_block_dimension':D,'iterations':it,'logs':logs,'warning':'Floating SDP diagnostics only; no unrestricted optimum or exact certificate is asserted.'}
    Path(str(stem)+'.json').write_text(json.dumps(result,indent=2)+'\n')
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--intervals',type=int,default=1);p.add_argument('--single-angle',type=float);p.add_argument('--iterations',type=int,default=10000);p.add_argument('--tol',type=float,default=1e-8);p.add_argument('--stem',required=True)
    args=p.parse_args()
    angles=[args.single_angle] if args.single_angle is not None else list(np.linspace(0,np.pi/2,args.intervals+1))
    solve(angles,args.iterations,args.tol,args.stem)
