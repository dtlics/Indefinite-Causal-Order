import itertools, math, json
from pathlib import Path
import numpy as np
from scipy.linalg import eigh

def cross_exp(pi, sig, kind):
    m=len(pi); par=list(range(2*m)); marks={}
    def root(x):
        while par[x]!=x:
            par[x]=par[par[x]]; x=par[x]
        return x
    def union(x,y):
        x,y=root(x),root(y)
        if x!=y: par[y]=x
    for p in (pi,sig):
        for t in range(1,m): union(m+p[t],p[t-1])
    if kind=='id':
        fixed=[(m+pi[0],0),(m+sig[0],1),(pi[-1],0),(sig[-1],1)]
    else:
        fixed=[(m+pi[0],0),(m+sig[0],0),(pi[-1],1),(sig[-1],1)]
    for i,x in fixed:
        r=root(i)
        if r in marks and marks[r]!=x:return None
        marks[r]=x
    comps={root(i) for i in range(2*m)}
    return len(comps)-len(marks)-m+(kind=='dep')

def matrices(m,d):
    ps=list(itertools.permutations(range(m))); ind={p:i for i,p in enumerate(ps)}
    ae=[cross_exp(ps[0],p,'id') for p in ps]
    be=[cross_exp(ps[0],p,'dep') for p in ps]
    avec=np.array([0 if a is None else float(d)**a for a in ae])
    bvec=np.array([0 if a is None else float(d)**a for a in be])
    A=np.empty((len(ps),len(ps)));B=np.empty_like(A)
    for i,p in enumerate(ps):
        inv=[0]*m
        for j,x in enumerate(p):inv[x]=j
        ids=np.array([ind[tuple(inv[x] for x in s)] for s in ps])
        A[i]=avec[ids];B[i]=bvec[ids]
    assert np.max(abs(A-A.T))<1e-12 and np.max(abs(B-B.T))<1e-12
    return ps,A,B,ae,be

def opt(m,d):
    ps,A,B,ae,be=matrices(m,d);G=A+B;H=A+B/d**2
    ev,Q=eigh(G); keep=ev>1e-10
    W=Q[:,keep]/np.sqrt(ev[keep])[None,:]
    vals,Z=eigh(W.T@H@W); w=W@Z[:,-1];w/=np.linalg.norm(w)
    r= len(ps);p=float(w@G@w/r); F=float(vals[-1])
    cyc=[tuple(list(range(m))[j:]+list(range(m))[:j]) for j in range(m)]
    inds=[ps.index(s) for s in cyc];z=np.zeros(r);z[inds]=1/m
    pc=float(z@G@z);fc=float(z@H@z/pc)
    return dict(m=m,d=d,dimension=r,rank=int(sum(keep)),Fmax=F,p_uniform=p,F_cyclic=fc,p_cyclic=pc,filter={str(ps[i]):float(x) for i,x in enumerate(w) if abs(x)>1e-8}), (ps,A,B,w)
if __name__=='__main__':
    out=[]
    for m in range(2,6):
        for d in (2,3,4,8,16):
            r,_=opt(m,d);out.append(r);print({k:v for k,v in r.items() if k!='filter'},flush=True)
    Path(__file__).with_name('permutation_scan.json').write_text(json.dumps(out,indent=2))
