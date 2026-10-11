#!/usr/bin/env python3
"""Exact rational-denominator universal NS completion certificate/replay."""
import argparse,gzip,json,math,sys,time
from fractions import Fraction as F
from pathlib import Path
import numpy as np
def reduce_word(seq):
    out=[]
    for x in seq:
        if out and out[-1]==x:out.pop()
        else:out.append(x)
    return tuple(out)
def to_tensor(H,n):return H.reshape(2,2,n,n,n,n).transpose(0,2,4,1,3,5).reshape(2*n*n,2*n*n)
def from_tensor(T,n):return T.reshape(2,n,n,2,n,n).transpose(0,3,1,4,2,5).reshape(4,n*n,n*n)

def setup(level,r):
    ws=[()]+[tuple((b+j)%2 for j in range(l)) for l in range(1,level+1) for b in range(2)];n=len(ws);p,q=r.numerator,r.denominator
    qq={():p*p+q*q,(0,1):p*q,(1,0):p*q};q2={}
    for u,a in qq.items():
        for v,b in qq.items():
            w=reduce_word(u+v);q2[w]=q2.get(w,0)+a*b
    groups={}
    for x in range(2):
        for u in range(n):
            for v in range(n):
                w=reduce_word(tuple(reversed(ws[v]))+ws[u]);groups.setdefault(w,[]).append((x*n+u)*n+v)
    gw=list(groups);gr=[np.array(groups[w]) for w in gw];t=[q2.get(w,0) for w in gw]
    M=math.lcm(*[len(g) for g in gr]);aw=[a*(M//len(g)) for a,g in zip(t,gr)];A=sum(a*b for a,b in zip(t,aw));B=M*A
    target=[]
    for x in range(2):
        for y in range(2):
            ca=np.zeros(n,dtype=object);cb=np.zeros(n,dtype=object)
            for w,a in qq.items():
                ca[ws.index(w)]+=a;ca[ws.index(reduce_word(w+(x,)))]+=a*(-1)**y
                cb[ws.index(w)]+=a;cb[ws.index(reduce_word(w+(y,)))]+=a*(-1)**x
            k=np.kron(ca,cb);target.append(np.outer(k,k))
    td=64*q**8;alpha=q2[()];beta=q2[(0,1)];gamma=q2[(0,1,0,1)];mu=alpha-2*beta-2*gamma
    assert mu>0 and level>=4
    J=mu*np.eye(n,dtype=object);e=np.zeros(n,dtype=object);e[0]=1;J+=n*mu*np.outer(e,e)
    for coeff,w in [(beta,(0,1)),(gamma,(0,1,0,1))]:
        v=e.copy();v[ws.index(w)]+=1;J+=2*n*coeff*np.outer(v,v)
    # Verify the advertised positive Gram's unit-scale marginal polynomial.
    agg={}
    for u in range(n):
        for v in range(n):
            w=reduce_word(tuple(reversed(ws[v]))+ws[u]);agg[w]=agg.get(w,0)+int(J[u,v])
    assert all(v==2*n*q2.get(w,0) for w,v in agg.items())
    return ws,gr,t,M,aw,A,B,np.array(target,dtype=object),td,alpha,mu,J,q

def project(H,n,gr,t,M,aw,A,B):
    T=to_tensor(H,n).copy()
    for axis in [1,0]:
        if axis==0:T=T.T
        ss=[T[:,g].sum(axis=1) for g in gr];agg=sum(a*s for a,s in zip(aw,ss));N=B*T
        for g,tw,s in zip(gr,t,ss):N[:,g]-=((M//len(g))*(A*s-tw*agg))[:,None]
        T=N
        if axis==0:T=T.T
    return from_tensor(T,n)

def verify_data(data):
    st=time.time();r=F(data['r']);level=data['level'];bits=data['bits'];ws,gr,t,M,aw,A,B,tar,td,alpha,mu,J,q=setup(level,r);n=len(ws)
    factors=np.array(data['factors'],dtype=object);gd=1<<(2*bits);D=math.lcm(td,gd)
    H0=tar*(D//td)+np.array([x@x.T for x in factors],dtype=object)*(D//gd)
    P=project(H0,n,gr,t,M,aw,A,B);Ed=H0*(B*B)-P
    errs=[]
    for E in Ed:
        sq=sum(int(z)*int(z) for z in E.ravel());f=math.isqrt(sq);f+=f*f<sq
        row=max(sum(abs(int(z)) for z in rr) for rr in E);errs.append(min(f,row))
    err=max(errs);Hden=mu*mu*D*B*B;Hnum=mu*mu*P+err*np.kron(J,J)[None,:,:]
    TT=to_tensor(Hnum,n);i0=t.index(q**4+4*r.numerator**2*q*q+r.numerator**4) # identity coefficient is unique here
    # Explicit proportional-overlap NS checks on BOTH local sides.
    checks=0
    for T in (TT,TT.T):
        sums=[T[:,g].sum(axis=1) for g in gr];s0=sums[i0]
        for s,tw in zip(sums,t):
            assert np.array_equal(alpha*s,tw*s0);checks+=len(s)
    assert all(np.array_equal(h,h.T) for h in Hnum)
    tr=sum(sum(int(h[i,i]) for i in range(n*n)) for h in Hnum)
    bound=F(tr*q**8,Hden*alpha*alpha)
    base=F(sum(sum(int(h[i,i]) for i in range(n*n)) for h in P)*q**8,D*B*B*alpha*alpha)
    repair=bound-base
    out={'status':'VERIFIED_EXACT_RATIONAL_KERNEL','r':str(r),'word_length':level,'word_count':n,'Gram_dimension':n*n,'upper_rational':str(bound),'upper_decimal_for_display':float(bound),'NS_proportional_coefficient_checks':checks,'repair_cost_rational':str(repair),'repair_cost_decimal_for_display':float(repair),'seconds':time.time()-st,'scope':'Universal rational-Laurent Kraus completion, exact integer PSD repair and flag-wise NS identities. No angle-grid error. Does not prove optimality.'}
    return out

def main():
    p=argparse.ArgumentParser();p.add_argument('--input');p.add_argument('--stem');p.add_argument('--level',type=int,default=5);p.add_argument('--r',default='2/25');p.add_argument('--bits',type=int,default=48);p.add_argument('--verify');a=p.parse_args()
    if a.verify:
        data=json.load(gzip.open(a.verify,'rt'));out=verify_data(data);print(json.dumps(out,indent=2));return
    vals=np.load(a.input);r=F(a.r);*_,tar,td,alpha,mu,J,q=setup(a.level,r)
    factors=[]
    for i in range(4):
        slack=vals[f'H_{i}']-np.asarray(tar[i],dtype=float)/td;ev,V=np.linalg.eigh((slack+slack.T)/2);root=V*np.sqrt(np.maximum(ev,0))[None,:]
        factors.append(np.rint(root*(1<<a.bits)).astype(np.int64).tolist())
    data={'kind':'rational_kernel_slack_Gram_factors','r':str(r),'level':a.level,'bits':a.bits,'factors':factors};out=verify_data(data)
    with gzip.open(a.stem+'_factors.json.gz','wt') as f:json.dump(data,f)
    Path(a.stem+'.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
