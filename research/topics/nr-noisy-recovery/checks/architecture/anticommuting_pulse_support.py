"""Exact finite rank certificate for the universal two-query success support.

This is a necessary-support proof, not a success-probability bound.
Only Fraction and integer modular arithmetic are used.
"""
from fractions import Fraction as F
from itertools import product
import json

PRIME = 1000003

def require(condition, message):
    if not condition:
        raise ValueError(message)

def frame(q):
    w,x,y,z=q
    n=w*w+x*x+y*y+z*z
    require(n>0, "nonzero quaternion")
    m=((w*w+x*x-y*y-z*z,2*(x*y-w*z),2*(x*z+w*y)),
       (2*(x*y+w*z),w*w-x*x+y*y-z*z,2*(y*z-w*x)),
       (2*(x*z-w*y),2*(y*z+w*x),w*w-x*x-y*y+z*z))
    r=[[F(t,n) for t in row] for row in m]
    a=[r[i][2] for i in range(3)]
    b=[r[i][0] for i in range(3)]
    require(sum(t*t for t in a)==sum(t*t for t in b)==1, "unit axes")
    require(sum(x*y for x,y in zip(a,b))==0, "orthogonal axes")
    return a,b

def features(a,b):
    # Feature index is (B index, A index), with 0 denoting identity.
    aa=[F(1)]+a;bb=[F(1)]+b
    return [bb[i]*aa[j] for i,j in product(range(4),repeat=2)]

def rows(q):
    a,b=frame(q);f=features(a,b);out=[]
    for i in range(3):
        row=[F(0)]*64
        row[:16]=[-(a[i]+b[i])*t for t in f]
        row[(i+1)*16:(i+2)*16]=f
        out.append(row)
    return out

def modrank(matrix):
    a=[[int(t.numerator%PRIME)*pow(int(t.denominator%PRIME),-1,PRIME)%PRIME
        for t in row] for row in matrix]
    rank=0;pivots=[]
    for col in range(64):
        k=next((k for k in range(rank,len(a)) if a[k][col]),None)
        if k is None:continue
        a[rank],a[k]=a[k],a[rank]
        inverse=pow(a[rank][col],-1,PRIME)
        a[rank]=[(t*inverse)%PRIME for t in a[rank]]
        for k in range(rank+1,len(a)):
            c=a[k][col]
            if c:a[k]=[(u-c*v)%PRIME for u,v in zip(a[k],a[rank])]
        pivots.append(col);rank+=1
        if rank==len(a):break
    return rank,pivots

def basis():
    out=[]
    # Four independent maps into each output coefficient, annihilated by A dot B.
    for o in range(4):
        v=[F(0)]*64
        for i in (1,2,3):v[o*16+4*i+i]=1
        out.append(v)
    # The proper map Z0=1, Zi=A_i+B_i.
    v=[F(0)]*64;v[0]=1
    for i in (1,2,3):
        v[i*16+i]=1
        v[i*16+4*i]=1
    out.append(v)
    return out

def verify():
    require(all(PRIME%d for d in range(2,1001)), "rank modulus is prime")
    # These are actual rational SO(3) frames, not merely formal polynomial points.
    candidates=[(1,x,y,z) for x,y,z in product(range(-2,3),repeat=3)]
    selected=[];matrix=[];rank=0
    for q in candidates:
        trial=matrix+rows(q)
        value,pivots=modrank(trial)
        if value>rank:
            selected.append(q);matrix=trial;rank=value
        if rank==59:break
    require(rank==59, "rank59 necessary-support certificate")
    vectors=basis()
    for row in matrix:
        for v in vectors:
            require(sum(x*y for x,y in zip(row,v))==0,"five exact kernel vectors")
    require(modrank(vectors)[0]==5, "five independent universal kernel vectors")
    rank,pivots=modrank(matrix)
    return {"status":"passed","prime":PRIME,"rank":rank,
            "ambient_dimension":64,"kernel_dimension":5,
            "quaternions":[list(q) for q in selected],"pivots":pivots,
            "exact_kernel_vectors":5,
            "scope":"Universal necessary two-query exact-success support for two unknown orthogonal qubit involutions, nonzero fixed sine/cosine pulse coefficients. Finite rational frames imply rank>=59 and five universal algebraic vectors imply rank<=59. No causal normalization, success-probability bound, adaptive-angle inclusion or hardware statement."}

if __name__=='__main__':
    print(json.dumps(verify(),sort_keys=True))
