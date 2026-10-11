#!/usr/bin/env python3
"""Exact integer/rational repair of a phase-twirled process SDP point.

The only floating operations choose dyadic Gram factors. All validity,
residual-norm bounds, objective values, and projection equalities that enter
the resulting certificate are then computed with Python integers.
Supported grids: L=1,2,4 (entries rational or in Q(sqrt(2))).
"""
import argparse,gzip,json,math,time
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from charged_grid_admm import ChargeModel

def ceil_sqrt(n):
    r=math.isqrt(int(n));return r if r*r==n else r+1
def combine(model,*terms):return {k:sum(c*A[k] for c,A in terms) for k in model.keys}
def trace(W):return sum(int(np.trace(v,axis1=1,axis2=2).sum()) for v in W.values())
def frob_square(W):return sum(int(np.sum(v*v)) for v in W.values())
def block_norm_upper(W):
    # Orthogonal setting/charge blocks: a maximum, not a sum, bounds the
    # global operator norm. Each block also admits its exact row-sum bound.
    bound=0
    for vv in W.values():
        for v in vv:
            f=ceil_sqrt(int(np.sum(v*v)))
            rows=max(int(z) for z in np.sum(np.abs(v),axis=1))
            bound=max(bound,min(f,rows))
    return bound
def add_identity(W,c):
    out={k:v.copy() for k,v in W.items()}
    for a in out.values():
        ii=np.arange(a.shape[1]);a[:,ii,ii]+=int(c)
    return out
def structured_dual_repair(E):
    # The four diagonal supports are scalar multiples of product CPTP Choi
    # operators: preserve/dephase the angle label, or fully depolarize it.
    # Hence these repairs remain in the exact dual affine space.
    bounds={'00':0,'0n':0,'n0':0,'nn':0}
    for (a,b),v in E.items():
        label=('0' if a==0 else 'n')+('0' if b==0 else 'n')
        bounds[label]=max(bounds[label],block_norm_upper({(a,b):v}))
    nn=bounds['nn'];a0=max(0,bounds['0n']-nn);b0=max(0,bounds['n0']-nn)
    zz=max(0,bounds['00']-nn-a0-b0)
    heights={k:nn+(a0 if k[0]==0 else 0)+(b0 if k[1]==0 else 0)+(zz if k==(0,0) else 0) for k in E}
    return heights,bounds,{'all_all':nn,'zero_all':a0,'all_zero':b0,'zero_zero':zz}
def add_sector_identity(W,heights):
    out={k:v.copy() for k,v in W.items()}
    for k,a in out.items():
        ii=np.arange(a.shape[1]);a[:,ii,ii]+=int(heights[k])
    return out
def p0_num(model,W):
    d=model.d
    A=model.replace_A(W,1,False);B=model.replace_B(W,1,False)
    AB=model.replace_A(B,1,False)
    AA=model.replace_A(A,0,False);AAB=model.replace_A(AB,0,False)
    BB=model.replace_B(B,0,False);ABB=model.replace_B(AB,0,False)
    out=combine(model,(2*d**3,A),(2*d**3,B),(-d*d,AB),(-2*d*d,AA),(d,AAB),(-2*d*d,BB),(d,ABB))
    return add_identity(out,-trace(W))

def objective_integer(model,L,p):
    assert L in (1,2,4)
    # P(theta)=(A+B sqrt2)/4, vectors ordered by angle then input/output qubits.
    table={0:([4,0,0,0],[0,0,0,0]),1:([2,0,0,2],[1,1,1,-1]),
           2:([2,2,2,2],[0,0,0,0]),3:([2,0,0,2],[-1,1,1,1]),4:([0,0,0,4],[0,0,0,0])}
    ps=[]
    for x in range(2):
        aa=[];bb=[]
        for j in range(L+1):
            a,b=table[(4*j//L) if x else 0];aa.extend(a);bb.extend(b)
        a=np.array(aa,dtype=object);b=np.array(bb,dtype=object)
        ident=np.tile(np.array([4,0,0,4],dtype=object),L+1)
        ps.append([(a,b),(ident-a,-b)])
    GA=model.zeros(object);GB=model.zeros(object)
    for x in range(2):
        for y in range(2):
            a,b=ps[x][y];c,d=ps[y][x]
            va=np.kron(a,c)+2*np.kron(b,d);vb=np.kron(a,d)+np.kron(b,c)
            GA[0,0][2*x+y]=np.outer(va,va)+2*np.outer(vb,vb)
            GB[0,0][2*x+y]=np.outer(va,vb)+np.outer(vb,va)
    den=1<<(2*p);bits=2*p-10;root2=math.isqrt(2*(1<<(2*bits)))
    GN=combine(model,(1<<bits,GA),(root2,GB))
    # Exact G differs from GN/den by less than ||GB||_F/den.
    err=block_norm_upper(GB)
    return GN,den,err,root2,bits

def gram_from_float(model,W,p):
    factors={};S={};scale=1<<p
    for k,a in W.items():
        vals,vecs=np.linalg.eigh(a)
        root=vecs*np.sqrt(np.maximum(vals,0))[:,None,:]
        integer=np.rint(root*scale).astype(np.int64).astype(object)
        factors[k]=integer
        S[k]=np.matmul(integer,integer.transpose(0,2,1))
    return S,factors

def certify(path,outstem,p=32):
    start=time.time();data=np.load(path);L=len(data['angles'])-1;model=ChargeModel(L+1);d=model.d;D=4*d**4
    U={k:data[f'U_{k[0]}_{k[1]}']/float(data['tau']) for k in model.keys}
    Z={k:data[f'Z_{k[0]}_{k[1]}'] for k in model.keys}
    GN,den,gerr,root2,bits=objective_integer(model,L,p)
    print('Building exact dual Gram matrices',flush=True)
    S,dual_factors=gram_from_float(model,U,p)
    T=combine(model,(1,GN),(1,S));E=p0_num(model,T);eroot=block_norm_upper(E)
    heights,sector_bounds,sector_weights=structured_dual_repair(E)
    YN=add_sector_identity(combine(model,(D,T),(-1,E)),heights)
    check=p0_num(model,YN)
    assert all(np.all(a==0) for a in check.values()),'exact dual affine orthogonality'
    upper=F(trace(YN),D*den*d*d)+F(4*d*d*gerr,den)
    print('Building exact primal Gram matrices',flush=True)
    X,primal_factors=gram_from_float(model,Z,p)
    PX=add_identity(p0_num(model,X),D*den//(d*d))
    ER=combine(model,(1,PX),(-D,X));proot=block_norm_upper(ER)
    WN=add_identity(PX,proot);wd=D*den+d*d*proot
    # Exact trace and affine constraints after white-noise repair.
    assert trace(WN)==4*d*d*wd
    Wp=p0_num(model,WN)
    Wfixed=add_identity(combine(model,(D,WN)), -(D*wd//(d*d)))
    assert all(np.all(Wp[k]==Wfixed[k]) for k in model.keys),'exact primal affine constraints'
    lower=F(sum(int(np.sum(GN[k]*WN[k])) for k in model.keys),den*wd)-F(4*d*d*gerr,den)
    # C=(1+sqrt2) pi²/16 < 3/2, checked independently by elementary bounds
    # sqrt2<99/70 and pi<22/7; the rational 3/(2L²) is safe for enclosure.
    unrestricted_upper=upper+F(3,2*L*L)
    result={'status':'exact_rational_certificate','intervals':L,'input_dimension':d,'output_dimension':2*d,
        'root_quantization_bits':p,'objective_common_denominator':str(den),
        'objective_sqrt2_lower_numerator':str(root2),'objective_sqrt2_denominator_bits':bits,
        'objective_frobenius_error_numerator':str(gerr),
        'dual_projection_norm_upper_numerator':str(eroot),'dual_projection_common_denominator':str(D*den),
        'dual_sector_norm_bounds':{k:str(v) for k,v in sector_bounds.items()},
        'dual_sector_repair_weights':{k:str(v) for k,v in sector_weights.items()},
        'primal_projection_norm_upper_numerator':str(proot),'primal_projection_common_denominator':str(D*den),
        'grid_lower_rational':str(lower),'grid_upper_rational':str(upper),
        'grid_lower_decimal':float(lower),'grid_upper_decimal':float(upper),
        'unrestricted_upper_using_3_over_2_L_squared_rational':str(unrestricted_upper),
        'unrestricted_upper_decimal':float(unrestricted_upper),'seconds':time.time()-start,
        'scope':'The grid interval is certified by exact integer arithmetic. The unrestricted upper additionally uses the audited Jordan-grid theorem; no matching optimum is claimed.'}
    Path(str(outstem)+'.json').write_text(json.dumps(result,indent=2)+'\n')
    # Gram factors are the exact PSD certificates; the verifier reconstructs
    # all operators from these integers and the explicit projection formulas.
    payload={'intervals':L,'bits':p,'dual_factors':{f'{a},{b}':v.tolist() for (a,b),v in dual_factors.items()},
             'primal_factors':{f'{a},{b}':v.tolist() for (a,b),v in primal_factors.items()}}
    with gzip.open(str(outstem)+'_gram_factors.json.gz','wt') as f:json.dump(payload,f)
    print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('input');a.add_argument('output');a.add_argument('--bits',type=int,default=32);v=a.parse_args();certify(v.input,v.output,v.bits)
