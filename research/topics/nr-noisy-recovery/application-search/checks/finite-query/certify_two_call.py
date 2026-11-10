#!/usr/bin/env python3
"""Exact rational certificate: a two-query quantum-switch advantage at d=4.

Default: independently reconstruct Haar moments, verify a supplied causal-tester
 dual, and check strict PSD block by block using rational LDL decomposition.
No floating-point computation is used by the verifier. Standard library only.

--generate reads a numerical candidate, rounds/project it, and writes a rational
certificate. Generation requires numpy, but the verification does not trust it.
"""
from __future__ import annotations
import argparse, itertools, json, math, time
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path

HERE=Path(__file__).resolve().parent

def zeros(n): return [[F(0) for _ in range(n)] for _ in range(n)]
def index(x,d):
    v=0
    for t in x:v=d*v+t
    return v

def ptr_last(x,d):
    m=len(x)//d
    return [[sum((x[a*d+t][b*d+t] for t in range(d)),F(0)) for b in range(m)] for a in range(m)]

def kron_identity(x,d):
    m=len(x);out=zeros(m*d)
    for a in range(m):
        for b in range(m):
            if x[a][b]:
                for t in range(d):out[a*d+t][b*d+t]=x[a][b]
    return out

def add_scaled(x,y,s=F(1)):
    for i in range(len(x)):
        for j in range(len(x)):
            if y[i][j]:x[i][j]+=s*y[i][j]

def linsolve(a,b):
    n=len(b);v=[[F(x) for x in row]+[F(bi)] for row,bi in zip(a,b)]
    for k in range(n):
        pivot=next(i for i in range(k,n) if v[i][k])
        v[k],v[pivot]=v[pivot],v[k]
        z=v[k][k];v[k]=[x/z for x in v[k]]
        for i in range(k+1,n):
            z=v[i][k]
            if z:
                v[i]=[a-z*b for a,b in zip(v[i],v[k])]
    out=[F(0)]*n
    for i in range(n-1,-1,-1):out[i]=v[i][-1]-sum((v[i][j]*out[j] for j in range(i+1,n)),F(0))
    return out

def cycles(p):
    visited=set();count=0
    for j in range(len(p)):
        if j not in visited:
            count+=1;k=j
            while k not in visited:visited.add(k);k=p[k]
    return count

def moment_difference(d):
    """Unnormalized Choi difference in factor order AI,AO,BI,BO."""
    perms=list(itertools.permutations(range(4)))
    gram=[]
    for p in perms:
        inv=[p.index(i) for i in range(4)]
        gram.append([d**cycles(tuple(inv[q[i]] for i in range(4))) for q in perms])
    rhs=[F(1) if set(p[:2])=={0,1} and set(p[2:])=={2,3} else F(1,d) for p in perms]
    coeff=linsolve(gram,rhs)
    out=zeros(d**4)
    for p,c in zip(perms,coeff):
        if not c:continue
        for col in itertools.product(range(d),repeat=4):
            row=tuple(col[p[k]] for k in range(4))
            r=list(row);s=list(col)
            # Partial transpose on the two input factors.
            for k in (0,2):r[k],s[k]=s[k],r[k]
            out[index(r,d)][index(s,d)]+=d*d*c
    j=zeros(d*d)
    for a,b in itertools.product(range(d),repeat=2):
        j[index((a,b),d)][index((a,b),d)]+=F(1,d+1)
    for a,b in itertools.product(range(d),repeat=2):
        j[index((a,a),d)][index((b,b),d)]+=F(1,d+1)
    for a,b,c,e in itertools.product(range(d*d),repeat=4):
        if j[a][b] and j[c][e]:out[a*d*d+c][b*d*d+e]-=j[a][b]*j[c][e]
    return out,coeff

def blocks(d):
    groups=defaultdict(list)
    for i,(a,b,c,e) in enumerate(itertools.product(range(d),repeat=4)):
        charge=[0]*d;charge[a]-=1;charge[b]+=1;charge[c]-=1;charge[e]+=1
        groups[tuple(charge)].append(i)
    return list(groups.values())

def positive_definite(x,groups):
    """Exact rational LDL: every positive diagonal pivot is a PSD certificate."""
    membership={i:k for k,g in enumerate(groups) for i in g}
    assert all(x[i][j]==x[j][i] for i in range(len(x)) for j in range(len(x)))
    assert all(not x[i][j] for i in range(len(x)) for j in range(len(x)) if membership[i]!=membership[j])
    mind=None
    for group in groups:
        n=len(group);l=zeros(n);diag=[]
        for i in range(n):
            l[i][i]=F(1)
            val=x[group[i]][group[i]]-sum((l[i][k]*l[i][k]*diag[k] for k in range(i)),F(0))
            assert val>0,('nonpositive exact LDL pivot',i,len(group),val)
            diag.append(val);mind=val if mind is None else min(mind,val)
            for j in range(i+1,n):
                l[j][i]=(x[group[j]][group[i]]-sum((l[j][k]*l[i][k]*diag[k] for k in range(i)),F(0)))/val
    return mind

def generate(path):
    import numpy as np
    d=4;data=np.load(HERE/'two_call_candidate_d4.npz');numeric=(data['Z']+data['Z'].T)/2
    z=[[F(int(round(float(numeric[i,j])*10**7)),10**7) for j in range(d**4)] for i in range(d**4)]
    g=ptr_last(z,d);y=[[v/d for v in row] for row in ptr_last(g,d)]
    corr=kron_identity(y,d);add_scaled(corr,g,F(-1));add_scaled(z,kron_identity(corr,d),F(1,d))
    t=ptr_last(y,d);lam=sum((t[i][i] for i in range(d)),F(0))/d
    corr=zeros(d)
    for i in range(d):
        for j in range(d):corr[i][j]=(lam if i==j else F(0))-t[i][j]
    yc=kron_identity(corr,d)
    yc=[[v/d for v in row] for row in yc]
    add_scaled(y,yc);add_scaled(z,kron_identity(kron_identity(yc,d),d),F(1,d))
    # Padding establishes lambda=4/25 exactly, with ample positive slack.
    c=(F(4,25)-lam)/(d*d)
    assert c>0
    for i in range(d**4):z[i][i]+=c
    den=1
    for row in z:
        for v in row:
            if v:den=math.lcm(den,v.denominator)
    entries=[[i,j,int(z[i][j]*den)] for i in range(d**4) for j in range(i,d**4) if z[i][j]]
    obj={'d':d,'lambda':'4/25','denominator':den,'symmetric_upper_entries':entries,
         'description':'Exact dual certificate. Ordinary balanced-prior success <= 29/50; switch control classifier succeeds with 13/20 using two calls.',
         'provenance':'A numerical candidate was rounded to 1e-7, exactly projected onto dual trace equalities, and padded. The verifier independently reconstructs the hypotheses and uses only rational arithmetic.'}
    path.write_text(json.dumps(obj,separators=(',',':'))+'\n')

def verify(path):
    start=time.time();obj=json.loads(path.read_text());d=obj['d'];lam=F(obj['lambda']);den=obj['denominator'];z=zeros(d**4)
    for i,j,v in obj['symmetric_upper_entries']:z[i][j]=z[j][i]=F(v,den)
    delta,coeff=moment_difference(d)
    for a,b,c,e in itertools.product(range(d),repeat=4):
        v=sum((delta[index((a,x,b,y),d)][index((c,x,e,y),d)]
               for x,y in itertools.product(range(d),repeat=2)),F(0))
        assert v==0, 'hypothesis difference must have zero output partial trace'
    visibility_gap=sum((delta[index((ell,k,i,ell),d)][index((i,j,j,k),d)]
                        for i,j,k,ell in itertools.product(range(d),repeat=4)),F(0))/d
    assert visibility_gap==F(d-1,d+1), 'independent switch-contraction check'
    g=ptr_last(z,d);y=[[v/d for v in row] for row in ptr_last(g,d)]
    assert g==kron_identity(y,d),'first causal dual trace equality'
    tr=ptr_last(y,d)
    assert all(tr[i][j]==(lam if i==j else F(0)) for i in range(d) for j in range(d)),'second causal dual trace equality'
    groups=blocks(d);p0=positive_definite(z,groups)
    zd=[row.copy() for row in z];add_scaled(zd,delta,F(-1));p1=positive_definite(zd,groups)
    sw=F(1,2)+F(d-1,4*(d+1));ordinary=(1+lam)/2
    assert sw>ordinary
    report={'status':'PASS: exact rational arithmetic', 'd':d,'ordinary_success_upper':str(ordinary),
            'switch_success':str(sw),'certified_success_gap':str(sw-ordinary),
            'dual_lambda':str(lam),'exact_visibility_gap':str(visibility_gap),'number_of_PSD_blocks':len(groups),'largest_PSD_block':max(map(len,groups)),
            'minimum_LDL_pivot_Z':str(p0),'minimum_LDL_pivot_Z_minus_Delta':str(p1),
            'certificate_upper_nonzero_entries':len(obj['symmetric_upper_entries']),
            'certificate_denominator':den,'elapsed_seconds':round(time.time()-start,3),
            'scope':'Two uses of one fixed, unknown memoryless channel; balanced prior between Haar-hidden rank-one dephasing and Lambda=(id+d Omega)/(d+1). All ordinary adaptive quantum testers with arbitrary ancillas are bounded. This certificate does not bound arbitrarily many uses or establish native hardware advantage.'}
    (HERE/'two_call_exact_verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--generate',action='store_true');p.add_argument('--certificate',type=Path,default=HERE/'two_call_exact_certificate.json');args=p.parse_args()
    if args.generate:generate(args.certificate)
    verify(args.certificate)
