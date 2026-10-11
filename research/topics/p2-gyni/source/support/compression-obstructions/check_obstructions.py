#!/usr/bin/env python3
"""Exact rational checks for finite-span compression obstructions."""
import itertools,json
from fractions import Fraction as F
from pathlib import Path
import numpy as np

def det(a):
    a=[[F(z) for z in row] for row in a];n=len(a);out=F(1)
    for k in range(n):
        p=next((j for j in range(k,n) if a[j][k]),None)
        if p is None:return F(0)
        if p!=k:a[k],a[p]=a[p],a[k];out=-out
        v=a[k][k];out*=v
        for i in range(k+1,n):
            t=a[i][k]/v
            for j in range(k+1,n):a[i][j]-=t*a[k][j]
    return out

def angle(t):return((1-t*t)/(1+t*t),2*t/(1+t*t))
Z=np.array([[F(1),F(0)],[F(0),F(-1)]],dtype=object)
X=np.array([[F(0),F(1)],[F(1),F(0)]],dtype=object)
Om=np.array([F(1),F(0),F(0),F(1)],dtype=object)
rows=[];pencils=0;minors=0;central=0;units=0
for K in range(2,11):
    pairs=[angle(F(j,K+1)) for j in range(1,K+1)]
    RR=[c*Z+s*X for c,s in pairs]
    for j,(c,s) in enumerate(pairs):
        gap=1-max(c*cc+s*ss for i,(cc,ss) in enumerate(pairs) if i!=j)
        assert gap>0;threshold=2-gap/2
        # Central anticommutator and noncommutativity establish distinct M2 fibers.
        assert np.array_equal((Z@RR[j]+RR[j]@Z)/2,c*np.eye(2,dtype=object));central+=1
        for k,(cc,ss) in enumerate(pairs):
            L=np.kron(Z,Z)+np.kron(RR[j],RR[k]);P=threshold*np.eye(4,dtype=object)-L
            if k==j:
                assert Om@P@Om==-gap
                assert np.array_equal(L@Om,2*Om)
            else:
                assert threshold*threshold>2+2*(c*cc+s*ss)
                for n in range(1,5):assert det(P[:n,:n])>0;minors+=1
            pencils+=1
        rows.append({'K':K,'target':j,'gap':str(gap),'threshold':str(threshold)})
    # Keep both output-setting flags; normalization projectors repeat in both.
    n=8*K;vecs=[];Ds=[]
    for j in range(K):
        e=np.zeros(n,dtype=np.int64);e[4*j]=1;vecs.append(e)
        D=np.zeros((n,n),dtype=np.int64)
        for x in range(2):
            for t in range(4):D[x*4*K+4*j+t,x*4*K+4*j+t]=1
        Ds.append(D)
    p=sum(vecs);Q=np.outer(p,p);E={}
    for j in range(K):
        for k in range(K):
            E[j,k]=Ds[j]@Q@Ds[k]
            assert np.array_equal(E[j,k],np.outer(vecs[j],vecs[k]));units+=1
    # Verify all adjacent matrix-unit products via exact integer contractions.
    for j in range(K):
        for k in range(K):
            assert np.array_equal(E[j,k].T,E[k,j]);units+=1
            for ell in range(K):
                # Multiplication by rank-one unit E_(ell,0) without large dense work.
                product=np.outer(E[j,k]@vecs[ell],vecs[0])
                target=E[j,0] if k==ell else np.zeros((n,n),dtype=np.int64)
                assert np.array_equal(product,target);units+=1
out={'status':'PASSED_EXACT','angles':'rational c=(1-t^2)/(1+t^2), s=2t/(1+t^2), t=j/(K+1)','K_values':list(range(2,11)),'separating_pencils':pencils,'strict_positive_leading_principal_minors':minors,'central_identities':central,'matrix_unit_checks':units,'solver_used':False,'floating_arithmetic_used':False,'scope':'Checks explicit algebraic obstruction formulas; does not establish a GYNI dimension cutoff or nonattainment.','cases':rows}
Path(__file__).with_name('obstruction_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='cases'},indent=2))
