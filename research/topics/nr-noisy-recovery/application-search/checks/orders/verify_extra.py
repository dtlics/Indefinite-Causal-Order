import sys,itertools,json
from fractions import Fraction as F
from pathlib import Path
import numpy as np
import sympy as sp
from explore_orders import matrices
from modular_protocol import accepted

def direct(m,d,coeff):
    ps=list(coeff);z=list(coeff.values());K=[]
    for a,b in itertools.product(range(d),repeat=2):
        M=np.zeros((d,d),complex);M[a,b]=1/np.sqrt(d);K.append(M)
    J=np.zeros((d*d,d*d),complex)
    maxres=0
    for ks in itertools.product(K,repeat=m):
        L=np.zeros((d,d),complex)
        for p,c in zip(ps,z):
            M=np.eye(d,dtype=complex)
            for k in p:M=ks[k]@M
            L+=c*M
        vec=L.reshape(-1,order='F');J+=np.outer(vec,vec.conj())/d
    perms,A,B,*_=matrices(m,d);v=np.zeros(len(perms),complex)
    for p,c in coeff.items():v[perms.index(p)]=c
    a=(v.conj()@A@v).real;b=(v.conj()@B@v).real
    phi=np.eye(d).reshape(-1,order='F')/np.sqrt(d)
    pred=a*np.outer(phi,phi)+b*np.eye(d*d)/d**2
    return float(np.max(abs(J-pred)))

rng=np.random.default_rng(20261110);out={}
for m,d in [(2,3),(3,3),(4,2),(4,3)]:
    ps=list(itertools.permutations(range(m)))
    v=rng.normal(size=len(ps))+1j*rng.normal(size=len(ps));v/=np.sum(abs(v))
    err=direct(m,d,dict(zip(ps,v)));out[f'direct_m{m}_d{d}']=err;assert err<1e-12
# Exact symbolic flag identity and closure bounds
D=sp.symbols('D',positive=True)
L=-1/D;H=(D+2)/(D*(D-4));f=lambda x,y:(x*y+1/(2*D))/(x+y+sp.Rational(1,2))
assert sp.simplify(f(L,L)-H)==0
assert sp.simplify((H+1/D)/(H+1)-2/(D-2))==0
for name,expr in [('cornerHH',H-f(H,H)),('cornerHL',H-f(H,L))]:
    out[name]=str(sp.factor(expr))
# Algebraic containment check for all rational depolarizing EB endpoints in d=3..32
for d in range(3,33):
    l=-F(1,d*d); t=F(1,d);h=F(d*d+2,d*d*(d*d-4))
    for a,b in itertools.product([l,t],repeat=2):
        den=a+b+F(1,2);r=(a*b+F(1,2*d*d))/den
        assert den>0 and l<=r<=t
    for a,b in itertools.product([l,h],repeat=2):
        r=(a*b+F(1,2*d*d))/(a+b+F(1,2));assert l<=r<=h
# Example controller readout polynomial
eta=sp.symbols('eta',real=True)
AA=[sp.Rational(x,64) for x in [3,-2,1,-2,1,-2,3,-2]]
BB=[sp.Rational(x,64) for x in [16,8,8,8,8,8,0,8]]
a=b=0
for j in range(8):
    k=(j^6).bit_count();w=eta**k*(1-eta)**(3-k);a+=w*AA[j];b+=w*BB[j]
out['accepted_probability']=str(sp.factor(a+b))
out['accepted_infidelity']=str(sp.factor(1-(a+b/4)/(a+b)))
Path(__file__).with_name('extra_checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
