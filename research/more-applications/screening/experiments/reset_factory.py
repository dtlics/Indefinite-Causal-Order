"""Two ordinary reset channels inside a switch: explicit magic-source model.
Resource comparator: stabilizer operations plus the same reset instruments.
This is NOT an unrestricted ordinary-quantum lower bound.
"""
from core import *
from pathlib import Path
import json,mpmath as mp,sympy as sp
ROOT=Path(__file__).resolve().parent
mp.mp.dps=70
plus=np.array([1,1],complex)/np.sqrt(2);rho=np.outer(plus,plus.conj())

def branch(a,b,k):
    den=4+k*(1+b)
    p=den/8
    x=(2*b+k*(1+b))/den
    z=a*(2+k*(1+b))/den
    m=(x+z)/2
    err=(1-np.sqrt(2)*m)/2
    return dict(a=a,b=b,kappa=k,p_plus=p,x=x,z=z,magic_l1=x+z,twirled_H_coordinate=m,magic_state_error=err)
# Independent Kraus verification of noisy-control formula.
rng=np.random.default_rng(12058);maxerr=0
for _ in range(100):
    a,b,k=rng.random(3)
    A=reset((I2+a*Z)/2);B=reset((I2+b*X)/2)
    kp,km=switch_branches(A,B)
    R=(1+k)/2*apply(kp,rho)+(1-k)/2*apply(km,rho)
    f=branch(a,b,k);m=f['p_plus']*(I2+f['x']*X+f['z']*Z)/2
    maxerr=max(maxerr,np.linalg.norm(R-m))

# Standard 15-to-1 error/acceptance recursion, ideal stabilizer operations.
def distill(e):
    r=1-2*e
    acc=(1+15*r**8)/16
    new=(1-15*r**7+15*r**8-r**15)/(2*(1+15*r**8))
    return new,acc
rows=[]
for a,b,k in [(1,1,1),(.9,.9,.98),(.8,.8,.9),(.75,.75,1)]:
    f=branch(a,b,k)
    ee=mp.mpf(str(f['magic_state_error']));cost=mp.mpf(2)/mp.mpf(str(f['p_plus']))
    stages=[dict(level=0,error=float(ee),expected_reset_calls=float(cost))]
    for level in range(1,5):
        ee,acc=distill(ee);cost*=15/acc
        stages.append(dict(level=level,error=float(ee),batch_acceptance=float(acc),expected_reset_calls=float(cost)))
    rows.append({'source':f,'distillation':stages})

# Records from projective reset implementations, if physically accessible.
z0=np.array([1,0],complex);z1=np.array([0,1],complex);minus=np.array([1,-1],complex)/np.sqrt(2)
As=[np.outer(z0,z0),np.outer(z0,z1)]
Bs=[np.outer(plus,plus),np.outer(plus,minus)]
record=[]
for i,A in enumerate(As):
 for j,B in enumerate(Bs):
  for s in [1,-1]:
   v=(B@A+s*A@B)@plus/2;p=float(np.vdot(v,v).real)
   if p<1e-14:continue
   rr=np.outer(v,v.conj())/p
   bloch=[float(np.trace(rr@P).real) for P in [X,Y,Z]]
   record.append({'i':i,'j':j,'sign':s,'p':p,'bloch':bloch,'magic':sum(abs(t) for t in bloch)>1+1e-8})
# General arbitrary reset Bloch vectors symbolic result via gamma=tauB rho tauA.
a,b,k=sp.symbols('a b k',real=True)
I=sp.eye(2);XX=sp.Matrix([[0,1],[1,0]]);ZZ=sp.diag(1,-1)
TA=(I+a*ZZ)/2;TB=(I+b*XX)/2;RHO=(I+XX)/2
M=(TA+TB+k*(TB*RHO*TA+TA*RHO*TB))/4
assert sp.simplify(M-((4+k*(1+b))*I+(2*b+k*(1+b))*XX+a*(2+k*(1+b))*ZZ)/16)==sp.zeros(2)
res={'verification_trials':100,'max_formula_residual':float(maxerr),'symbolic_formula':True,'source_cases':rows,'ideal_visible_record_branches':record,'resource_scope':'Strict improvement against any stabilizer-only protocol with the same reset channels and no magic input. A generic known-dilation compiler uses non-Clifford control and must be priced. Not a black-box query separation against arbitrary ordinary processing.'}
ROOT.joinpath('reset_factory.json').write_text(json.dumps(res,indent=2))
print(json.dumps(res,indent=2))
