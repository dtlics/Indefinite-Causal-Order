"""Exact guards for the isolated-blue-band moving-CAPS factory comparison.

The method note owns the analytic parity, sideband and ordinary-routing
assumptions.  Gaussian-rational atomic Kraus fixtures below retain all
three final-motion records.  Polynomial identities and rational source
constants guard the analytic bucket-readout rate comparison.  No finite
fixture certifies oscillator tails, a physical analyzer or a router cost.
"""
from fractions import Fraction as F
import json


def require(test,label):
    if not test:raise RuntimeError(label)


class G:
    """Gaussian rationals, with no floating-point arithmetic."""
    def __init__(self,real=0,imag=0):
        if isinstance(real,G):self.real,self.imag=real.real,real.imag
        else:self.real,self.imag=F(real),F(imag)
    def __add__(self,other):
        other=G(other)
        return G(self.real+other.real,self.imag+other.imag)
    __radd__=__add__
    def __neg__(self):return G(-self.real,-self.imag)
    def __sub__(self,other):return self+-G(other)
    def __mul__(self,other):
        other=G(other)
        return G(self.real*other.real-self.imag*other.imag,
                 self.real*other.imag+self.imag*other.real)
    __rmul__=__mul__
    def __truediv__(self,other):
        other=G(other);den=other.norm2()
        require(den>0,'nonzero Gaussian denominator')
        return self*G(other.real/den,-other.imag/den)
    def __eq__(self,other):
        other=G(other)
        return self.real==other.real and self.imag==other.imag
    def norm2(self):return self.real*self.real+self.imag*self.imag


def atomic_kraus(epsilon,t,d,s):
    """Diagonal spin Kraus entries, ordered 00,01,10,11.

    Native: d=Delta r0, s=Delta s22.  Ordinary one-contact erasure:
    d=s=1.  Source motion is (|0>+epsilon|2>) at each node, normalized.
    The factor1/2 includes balanced path preparation and minus readout.
    """
    epsilon=F(epsilon);z=epsilon*epsilon
    u=epsilon*G(t)*G(d)/(2*(1+z))
    v=epsilon*G(t)*G(s)/(2*(1+z))
    return {'00':[G(0),-u,u,G(0)],
            '02':[G(0),G(0),epsilon*u,epsilon*v],
            '20':[G(0),-epsilon*u,G(0),-epsilon*v]}


def atomic_score(records):
    """Launch probability and singlet overlap after input spin |++>."""
    require(set(records)=={'00','02','20'},'all three final-motion records')
    require(all(len(k)==4 for k in records.values()),'two-qubit spin dimension')
    p=sum((sum((entry.norm2() for entry in k),F(0))/4
           for k in records.values()),F(0))
    g=sum(((k[2]-k[1]).norm2()/8 for k in records.values()),F(0))
    return p,g


def native_score(z,idark,i22):
    return (idark*z*(1+(1+i22/idark)*z)/(8*(1+z)**2),
            idark*z*(1+z/2)/(8*(1+z)**2))


def ordinary_score(z,i0):
    return (i0*z*(1+2*z)/(8*(1+z)**2),
            i0*z*(1+z/2)/(8*(1+z)**2))


def match_preparation(z,rho):
    z,rho=F(z),F(rho)
    require(z>0,'positive native excitation parameter')
    require(rho>=0,'nonnegative contamination ratio')
    require(rho*z<1,'native singlet fidelity greater than one half')
    denominator=3+(1-rho)*z
    require(denominator>0,'positive matched-preparation denominator')
    ordinary_z=(1+2*rho)*z/denominator
    require(0<ordinary_z<1,'finite feasible ordinary preparation')
    return ordinary_z


def frontier(i0,idark,i22,z):
    i0,idark,i22,z=map(F,(i0,idark,i22,z))
    require(i0>0 and idark>0,'nonzero ordinary and native useful moments')
    require(i22>=0,'nonnegative bright contamination moment')
    rho=i22/idark;q=idark/i0
    ordinary_z=match_preparation(z,rho)
    pn,gn=native_score(z,idark,i22)
    po,go=ordinary_score(ordinary_z,i0)
    require(gn/pn>F(1,2),'useful native singlet threshold')
    require(go/po==gn/pn,'ordinary preparation matches singlet fidelity')
    ratio=3*(1+2*rho)*(1+z)**2/(q*(3+(2+rho)*z)**2)
    require(po/pn==go/gn==ratio,'exact launch-yield and good-mass ratio')
    require(ratio>=1/(3*q),'ordinary bucket frontier bound')
    return ordinary_z,ratio


# Exact polynomials in three formal variables; no sampled positivity test.
def clean(p):return {key:value for key,value in p.items() if value}
def constant(value):return {(0,0,0):F(value)} if value else {}
def add(a,b):
    out=dict(a)
    for key,value in b.items():out[key]=out.get(key,F(0))+value
    return clean(out)
def scale(a,value):return clean({key:coefficient*value for key,coefficient in a.items()})
def multiply(a,b):
    out={}
    for ka,va in a.items():
        for kb,vb in b.items():
            key=tuple(x+y for x,y in zip(ka,kb))
            out[key]=out.get(key,F(0))+va*vb
    return clean(out)
def square(a):return multiply(a,a)


def polynomial_guards():
    one=constant(1);r={(1,0,0):F(1)};z={(0,1,0):F(1)};x={(0,0,1):F(1)}
    rz=multiply(r,z)
    numerator=add(z,scale(rz,2))
    denominator=add(add(constant(3),z),scale(rz,-1))
    combined=add(constant(3),multiply(add(constant(2),r),z))
    require(add(denominator,numerator)==combined,'matched source normalization polynomial')
    require(add(scale(denominator,2),numerator)==scale(add(constant(2),z),3),
            'matched good-mass ratio cancellation polynomial')
    left=multiply(add(scale(denominator,2),numerator),
                  add(one,multiply(add(one,r),z)))
    right=multiply(add(constant(2),z),add(denominator,scale(numerator,2)))
    require(left==right,'singlet-fidelity matching polynomial')
    gap=add(scale(multiply(add(one,scale(r,2)),square(add(one,z))),9),
            scale(square(combined),-1))
    # For r>=0,z>0,r*z<1 every displayed term is nonnegative.
    certificate=add(add(add(scale(r,18),scale(z,6)),scale(rz,29)),
                    add(add(scale(square(z),5),scale(multiply(r,square(z)),14)),
                        multiply(rz,add(one,scale(rz,-1)))))
    require(gap==certificate,'global frontier positivity identity')
    # Here r denotes kappa^2, z denotes delta/2, x denotes w+delta/2.
    product=multiply(add(r,square(add(x,scale(z,-1)))),add(r,square(add(x,z))))
    expanded=add(add(square(add(r,square(z))),
                     scale(multiply(square(x),add(r,scale(square(z),-1))),2)),
                 square(square(x)))
    require(product==expanded,'empty-cavity denominator global minimum identity')
    return 5


def empty_cavity_constants():
    kin=F(1,5);g=F(38,5);gamma=F(3);mu=F(69,500)
    kex_squared=kin*kin+kin*g*g/gamma
    require(kex_squared==F(1459,375),'source output-coupling square')
    kex_lower=F(493,250)
    require(kex_squared>kex_lower*kex_lower,'strict rational output-coupling lower bound')
    kappa_lower=kin+kex_lower;delta=2*mu
    require(kappa_lower==F(543,250) and kappa_lower>delta/2,
            'empty-cavity denominator minimum regime')
    q_upper=4*kex_squared*delta*delta/(kappa_lower*kappa_lower+delta*delta/4)**2
    require(q_upper<F(53,1000)<F(1,18),'global bucket amplitude-square bound below one eighteenth')
    require(1/(3*q_upper)>6,'ordinary rate multiplier exceeds six')
    return q_upper


def reject(fn,label):
    try:fn()
    except RuntimeError:return label
    raise RuntimeError('invalid fixture survived: '+label)


def verify():
    # Literal atomic Kraus records first, including complex amplitudes and
    # both O(epsilon^4) noise records.  The formulas are then checked globally
    # by polynomial identities plus the explicitly stated positivity domain.
    atomic_fixtures=0
    for epsilon in (F(1,10),F(1,2),F(1),F(2)):
        for t,d,s in ((G(F(1,3),F(1,5)),G(F(1,10),F(-1,7)),G(0)),
                      (G(F(2,5),F(-1,9)),G(F(1,4),F(1,5)),G(F(1,10),F(-1,8)))):
            z=epsilon*epsilon
            native=atomic_score(atomic_kraus(epsilon,t,d,s))
            require(native==native_score(z,(t*d).norm2(),(t*s).norm2()),'complete native atomic-record score')
            ordinary=atomic_score(atomic_kraus(epsilon,t,1,1))
            require(ordinary==ordinary_score(z,t.norm2()),'complete ordinary atomic-record score')
            atomic_fixtures+=1
    # Id=0 cannot provide positive singlet overlap, including a nonzero
    # contamination-only accepted event.  Zero launch amplitude has p=g=0.
    require(atomic_score(atomic_kraus(F(1,2),G(1),G(0),G(1)))[1]==0,
            'zero useful native amplitude has zero singlet weight')
    require(atomic_score(atomic_kraus(F(0),G(1),G(1),G(1)))==(0,0),
            'zero coherent excitation gives no blue event')
    identities=polynomial_guards();q_upper=empty_cavity_constants()
    frontier_fixtures=[]
    for rho in (F(0),F(1,100),F(1),F(2),F(100)):
        for z in (F(1,1000),F(1,100),F(1,2),F(2),F(100)):
            if rho*z>=1:continue
            ordinary_z,ratio=frontier(1,q_upper,rho*q_upper,z)
            require(ratio>6,'source-qualified ordinary rate advantage')
            frontier_fixtures.append({'native_z':str(z),'rho':str(rho),
                                      'ordinary_z':str(ordinary_z),'yield_ratio':str(ratio)})
    incomplete=atomic_kraus(F(1,2),G(1),G(1),G(1));incomplete.pop('02')
    invalid=[reject(lambda:atomic_score(incomplete),'missing motion record'),
             reject(lambda:match_preparation(0,0),'zero native z'),
             reject(lambda:match_preparation(1,-1),'negative rho'),
             reject(lambda:match_preparation(1,1),'singlet threshold equality'),
             reject(lambda:frontier(0,1,0,1),'zero ordinary useful moment'),
             reject(lambda:frontier(1,0,1,1),'zero native useful moment')]
    return {'status':'passed','atomic_Gaussian_rational_fixtures':atomic_fixtures,
            'complete_final_motion_records':['00','02','20'],
            'exact_polynomial_identities':identities,'q_strict_upper':str(q_upper),
            'uniform_yield_multiplier_strict_lower':str(1/(3*q_upper)),
            'frontier_fixtures':frontier_fixtures,'invalid_fixtures_rejected':invalid,
            'scope':'Isolated blue-band standing-wave Bell-state factory; frequency-diagonal photon readout, tunable supplied product-motion preparation and coherent one-contact A/B bypass. Analytic assumptions own the global claim; no all-readout, all-router, packet-tail, full-loss-channel or physical-rate certificate.'}


if __name__=='__main__':print(json.dumps(verify(),sort_keys=True))
