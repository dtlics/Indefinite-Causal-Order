"""Finite exact guards for the C5/C6 theoretical application corollaries.

Standard library only; weighted Kraus families use Gaussian rationals and
avoid square roots. Complete finite matrix identities are checked at d=2,4.
The all-dimension diamond bounds, query lower bounds, Haar/process freshness
and statistical independence premises remain analytic dependencies.
"""
from fractions import Fraction as F
from pathlib import Path
import contextlib
import hashlib
import importlib.util
import io
import json

HERE=Path(__file__).resolve().parent
HELPER_CANDIDATES=(
    HERE/'verify_unital_entropy.py',
    HERE.parent/'repo-update/research/topics/nr-noisy-recovery/checks/architecture/verify_unital_entropy.py',
)
HELPER=next((p for p in HELPER_CANDIDATES if p.is_file()),None)
if HELPER is None:
    raise RuntimeError('Cannot locate the stdlib Gaussian-rational helper')
spec=importlib.util.spec_from_file_location('theory_gaussian_rationals',HELPER)
helper=importlib.util.module_from_spec(spec)
capture=io.StringIO()
with contextlib.redirect_stdout(capture):
    spec.loader.exec_module(helper)
if capture.getvalue():
    raise RuntimeError('Helper executed or printed on import')

C,zero,eye,adj,add,scale,mul,trace,choi,effects=(
    helper.C,helper.zero,helper.eye,helper.adj,helper.add,helper.scale,
    helper.mul,helper.trace,helper.choi,helper.effects)

def require(condition,label):
    if not condition:raise RuntimeError(label)

def matrix_unit(d,a,b):
    out=zero(d);out[a][b]=C(1);return out

def apply(family,x):
    out=zero(len(x))
    for w,k in family:out=add(out,scale(mul(mul(k,x),adj(k)),w))
    return out

def supermatrix(family):
    d=len(family[0][1]);out=zero(d*d)
    for a in range(d):
        for b in range(d):
            y=apply(family,matrix_unit(d,a,b))
            for c in range(d):
                for e in range(d):out[c*d+e][a*d+b]=y[c][e]
    return out

def omega_family(d):
    return [(F(1,d),matrix_unit(d,a,b)) for a in range(d) for b in range(d)]

def mix(a,b,t):
    require(0<=t<=1,'convex channel mixture parameter')
    return [(w*(1-t),k) for w,k in a]+[(w*t,k) for w,k in b]


def check_channel(family,label):
    require(all(w>=0 for w,k in family),label+' nonnegative Kraus weights')
    d=len(family[0][1])
    tp,unital=effects(family)
    require(tp==eye(d) and unital==eye(d),label+' trace preserving and unital')

def visibility(a,b):
    d=len(a[0][1]);answer=C()
    for w,k in a:
        for v,l in b:
            # Real trace is unchanged by reversing the switch control labels.
            answer+=(w*v/d)*trace(mul(mul(mul(adj(l),adj(k)),l),k))
    require(answer.i==0,'visibility imaginary cancellation')
    return answer.r

def minus(a,b):
    d=len(a[0][1]);answer=F()
    for w,k in a:
        for v,l in b:
            answer+=w*v*helper.frob2(helper.comm(k,l))/(4*d)
    return answer

def tensor(a,b):
    m,n=len(a),len(b)
    return [[a[i//n][j//n]*b[i%n][j%n] for j in range(m*n)] for i in range(m*n)]

def conjugate_projectors(projectors,u):
    return [mul(mul(u,p),adj(u)) for p in projectors]

def projector_family(projectors):return [(F(1),p) for p in projectors]

def check_projector(p,rank,label):
    require(adj(p)==p and mul(p,p)==p,label+' projection')
    require(trace(p)==rank,label+' rank by exact projection trace')

def check_resolution(projectors,d,label):
    total=zero(d)
    for i,p in enumerate(projectors):
        check_projector(p,1,label+' rank-one')
        total=add(total,p)
        for j,q in enumerate(projectors):
            require(mul(p,q)==(p if i==j else zero(d)),label+' orthogonality')
    require(total==eye(d),label+' complete resolution')

def flat_projectors(d):
    p=[matrix_unit(d,j,j) for j in range(d)]
    q=[]
    for j in range(d):
        signs=[-1 if (a&j).bit_count()%2 else 1 for a in range(d)]
        q.append([[C(F(signs[a]*signs[b],d)) for b in range(d)] for a in range(d)])
    return p,q

def rational_unitary(d):
    u=[[C(F(3,5)),C(0,F(4,5))],[C(0,F(4,5)),C(F(3,5))]]
    return u if d==2 else tensor(u,u)

def complete_mub_projectors(d):
    """Finite stabilizer 2-design guard, not a proof of a Haar integral."""
    i,x,y,z=eye(2),[[C(),C(1)],[C(1),C()]],[[C(),C(0,-1)],[C(0,1),C()]],[[C(1),C()],[C(),C(-1)]]
    if d==2:
        return [[scale(add(i,g,s),F(1,2)) for s in (-1,1)] for g in (x,y,z)]
    generators=((tensor(z,i),tensor(i,z)),(tensor(x,i),tensor(i,x)),
                (tensor(y,i),tensor(i,y)),(tensor(x,y),tensor(y,z)),
                (tensor(x,z),tensor(y,x)))
    return [[scale(mul(add(eye(4),a,s),add(eye(4),b,t)),F(1,4))
             for s in (-1,1) for t in (-1,1)] for a,b in generators]

def case(d,conjugated):
    p,q=flat_projectors(d)
    if conjugated:
        u=rational_unitary(d)
        require(mul(adj(u),u)==eye(d),'rational complex unitary')
        p,q=conjugate_projectors(p,u),conjugate_projectors(q,u)
    check_resolution(p,d,'P');check_resolution(q,d,'Q')
    for pi in p:
        for qi in q:
            require(trace(mul(pi,qi))==F(1,d),'flat overlap')
            require(mul(mul(pi,qi),pi)==scale(pi,F(1,d)),'flat pinching overlap')
    a,b=projector_family(p),projector_family(q)
    om=omega_family(d);ident=[(F(1),eye(d))]
    for label,family in (('A',a),('B',b),('Omega',om),('identity',ident)):
        check_channel(family,label)
    sa,sb,so=supermatrix(a),supermatrix(b),supermatrix(om)
    require(mul(sa,sa)==sa and mul(sb,sb)==sb,'A/B idempotence')
    require(mul(sa,sb)==so and mul(sb,sa)==so,'AB=BA=Omega on all matrix units')
    require(mul(so,so)==so,'Omega idempotence')
    a0,b0=add(sa,so,-1),add(sb,so,-1)
    check_projector(so,1,'Omega superoperator')
    check_projector(a0,d-1,'A-Omega superoperator')
    check_projector(b0,d-1,'B-Omega superoperator')
    require(mul(a0,b0)==zero(d*d) and mul(b0,a0)==zero(d*d),'traceless orthogonal ranges')
    rest=add(add(add(eye(d*d),so,-1),a0,-1),b0,-1)
    check_projector(rest,(d-1)**2,'Phi zero eigenspace')
    phi=mix(a,b,F(1,2));sphi=supermatrix(phi)
    check_channel(phi,'Phi')
    require(sphi==add(so,scale(add(a0,b0),F(1,2))),'Phi spectral resolution')
    power=eye(d*d)
    for k in range(1,6):
        power=mul(power,sphi)
        require(power==add(so,scale(add(a0,b0),F(1,2**k))),'Phi exact power')
        require(mul(sa,sa)==sa,'SAME Phi power remains pinching')
    ja,jb,jid=choi(a),choi(b),choi(ident)
    ra,rb=scale(ja,d),scale(jb,d)
    check_projector(ra,d,'pinching Choi support A')
    check_projector(rb,d,'pinching Choi support B')
    check_projector(jid,1,'normalized maximally entangled Choi')
    require(mul(ra,rb)==jid and mul(rb,ra)==jid,'Choi supports intersect only at identity')
    ta,tb=add(ra,jid,-1),add(rb,jid,-1)
    check_projector(ta,d-1,'traceless Choi support A')
    check_projector(tb,d-1,'traceless Choi support B')
    require(mul(ta,tb)==zero(d*d),'traceless Choi supports orthogonal')
    require(choi(phi)==add(scale(jid,F(1,d)),scale(add(ta,tb),F(1,2*d))),
            'Phi Choi multiplicities d^-1 once and (2d)^-1 repeated2d-2')
    require(visibility(a,a)==1 and minus(a,a)==0,'SAME self-Phi flag')
    require(visibility(a,b)==F(1,d),'cross MUB visibility')
    require(visibility(phi,phi)==F(d+1,2*d),'MUB self-Phi visibility')
    require(minus(phi,phi)==F(d-1,4*d),'MUB self-Phi minus probability')
    # The known input P0 witnesses the pinching/replacement distance. This is
    # not a finite enumeration of the all-reference diamond-norm upper bound.
    output_difference=add(apply(a,p[0]),apply(om,p[0]),-1)
    require(output_difference==add(scale(p[0],1-F(1,d)),scale(add(eye(d),p[0],-1),-F(1,d))),
            'pinching distance lower witness spectral resolution')
    trace_norm=(1-F(1,d))+F(d-1,d)
    require(trace_norm/2==1-F(1,d),'pinching distance witness value')
    # Complete normalized Choi projectors guard the entropy-family spectra.
    for t in (F(0),F(1,7),F(1,2),F(1)):
        high,low=mix(ident,a,t),mix(ident,om,t)
        check_channel(high,'high production');check_channel(low,'low production')
        require(choi(high)==add(scale(jid,1-t+t/d),scale(ta,t/d)),
                'high production Choi spectrum')
        require(choi(low)==add(scale(jid,1-t+t/(d*d)),
                scale(add(eye(d*d),jid,-1),t/(d*d))),'low production Choi spectrum')
        require(visibility(high,high)==1,'high production self visibility')
        require(visibility(low,low)==1-t*t+t*t/(d*d),'low production self visibility')
    return {'d':d,'common_rational_complex_conjugation':conjugated,
            'operator_spectrum_multiplicities':[1,2*d-2,(d-1)**2],
            'self_Phi_visibility':str(F(d+1,2*d)),
            'self_Phi_minus':str(F(d-1,4*d)),
            'pinching_distance_input_witness':str(1-F(1,d)),
            'full_matrix_unit_and_Choi_guards':True}

def freshness_case(d):
    om=omega_family(d);ident=[(F(1),eye(d))]
    lam=mix(ident,om,F(d,d+1));sl=supermatrix(lam)
    check_channel(lam,'Lambda')
    require(sl==scale(add(supermatrix(ident),scale(supermatrix(om),d)),F(1,d+1)),
            'Lambda formula on all matrix units')
    bases=complete_mub_projectors(d)
    require(len(bases)==d+1,'finite complete MUB count')
    for basis in bases:check_resolution(basis,d,'finite MUB basis')
    for i,left in enumerate(bases):
        for j,right in enumerate(bases):
            if i==j:continue
            for p in left:
                for q in right:require(trace(mul(p,q))==F(1,d),'finite complete MUB overlap')
    twirl=[(F(1,d+1),p) for basis in bases for p in basis]
    check_channel(twirl,'finite MUB twirl')
    require(supermatrix(twirl)==sl,'finite MUB averaged pinching equals Lambda')
    require(visibility(lam,lam)==F(2,d+1),'Lambda self visibility')
    require(minus(lam,lam)==F(d-1,2*(d+1)),'rapid pure-dephasing minus')
    weak=[]
    for t in (F(0),F(1,7),F(1,2),F(1)):
        rapid=mix(ident,lam,t)
        check_channel(rapid,'weak rapid')
        expected=t*t*F(d-1,2*(d+1))
        require(minus(rapid,rapid)==expected,'weak rapid minus')
        require(visibility(rapid,rapid)==1-2*expected,'weak rapid visibility/minus relation')
        static_values=[]
        for basis in bases:
            static=mix(ident,projector_family(basis),t)
            require(minus(static,static)==0 and visibility(static,static)==1,
                    'weak quasistatic shared-basis minus is zero')
            static_values.append(F(0))
        require(sum(static_values,F())/(d+1)==0,'averaged quasistatic flag remains zero')
        weak.append({'t':str(t),'rapid_minus':str(expected),'quasistatic_minus':'0'})
    return {'d':d,'Lambda_visibility':str(F(2,d+1)),
            'finite_MUB_average_bases':len(bases),'weak_cases':weak,
            'scope':'Finite MUB average guards the algebra; it does not prove the Haar average or the physical joint freshness/coherent-label interface.'}

def constants():
    seven=F(5,6)**7;nine=F(7,8)**9;four=F(3,4)**4
    require(seven==F(78125,279936) and seven<F(1,3),'seven rapid-fluctuation trials')
    require(nine==F(40353607,134217728) and nine<F(1,3),'nine self-Phi trials')
    require(F(7,8)**7>F(1,3),'seven trials do not suffice for worst-case self-Phi miss rule')
    require(four==F(81,256) and four<F(1,3),'four cross-C6 trials')
    distance=F(509,10000)+F(1,100)
    require(distance==F(609,10000) and distance<F(1,3),'C5 plus rapid/Omega hybrid constant')
    helstrom=(1+distance)/2
    require(helstrom==F(10609,20000) and helstrom<F(2,3),'balanced Helstrom threshold')
    return {'seven_rapid_miss_bound':str(seven),'nine_self_Phi_miss_bound':str(nine),
            'four_cross_C6_miss_bound':str(four),'seven_self_Phi_not_enough':True,
            'noise_model_half_trace_bound':str(distance),'balanced_Helstrom_success_bound':str(helstrom),
            'scope':'Only exact rational combinations and trial inequalities. The B(q,d) analytic estimate, hybrid diamond norm and independence premises are not inferred from these arithmetic checks.'}

def verify():
    return {'status':'passed','arithmetic':'stdlib Fraction Gaussian rationals; no floating point',
            'helper_import_printed_nothing':True,'helper':str(HELPER),
            'helper_sha256':hashlib.sha256(HELPER.read_bytes()).hexdigest(),
            'geometry_cases':[case(d,c) for d in (2,4) for c in (False,True)],
            'freshness_algebra_cases':[freshness_case(d) for d in (2,4)],
            'decision_constants':constants(),
            'scope':'Finite exact complete matrix-unit, projector, Choi and weighted-Kraus identities at d=2,4. All-dimension diamond/trace-norm upper bounds, Choi entropy bounds, C5/C6 query lower bounds, Haar integration, continuous priors, session freshness and coherent extension assumptions remain analytic. No ODE, source/hardware model or full Lean kernel validation.'}

if __name__=='__main__':
    print(json.dumps(verify(),sort_keys=True))
