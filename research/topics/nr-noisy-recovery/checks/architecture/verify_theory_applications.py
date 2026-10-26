"""Finite exact guards for the current C5/C6 application extensions.

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
from math import comb,prod

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

def verify_base():
    return {'status':'passed','arithmetic':'stdlib Fraction Gaussian rationals; no floating point',
            'helper_import_printed_nothing':True,'helper':str(HELPER),
            'helper_sha256':hashlib.sha256(HELPER.read_bytes()).hexdigest(),
            'geometry_cases':[case(d,c) for d in (2,4) for c in (False,True)],
            'freshness_algebra_cases':[freshness_case(d) for d in (2,4)],
            'decision_constants':constants(),
            'scope':'Finite exact complete matrix-unit, projector, Choi and weighted-Kraus identities at d=2,4. All-dimension diamond/trace-norm upper bounds, Choi entropy bounds, C5/C6 query lower bounds, Haar integration, continuous priors, session freshness and coherent extension assumptions remain analytic. No ODE, source/hardware model or full Lean kernel validation.'}

def robust_constants():
    epsilon=F(1,24)
    remainder=epsilon+2*epsilon*epsilon
    require(remainder==F(13,288),'robust event remainder')
    rapid_self=F(1,8)-remainder
    rapid_pair=F(1,4)-remainder
    require(rapid_self==F(23,288) and rapid_pair==F(59,288),
            'robust event bands')
    rapid_horizon=F(1,4)+F(5,2)*epsilon
    slow_horizon=F(1,2)-3*epsilon
    require(rapid_horizon==F(17,48) and slow_horizon==F(18,48),
            'robust horizon-three endpoint arithmetic')
    require(rapid_horizon<slow_horizon,'disjoint robust horizon bands')
    require(3*epsilon==F(1,8) and F(1,2)-3*epsilon==F(3,8),
            'robust deletion endpoint arithmetic')
    def binomial_cdf2(p):
        return sum((comb(43,k)*p**k*(1-p)**(43-k) for k in range(3)),F())
    slow_error=1-binomial_cdf2(remainder)
    rapid_error=binomial_cdf2(rapid_self)
    delete_error=1-(1-remainder)**5
    keep_error=(1-rapid_pair)**5
    errors=(slow_error,rapid_error,delete_error,keep_error)
    require(all(0<e<F(1,3) for e in errors),'exact robust binomial error bounds')
    require(F(1,16)-remainder==F(5,288)
            and rapid_self-F(1,16)==F(5,288),'robust sample-mean margin')
    return {'epsilon':str(epsilon),'event_remainder':str(remainder),
            'self_event_bands':[str(remainder),str(rapid_self)],
            'pair_event_bands':[str(remainder),str(rapid_pair)],
            'horizon_three_bounds':[str(rapid_horizon),str(slow_horizon)],
            'self_trials':43,'self_minus_threshold':3,
            'pair_trials':5,'pair_minus_threshold':1,
            'exact_errors':[str(e) for e in errors],
            'scope':'Rational endpoint and binomial calculations only. The all-dimension diamond-ball decomposition, continuity inequalities, monotonicity and independent-trial premises remain analytic.'}


def nonunital_pinching_tester():
    d=2;p,q=flat_projectors(d)
    a,b=projector_family(p),projector_family(q)
    k0=[[C(1),C()],[C(),C(F(3,5))]]
    k1=[[C(),C(F(4,5))],[C(),C()]]
    damp=[(F(1),k0),(F(1),k1)]
    tp,unital=effects(damp)
    require(tp==eye(d),'amplitude damping trace preserving')
    expected_unital=[[C(F(41,25)),C()],[C(),C(F(9,25))]]
    require(unital==expected_unital and unital!=eye(d),'amplitude damping nonunital')
    jc=choi(damp)
    r0=scale(choi([(F(1),k0)]),F(25,17))
    r1=scale(choi([(F(1),k1)]),F(25,8))
    check_projector(r0,1,'damping first Choi eigenspace')
    check_projector(r1,1,'damping second Choi eigenspace')
    require(mul(r0,r1)==zero(d*d),'damping Choi eigenspaces orthogonal')
    require(jc==add(scale(r0,F(17,25)),scale(r1,F(8,25)))
            and trace(jc)==1,'normalized nonunital Choi state spectrum')
    pi_a,pi_b=scale(choi(a),d),scale(choi(b),d)
    check_projector(pi_a,d,'pinching A normalized-Choi tester')
    check_projector(pi_b,d,'pinching B normalized-Choi tester')
    overlap_a=trace(mul(pi_a,jc));overlap_b=trace(mul(pi_b,jc))
    require(overlap_a==F(17,25) and overlap_b==F(4,5),
            'nonunital normalized-Choi tester overlaps')
    direct_a,direct_b=minus(damp,a),minus(damp,b)
    require(direct_a==F(4,25) and direct_b==F(1,10),
            'direct nonunital commutator event')
    require(C(direct_a)==(1-overlap_a)/2
            and C(direct_b)==(1-overlap_b)/2,'normalized-Choi event identity')
    phi=mix(a,b,F(1,2));tester=scale(add(pi_a,pi_b),F(1,2))
    mixed_overlap=trace(mul(tester,jc));mixed_event=minus(damp,phi)
    require(mixed_overlap==F(37,50) and mixed_event==F(13,100)
            and C(mixed_event)==(1-mixed_overlap)/2,'mixed-center tester identity')
    return {'d':d,'damping_survival_amplitude':'3/5','damping_jump_amplitude':'4/5',
            'trace_preserving':True,'nonunital':True,
            'Choi_eigenvalues':['17/25','8/25','0','0'],
            'pinching_tester_overlaps':[str(overlap_a.r),str(overlap_b.r)],
            'pinching_minus_events':[str(direct_a),str(direct_b)],
            'mixture_minus_event':str(mixed_event),
            'scope':'An actual nonunital channel checks the normalized-Choi event formula. No general SDP or channel-distance continuity theorem is inferred.'}


def capacity_case(d):
    t=F(3,4);beta=t*F(d,d+1)
    ident=[(F(1),eye(d))];om=omega_family(d)
    p,_=flat_projectors(d);a=projector_family(p)
    lam=mix(ident,om,F(d,d+1))
    rapid=mix(ident,lam,t);rapid_depolarizing=mix(ident,om,beta)
    static=mix(ident,a,t)
    for label,family in (('rapid capacity channel',rapid),('static capacity channel',static)):
        check_channel(family,label)
    require(supermatrix(rapid)==supermatrix(rapid_depolarizing),
            'NR22 rapid replacement parameter conversion')
    jid=choi(ident);rest=add(eye(d*d),jid,-1)
    check_projector(jid,1,'rapid leading Choi eigenspace')
    check_projector(rest,d*d-1,'rapid residual Choi eigenspace')
    leading=1-t+t/d;rapid_tail=t/F(d*(d+1))
    require(choi(rapid)==add(scale(jid,leading),scale(rest,rapid_tail)),
            'NR22 rapid t=3/4 full Choi spectrum')
    static_tail=add(scale(choi(a),d),jid,-1)
    check_projector(static_tail,d-1,'static residual Choi eigenspace')
    require(choi(static)==add(scale(jid,leading),scale(static_tail,t/d)),
            'NR22 static t=3/4 full Choi spectrum')
    require(beta>=F(1,2),'finite rapid antidegradable parameter regime')
    require(minus(static,static)==0
            and minus(rapid,rapid)==t*t*F(d-1,2*(d+1)),
            'NR22 capacity diagnostic event at t=3/4')
    return {'d':d,'t':str(t),'rapid_replacement_beta':str(beta),
            'rapid_Choi_spectrum':{'leading':str(leading),'tail':str(rapid_tail),
                                   'tail_multiplicity':d*d-1},
            'static_Choi_spectrum':{'leading':str(leading),'tail':str(t/d),
                                    'tail_multiplicity':d-1,'zero_multiplicity':d*d-d},
            'rapid_minus':str(minus(rapid,rapid)),
            'scope':'Complete finite normalized-Choi and event identities at this d. General antidegradability, common-code existence and capacity bounds remain analytic.'}


def index_digits(index,dims):
    out=[]
    for dim in reversed(dims):out.append(index%dim);index//=dim
    require(index==0,'tensor index domain')
    return tuple(reversed(out))


def flat_index(digits,dims):
    index=0
    for digit,dim in zip(digits,dims):index=index*dim+digit
    return index


def partial_trace(x,dims,traced):
    require(len(x)==prod(dims),'partial-trace tensor dimensions')
    kept=tuple(i for i in range(len(dims)) if i not in traced)
    kept_dims=tuple(dims[i] for i in kept)
    out=zero(prod(kept_dims))
    digits=[index_digits(i,dims) for i in range(len(x))]
    for i,left in enumerate(digits):
        for j,right in enumerate(digits):
            if all(left[a]==right[a] for a in traced):
                a=flat_index(tuple(left[k] for k in kept),kept_dims)
                b=flat_index(tuple(right[k] for k in kept),kept_dims)
                out[a][b]+=x[i][j]
    return out


def choi_from_map(input_d,output_d,action):
    out=zero(input_d*output_d)
    for a in range(input_d):
        for b in range(input_d):
            out=add(out,scale(tensor(action(matrix_unit(input_d,a,b)),
                                    matrix_unit(input_d,a,b)),F(1,input_d)))
    return out


def logical_extension():
    d=2;t=F(3,4);beta=t*F(d,d+1);tau=scale(eye(d),F(1,d))
    require(beta==F(1,2),'d2 NR22 symmetric-extension parameter')
    def extension(x):
        copies=add(tensor(x,tau),tensor(tau,x))
        return add(scale(copies,1-beta),
                   scale(tensor(tau,tau),(2*beta-1)*trace(x)))
    # Normalized extension Choi order is B1,B2,R; the output channel is 2->4.
    jext=choi_from_map(d,d*d,extension)
    dims=(d,d,d);bell1,bell2=zero(d**3),zero(d**3)
    for i in range(d**3):
        a,b,r=index_digits(i,dims)
        for j in range(d**3):
            aa,bb,rr=index_digits(j,dims)
            if a==r and aa==rr and b==bb:bell1[i][j]=C(F(1,d))
            if b==r and bb==rr and a==aa:bell2[i][j]=C(F(1,d))
    check_projector(bell1,d,'logical Bell projector with spectator B2')
    check_projector(bell2,d,'logical Bell projector with spectator B1')
    require(mul(mul(bell1,bell2),bell1)==scale(bell1,F(1,4)),
            'logical Bell projector overlap')
    s=add(bell1,bell2);s2=mul(s,s)
    plus=add(scale(s2,F(2,3)),scale(s,-F(1,3)))
    small=add(scale(s2,-2),scale(s,3))
    kernel=add(add(eye(d**3),plus,-1),small,-1)
    check_projector(plus,2,'logical Bell sum eigenvalue 3/2')
    check_projector(small,2,'logical Bell sum eigenvalue 1/2')
    check_projector(kernel,4,'logical Bell sum kernel')
    require(mul(plus,small)==zero(d**3),'logical Bell spectral orthogonality')
    require(s==add(scale(plus,F(3,2)),scale(small,F(1,2))),
            'logical Bell sum exact spectrum')
    require(F(3,2)/2==F(3,4),'logical qubit Bell-fidelity ceiling arithmetic')
    require(jext==scale(s,F(1,4)) and trace(jext)==1,
            'symmetric extension normalized Choi equality and positivity')
    swap=zero(d**3)
    for i in range(d**3):
        a,b,r=index_digits(i,dims)
        swap[flat_index((b,a,r),dims)][i]=C(1)
    require(mul(mul(swap,jext),adj(swap))==jext,'extension output-swap symmetry')
    rapid=mix([(F(1),eye(d))],omega_family(d),beta)
    jrapid=choi(rapid)
    require(partial_trace(jext,dims,(1,))==jrapid
            and partial_trace(jext,dims,(0,))==jrapid,'both rapid Choi marginals')
    require(partial_trace(jext,dims,(0,1))==scale(eye(d),F(1,d)),
            'symmetric extension trace-preserving Choi marginal')
    require(partial_trace(jext,dims,(2,))==scale(eye(d*d),F(1,d*d)),
            'symmetric extension maximally mixed output marginal')
    for a in range(d):
        for b in range(d):
            x=matrix_unit(d,a,b);out=extension(x);expected=apply(rapid,x)
            require(partial_trace(out,(d,d),(1,))==expected
                    and partial_trace(out,(d,d),(0,))==expected,
                    'both extension marginals on all matrix units')
    bell=choi([(F(1),eye(d))])
    require(trace(mul(bell,jrapid))==F(5,8),
            'particular rapid marginal Bell overlap is 5/8, not ceiling 3/4')
    return {'d':d,'order':['B1','B2','R'],'replacement_beta':str(beta),
            'extension_Choi_eigenvalues':{'3/8':2,'1/8':2,'0':4},
            'both_output_marginals_checked':True,'all_input_matrix_units_checked':True,
            'logical_Bell_projector_sum_spectrum':{'3/2':2,'1/2':2,'0':4},
            'logical_qubit_Bell_ceiling':'3/4','particular_rapid_Bell_overlap':'5/8',
            'scope':'Actual 2->4 extension and K=2 projector spectrum only. Tensor-power extensions, arbitrary encoders/decoders, all-K overlap norms and the universal coding theorem remain analytic.'}


def block_counterexample():
    d=4;p,_=flat_projectors(d);_,local=flat_projectors(2);q=[]
    for offset in (0,2):
        for small in local:
            large=zero(d)
            for i in range(2):
                for j in range(2):large[offset+i][offset+j]=small[i][j]
            q.append(large)
    check_resolution(q,d,'block-Hadamard rank-one resolution')
    a,b=projector_family(p),projector_family(q);phi=mix(a,b,F(1,2))
    overlap=[[trace(mul(pi,qj)) for qj in q] for pi in p]
    expected=[[C(F(1,2) if i//2==j//2 else 0) for j in range(d)] for i in range(d)]
    require(overlap==expected,'block-Hadamard overlap matrix')
    require(visibility(a,b)==F(1,2) and visibility(phi,phi)==F(3,4),
            'block-Hadamard cross/self scalar distinction')
    state=zero(d);state[0][0]=state[1][1]=C(F(1,2))
    require(apply(a,state)==state and apply(b,state)==state
            and apply(phi,state)==state,'actual nonreplacement fixed state')
    difference=add(state,scale(eye(d),F(1,d)),-1)
    require(all(difference[i][j]==0 for i in range(d) for j in range(d) if i!=j),
            'block witness diagonal trace norm')
    require(sum((abs(difference[i][i].r) for i in range(d)),F())/2==F(1,2),
            'block witness half trace distance')
    return {'d':d,'cross_visibility':'1/2','self_visibility':'3/4',
            'fixed_state_half_distance_from_replacement':'1/2',
            'scope':'Exact rational block-Hadamard nonmixing ingredient. The irrational equal-scalar comparison and general principal-angle theorem remain analytic.'}


def entropy_integer_guard():
    # h2(3/4)=2-(3/4)log2(3)<13/16 iff 3^12>2^19.
    require(3**12>2**19 and 3**12-2**19==7153,'binary entropy integer witness')
    require(F(4,4)-F(13,16)==F(3,16)>0,'n=4 lower-rate witness arithmetic')
    return {'integer_comparison':'3^12 > 2^19','positive_difference':7153,
            'h2_three_quarters_upper_bound':'13/16','n4_rate_lower_witness':'3/16',
            'scope':'The exact integer comparison is linked only to the displayed elementary binary-entropy identity. The compound coding and all-dimension entropy/capacity deductions remain analytic.'}


def verify():
    out=verify_base()
    out.update({'base_guard_source_sha256':'5d6afa9af80c15486e707b084c3e73f561a04458ee7a9d46a5b536b397436144',
                'robustness_constants':robust_constants(),
                'nonunital_pinching_tester':nonunital_pinching_tester(),
                'NR22_capacity_cases':[capacity_case(d) for d in (2,4)],
                'd2_extension_and_logical_overlap':logical_extension(),
                'd4_block_nonmixing':block_counterexample(),
                'binary_entropy_integer_guard':entropy_integer_guard(),
                'scope':'Finite exact stdlib identities only: old d=2,4 guards, rational robustness/binomial endpoints, a nonunital normalized-Choi tester, t=3/4 rapid/static Choi spectra, the actual d=2 symmetric extension with all marginals, K=2 Bell-projector overlap and a rational block-Hadamard fixed state. All-dimension norm/SDP/principal-angle theorems, C5/C6 bounds, independent sampling/coherent freshness, all-K code ceilings and universal compound coding remain analytic. No ODE, fitting, exhaustive stronger claim or formal-kernel validation.'})
    return out


if __name__=='__main__':
    print(json.dumps(verify(),sort_keys=True))
