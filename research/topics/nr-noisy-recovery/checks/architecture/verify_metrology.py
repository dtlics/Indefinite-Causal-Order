"""Exact metrology benchmark: adaptive-comb dual, SWITCH readout and echo.

No optimizer, NumPy or floating-point feasibility check is used. This
rebuilds the authors' sequential dual LMI at phi=0 from Kraus derivatives.
Rational square-root enclosures and exact LDL establish its positivity.
Phase covariance transfers the bound to every local working point.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json, math

if not __debug__:
    raise RuntimeError('Exact certificate requires Python without -O.')

HERE=Path(__file__).resolve().parent

def interval(a,b=None):return (F(a),F(a if b is None else b))
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def mul(a,b):
    v=[x*y for x in a for y in b]
    return min(v),max(v)
def sqrt_bounds(x,digits=30):
    scale=10**digits
    n=isqrt(x.numerator*scale**2//x.denominator)
    lo,hi=F(n,scale),F(n+1,scale)
    assert lo*lo<=x<=hi*hi
    return lo,hi
def ldl_positive(matrix):
    n=len(matrix);L=[[F(i==j) for j in range(n)] for i in range(n)];pivots=[]
    assert matrix==list(map(list,zip(*matrix)))
    for j in range(n):
        pivot=matrix[j][j]-sum(L[j][k]**2*pivots[k] for k in range(j))
        assert pivot>0,('nonpositive exact LDL pivot',j,pivot)
        pivots.append(pivot)
        for i in range(j+1,n):
            L[i][j]=(matrix[i][j]-sum(L[i][k]*L[j][k]*pivots[k] for k in range(j)))/pivot
    # Reconstruct every coordinate, including the zero pattern.
    for i in range(n):
        for j in range(n):
            assert matrix[i][j]==sum(L[i][k]*pivots[k]*L[j][k] for k in range(n))
    return pivots

def verify_sequential(certificate):
    assert certificate['schema']=='metrology-ad-two-query-dual-v1'
    assert certificate['queries']==2 and certificate['local_working_point']=='0'
    p=F(certificate['decay_probability']);q=1-p
    assert p==F(2,5) and F(certificate['exposure_time'])==1
    assert all(type(v) is str for v in certificate['h_diagonal'])
    assert len(certificate['h_diagonal'])==4
    h=list(map(F,certificate['h_diagonal']))
    assert len(certificate['Q'])==4 and all(len(row)==4 for row in certificate['Q'])
    assert all(type(v) is str for row in certificate['Q'] for v in row)
    Q=[list(map(F,row)) for row in certificate['Q']]
    assert Q==list(map(list,zip(*Q)))
    a=sqrt_bounds(q);b=sqrt_bounds(p)
    # Tr_output Q=I_input is exact; no approximate normalization is trusted.
    assert [[Q[i][j]+Q[2+i][2+j] for j in range(2)] for i in range(2)]==[[1,0],[0,1]]
    lam=F(certificate['QFI_upper']);assert lam==F(64,25)
    z=interval(0);one=interval(1)
    K=[[[one,z],[z,a]],[[z,b],[z,z]]]
    # N_i=vec(K_i2) tensor vec(K_i1), with output-first row-major vectorization.
    # At phi=0, dot N=i*delta*N, delta=sum of input-column Z phases.
    vectors=[];derivative_weights=[]
    for k2 in range(2):
        for k1 in range(2):
            v=[];w=[]
            for o2 in range(2):
                for i2 in range(2):
                    for o1 in range(2):
                        for i1 in range(2):
                            v.append(mul(K[k2][o2][i2],K[k1][o1][i1]))
                            w.append(F(i2+i1-1))
            vectors.append(v);derivative_weights.append(w)
    T=[[z for _ in range(8)] for _ in range(8)]
    for i in range(4):
        for last_output in range(2):
            for row in range(8):
                index=last_output*8+row
                T[row][2*i+last_output]=mul(vectors[i][index],interval(h[i]-derivative_weights[i][index]))
    # A=[[lambda I/4,T^T],[T,I tensor Q]] is unitarily congruent to the
    # complex author LMI whose offdiagonal block is i*T.
    A=[[z for _ in range(16)] for _ in range(16)]
    for i in range(8):
        A[i][i]=interval(lam/4)
        for j in range(8):
            A[8+j][i]=A[i][8+j]=T[j][i]
            A[8+i][8+j]=interval(Q[i%4][j%4] if i//4==j//4 else 0)
    center=[[(v[0]+v[1])/2 for v in row] for row in A]
    # Every true entry is within its enclosing interval. Symmetry gives
    # spectral norm <= maximum absolute row sum <= this exact radius.
    radius=max(sum((hi-lo)/2 for lo,hi in row) for row in A)
    safe=[[center[i][j]-(radius if i==j else 0) for j in range(16)] for i in range(16)]
    pivots=ldl_positive(safe)
    # Thus true A >= center-radius I >0 and the dual proves QFI<=lambda.
    out=dict(status='passed',arithmetic='stdlib Fractions; exact interval containment and LDL reconstruction',
             p=str(p),local_phi='0; all local phi follow by phase covariance',queries=2,
             sequential_QFI_upper=str(lam),h_diagonal=[str(x) for x in h],
             Q=[[str(x) for x in row] for row in Q],
             sqrt_q_interval=[str(x) for x in a],sqrt_p_interval=[str(x) for x in b],
             interval_operator_radius=str(radius),strict_LDL_pivots=16,
             minimum_pivot_positive=True,minimum_pivot_decimal=float(min(pivots)),
             all_LDL_coordinates_reconstructed=True,
             scope='All deterministic two-query sequential strategies with arbitrary ancillary quantum memory, controls and final measurements; local single-parameter QFI. The process/dual theorem is the cited mathematical input.')
    return out


def poly_add(a,b):
    return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]
def poly_mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c
def poly_scale(a,x):return [x*y for y in a]

def verify_switch_and_echo():
    p,q,x=F(2,5),F(3,5),F(2,3)
    nojump=1-x+x*q*q;jump=x*p*(1+q)
    assert nojump+jump==1 and nojump==F(43,75) and jump==F(32,75)
    # p_y+ =p_y-=nojump/2; derivatives squared are4q虏x(1-x).
    # p_c+ =p_c-=jump/2; derivatives squared arex虏p虏q nu虏.
    nojump_F=2*(4*q*q*x*(1-x))/(nojump/2)
    jump_coefficient=2*(x*x*p*p*q)/(jump/2)
    assert nojump_F==F(96,43) and jump_coefficient==F(2,5)
    ideal=nojump_F+jump_coefficient;upper=F(64,25)
    assert ideal==F(566,215) and ideal-upper==F(78,1075)
    threshold_nu_sq=(upper-nojump_F)/jump_coefficient
    assert threshold_nu_sq==F(176,215)
    rows=[]
    for nu,eta in ((F(1),F(1)),(F(97,100),F(1)),(F(97,100),F(99,100))):
        fish=nojump_F+jump_coefficient*nu*nu
        survival_threshold=upper/fish
        physical=eta*fish
        rows.append(dict(visibility=str(nu),independent_erasure_survival=str(eta),
                         switch_FI=str(physical),switch_FI_decimal=float(physical),
                         gap_over_certified_all_sequential_upper=str(physical-upper),
                         gap_decimal=float(physical-upper),
                         minimum_survival_to_beat_upper=str(survival_threshold),
                         maximum_round_duration_ratio_to_beat_upper=str(physical/upper)))
        assert physical>upper
    # Independently verify the retained-environment echo dominance identity.
    # r=sqrt(q), all-input ideal SWITCH maxF root formula; denominators positive.
    left=poly_add(poly_mul([1,0,3],poly_mul([1,0,0,0,-1],[1,0,0,0,-1])),
             poly_scale(poly_mul([0,0,4],poly_mul([1,0,1,-2],[1,0,1,-2])),-1))
    right=poly_mul(poly_mul([1,-1],[1,-1]),poly_mul([1,-1],[1,-1]))
    right=poly_mul(right,[1,4,9,16,15,12,3])
    assert left==right
    out=dict(status='passed',arithmetic='stdlib exact Fractions and integer polynomials',
             input='sqrt(1/3)|00>_TR+sqrt(2/3)|11>_TR, plus_C',
             p=str(p),working_point='phi=pi/2; t=1 each use',
             unconditional_readout_probabilities=[str(nojump/2)]*2+[str(jump/2)]*2,
             nojump_FI=str(nojump_F),jump_FI_visibility_squared_coefficient=str(jump_coefficient),
             ideal_two_query_FI=str(ideal),certified_all_sequential_upper=str(upper),
             ideal_gap=str(ideal-upper),minimum_visibility_squared=str(threshold_nu_sq),
             minimum_visibility_decimal=math.sqrt(float(threshold_nu_sq)),robustness=rows,
             retained_bath_echo_polynomial_identity='(1-r)^4(1+4r+9r^2+16r^3+15r^4+12r^5+3r^6)',
             retained_bath_echo_scope='Different native resource: cold inaccessible environment retained between two visits; not fresh independent AD calls.',
             limitations=['Local known-working-point single-parameter information, not a global finite-sample MSE claim.',
                          'Known p; clean reference/helper/readout except specified control dephasing and independent flagged erasure.',
                          'Walltime comparison requires measured durations; ratio entries are sufficient conditional thresholds.'])
    return out



def verify_regular_echo():
    p,q=F(2,5),F(3,5)
    c,s=F(99,101),F(20,101)
    assert c*c+s*s==1
    c2,s2=c*c-s*s,2*c*s
    coherence=p*c+q*c2
    derivative=p*s+2*q*s2
    assert -1<coherence<1
    fisher=derivative**2/(1-coherence**2)
    # The all-input ideal SWITCH formula is decreasing in sqrt(q) here.
    lo,hi=sqrt_bounds(q)
    inside=1+q-2*q*lo
    assert inside>0
    switch_upper=4*q*inside**2/(1-q*q)**2
    assert F(2323,3000)**2<q
    assert F(321,16)-F(45,2)*F(2323,3000)==F(66,25)
    assert switch_upper<F(66,25)<F(8,3)<fisher
    additional=dict(cos_offset=str(c),sin_offset=str(s),classical_FI=str(fisher))
    c,s=F(399,401),F(40,401)
    assert c*c+s*s==1
    coherence=p*c+q*(c*c-s*s)
    derivative=p*s+4*q*s*c
    assert -1<coherence<1
    fisher=derivative**2/(1-coherence**2)
    assert fisher==F(6249620000,2236326803)>F(279,100)
    assert (1-coherence)/2==F(5602,804005)
    return dict(status='passed',cos_offset=str(c),sin_offset=str(s),
                retained_environment_echo_classical_FI=str(fisher),
                echo_FI_decimal=float(fisher),iid_SWITCH_all_input_QFI_less_than='66/25',
                readout_probabilities=[str((1+coherence)/2),str((1-coherence)/2)],
                additional_regular_point=additional,
                scope='Regular finite-offset X readout for the analytically specified retained-environment collision echo; not fresh iid AD calls.')


def verify_longer_ordinary_block():
    # Exact Q(sqrt(15)) arithmetic for the analytically specified feedback
    # protocol. This is a feasible lower bound, not a numerical N3 optimum.
    def plus(a,b):return (a[0]+b[0],a[1]+b[1])
    def times(a,b):return (a[0]*b[0]+15*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
    def weighted(a,w):return (a[0]*w,a[1]*w)
    n,j=F(4,5),F(1,5)
    r=(F(0),F(1,4));t=(F(0),F(0));ts=[]
    for _ in range(3):
        t=times(r,plus(t,(F(1,2),F(0))))
        ts.append(t)
    weights=[j*n,j*n*n,n**3]
    assert sum(weights,F(0))+j==1
    fisher=(F(0),F(0))
    for tangent,probability in zip(ts,weights):
        fisher=plus(fisher,weighted(times(tangent,tangent),4*probability))
    assert fisher==(F(843,320),F(168,320))
    assert F(15,4)**2<15 and F(387,100)**2<15
    lower=fisher[0]+fisher[1]*F(15,4)
    assert lower>F(9,2)
    # The all-input/all-phase ideal two-call SWITCH optimum at p=2/5.
    switch_upper=(321-72*F(387,100))/16
    assert switch_upper<F(8,3)
    launch=F(2,3)
    assert launch*3==2 and launch*lower>3>switch_upper
    assert lower/3>F(3,2)>F(4,3)>switch_upper/2
    return dict(status='passed',three_query_feedback_FI='(843+168 sqrt(15))/320',
                exact_coefficients=[str(v) for v in fisher],
                three_query_FI_strict_lower='9/2',two_query_SWITCH_FI_strict_upper='8/3',
                launch_probability=str(launch),expected_query_cost='2',
                launched_protocol_FI_strict_lower='3',
                scope='Exact feedback-tangent and recorded-history scalar algebra; the feasible three-call protocol is proved in metrology.md. This excludes an unrestricted per-query or mean-two-query interpretation of the hard-two-query benchmark.')


def main():
    certificate=json.loads((HERE/'metrology_sequential_certificate.json').read_text(encoding='utf-8'))
    report=dict(status='passed',arithmetic='Python standard library; exact rational intervals, LDL and integer polynomials',
                sequential_dual=verify_sequential(certificate),
                SWITCH_readout_and_robustness=verify_switch_and_echo(),
                retained_collision_echo=verify_regular_echo(),
                longer_ordinary_block=verify_longer_ordinary_block(),
                scope='Finite algebra/certificate replay. General tester semantics, all-input covariance/concavity and native collision-interface proofs remain in metrology.md; no numerical SDP or hardware-runtime certificate.')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
