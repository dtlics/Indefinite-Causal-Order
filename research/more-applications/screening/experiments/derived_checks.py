"""Independent numerical and symbolic checks of new screening identities."""
from core import *
from pathlib import Path
import json, sympy as sp
ROOT=Path(__file__).resolve().parent
rng=np.random.default_rng(19013)
out={}
# Lindblad short-time self-switch coefficient.
low=np.array([[0,1],[0,0]],complex); high=low.conj().T
models=[('dephasing',np.zeros((2,2)),[np.sqrt(.7)*Z]),
        ('two_Pauli_jumps',np.zeros((2,2)),[np.sqrt(.7)*X,np.sqrt(.3)*Z]),
        ('amplitude_damping',np.zeros((2,2)),[np.sqrt(.7)*low]),
        ('thermal_jumps',np.zeros((2,2)),[np.sqrt(.7)*low,np.sqrt(.3)*high]),
        ('drive_and_dephasing',.4*X,[np.sqrt(.7)*Z]),
        ('correlated_jump',.2*Y,[.5*X+.3j*Z])]
Lrows=[]
for name,H,Ls in models:
    coeff=sum(np.linalg.norm(a@b-b@a,'fro')**2 for a in Ls for b in Ls)/8
    vals=[]
    for t in [.04,.02,.01,.005]:
        K=lindblad_channel(H,Ls,t)
        p=metrics(K,K)['p_minus']
        vals.append(dict(t=t,p_minus=p,p_over_t2=p/t**2))
    Lrows.append(dict(name=name,leading_t2_coefficient=coeff,values=vals))
out['lindblad']=Lrows
# Choi-space commutator operator identity, exact in dimensions 2,3.
exact=[]
for d in [2,3]:
    Es=[]
    for j in range(d):
        for i in range(d):
            E=sp.zeros(d);E[i,j]=1;Es.append(E)
    def sv(A):return sp.Matrix([A[i,j] for j in range(d) for i in range(d)])
    C=sp.Matrix.hstack(*[sv(B*A-A*B) for A in Es for B in Es])
    V=sv(sp.eye(d))
    lhs=C*C.T;rhs=2*d*sp.eye(d*d)-2*V*V.T
    assert lhs==rhs
    exact.append({'dimension':d,'CCdagger_identity':True,'rank':C.rank()})
out['exact_commutator_operator']=exact
# Known Pauli Kraus-span measurement normalization. T maps Pauli labels to commutator matrices/(2sqrt(d)).
spanrows=[]
for n in [1,2,3,4]:
    d=2**n
    labels=['I'*n]+['I'*j+c+'I'*(n-j-1) for j in range(n) for c in 'XYZ']
    Fs=[pauli_string(s) for s in labels]
    T=np.column_stack([vec(b@a-a@b)/(2*np.sqrt(d)) for a in Fs for b in Fs])
    norm2=float(np.linalg.eigvalsh(T@T.conj().T)[-1])
    spanrows.append(dict(n=n,basis_size=len(Fs),norm_squared=norm2))
out['single_site_error_spans']=spanrows
# Known parity check/switch equivalence and no-postselection-fidelity free lunch.
maxPCS=maxFE=maxprojective=0.
for _ in range(60):
    A=random_channel(2,4,rng);B=random_channel(2,4,rng)
    plus,minus=switch_branches(A,B)
    m=metrics(A,B)
    maxFE=max(maxFE,abs(m['Fe_plus_joint']-m['Fe_AB']),m['Fe_minus_joint'])
    # final P removes intended P from S(P,E), yielding Kraus even/odd conjugation.
    P=PAULI[int(rng.integers(1,4))]
    kp,km=switch_branches([P],A)
    pcs_p=[(k+P@k@P)/2 for k in A];pcs_m=[(k-P@k@P)/2 for k in A]
    maxPCS=max(maxPCS,np.linalg.norm(choi([P@k for k in kp])-choi(pcs_p)),np.linalg.norm(choi([P@k for k in km])-choi(pcs_m)))
    # visible projective ABA estimator, one rank2 projector in dimension3.
for _ in range(20):
    U,_=np.linalg.qr(rng.normal(size=(3,3))+1j*rng.normal(size=(3,3)))
    Ps=[U@np.diag([1,1,0])@U.conj().T,U@np.diag([0,0,1])@U.conj().T]
    B=random_channel(3,5,rng)
    agree=sum(np.linalg.norm(p@b@p)**2 for p in Ps for b in B)/3
    maxprojective=max(maxprojective,abs(agree-metrics(Ps,B)['v']))
out['max_PCS_identity_residual']=float(maxPCS)
out['max_entanglement_fidelity_weight_identity_error']=maxFE
out['max_one_visible_projector_ABA_error']=maxprojective
# Leakage minus branch on computational code; every Kraus annihilates |0>.
leakrows=[]
for g,h in [(0.05,.8),(.5,1),(.01,.01)]:
    A=jump_channel(3,1,2,g);B=jump_channel(3,2,1,h)
    plus,minus=switch_branches(A,B)
    V=np.eye(3)[:,:2]
    K=[k@V for k in minus]
    # Input |0> is annihilated, making this trace-decreasing map EB on the logical qubit.
    assert max(np.linalg.norm(k[:,0]) for k in K)<1e-14
    computed=sum(np.linalg.norm(k[:,1])**2 for k in K)
    predicted=g*((1-np.sqrt(1-h))**2+h)/4
    assert abs(computed-predicted)<1e-12
    leakrows.append(dict(leakage=g,repump=h,p_minus_given_logical_one=computed,p_minus_given_logical_zero=0,minus_EB_on_code=True))
out['leakage']=leakrows
# Same-distribution Pauli self-switch vs bias parameter.
noise=[]
for probs in [[.97,.01,.01,.01],[.97,.001,.001,.028],[.97,0,0,.03]]:
    K=pauli_channel(probs);p=metrics(K,K)['p_minus'];s=1-probs[0]
    noise.append(dict(distribution=probs,p_minus=p,normalized_error_diversity=p/s**2))
out['bias_signatures']=noise
# Gaussian Weyl-kick fingerprint, independent of target state: v=(1+sx^2 sp^2)^(-1/2) for [x,p]=i.
# Monte Carlo verification of E cos(XP) against the Gaussian integral.
mc=[]
for sx,sp_ in [(.1,.2),(.5,.7),(1.,1.5)]:
    samples=1000000
    val=float(np.mean(np.cos(rng.normal(0,sx,samples)*rng.normal(0,sp_,samples))))
    analytic=1/np.sqrt(1+sx*sx*sp_*sp_)
    mc.append(dict(sigma_x=sx,sigma_p=sp_,analytic_visibility=analytic,monte_carlo_visibility=val,N=samples))
out['Gaussian_kicks']=mc
(ROOT/'derived_checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
