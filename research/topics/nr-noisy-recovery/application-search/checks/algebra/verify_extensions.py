"""Further algebraic/numerical checks. No external service or secret data required."""
from __future__ import annotations
import json, math, itertools
from pathlib import Path
import numpy as np
import sympy as sp
from explore import I,X,Y,Z,PAULIS,random_channel,random_unitary,branch,nested,choi,score,gad,replacement
OUT=Path(__file__).resolve().parent
rng=np.random.default_rng(910373)


def sequential(ks):
    ms=branch(ks,ks,-1)
    return [b@a for a in ms for b in ms]


def canonical(u):
    flat=u.ravel(); k=next(i for i,x in enumerate(flat) if abs(x)>1e-8)
    v=u/(flat[k]/abs(flat[k]));return tuple(np.round(v.real,9).ravel())+tuple(np.round(v.imag,9).ravel())
H=(X+Z)/np.sqrt(2); S=np.diag([1,1j])
cliff=[I];seen={canonical(I)}
for u in cliff:
    for g in [H,S]:
        v=g@u;key=canonical(v)
        if key not in seen:cliff.append(v);seen.add(key)
assert len(cliff)==24

rows=[]
for _ in range(80):
    U=random_unitary(rng);a=random_unitary(rng)[:,0];b=random_unitary(rng)[:,0]
    ks=[np.outer(a,U[:,0].conj()),np.outer(b,U[:,1].conj())]
    f=float(abs(np.vdot(a,b))**2)
    results=[score(sequential([w@k for k in ks])) for w in cliff]
    pred=(1-f)*(2-f)/24
    rows.append({'overlap':f,'mean_p':float(np.mean([r['p'] for r in results])),
                 'predicted':pred,'max_residual':max(r['scalar_kraus_residual'] for r in results)})
meas=[]
for _ in range(50):
    U=random_unitary(rng);ks=[np.outer(U[:,i],U[:,i].conj()) for i in range(2)]
    ps=[score(sequential([w@k for k in ks]))['p'] for w in cliff]
    meas.append(float(np.mean(ps)))

# Verify arbitrary 2-Kraus scalar identity, with no measure-prepare promise.
r2=[]
for _ in range(100):
    ks=random_channel(rng,2);out=score(sequential(ks));c=ks[0]@ks[1]-ks[1]@ks[0]
    out['predicted']=float(abs(np.linalg.det(c))**2/4);r2.append(out)

# Fixed-pure channels, arbitrary convex combination of phase-rotated amplitude damping.
fixed=[]
for _ in range(50):
    u=random_unitary(rng);ks=[]
    weights=rng.dirichlet(np.ones(3))
    for w in weights:
        g=float(rng.uniform());a=float(rng.uniform(0,2*np.pi));phase=np.diag([1,np.exp(1j*a)])
        for k in gad(g,0)[:2]:ks.append(np.sqrt(w)*u@phase@k@u.conj().T)
    fixed.append(score(nested(ks,ks,ks,ks))['p'])

# Full eight-flag instrument completeness, including unrelated maps.
complete=[]
for _ in range(15):
    ch=[random_channel(rng,int(rng.integers(2,5))) for j in range(4)]
    allk=[k for flags in itertools.product([-1,1],repeat=3) for k in nested(*ch,flags=flags)]
    complete.append(float(np.linalg.norm(sum(k.conj().T@k for k in allk)-I)))

# Generalized amplitude-damping yield and EB eigenvalue.
gadrows=[]
for gamma in [.01,.1,.5,.9,.95,1.]:
  for e in [0.,.1,.25,.5]:
    ks=gad(gamma,e);out=score(nested(ks,ks,ks,ks));p=out['p'];s=math.sqrt(1-gamma)
    pred=e*(1-e)*gamma**2*(1-s)**4/8+e**2*(1-e)**2*gamma**4/4
    J=choi(ks);pt=J.reshape(2,2,2,2).transpose(0,3,2,1).reshape(4,4)
    N=math.ceil(math.log(.01)/math.log1p(-p)) if p>1e-16 else None
    gadrows.append({'gamma':gamma,'excited':e,'p':p,'predicted':pred,'Choi_PPT_min_eig':float(np.linalg.eigvalsh(pt)[0]),
                    'attempts_99':N,'calls_99':4*N if N else None,'mean_calls':4/p if p>1e-16 else None})

# Explicit 3-bit readout errors. On Bell input compute all branch maps and weights.
flagrows=[]
for name,ks in [('GAD95_25',gad(.95,.25)),('depolarizer',replacement(I/2))]:
    branches={flags:choi(nested(ks,ks,ks,ks,flags)) for flags in itertools.product([-1,1],repeat=3)}
    phi=I.reshape(-1,order='F')/np.sqrt(2);target=(-1,-1,1)
    p=score(nested(ks,ks,ks,ks))['p']
    for eta in [0.,1e-5,1e-4,.001,.01]:
        jout=sum((eta**sum(x!=y for x,y in zip(flags,target))*(1-eta)**sum(x==y for x,y in zip(flags,target)))*J for flags,J in branches.items())
        prob=float(np.trace(jout).real);F=float(np.vdot(phi,jout@phi).real/prob)
        bound=eta*(1-p)/((1-eta)*p+eta*(1-p)) if eta else 0
        flagrows.append({'model':name,'flag_error':eta,'accepted_probability_Bell':prob,'conditional_Bell_fidelity':F,'reference_complete_conditional_error_upper':bound})

# Exact symbolic qubit central identity for arbitrary 2x2 matrix entries.
a,b,c,d,e,f=sp.symbols('a b c d e f')
T=sp.Matrix([[a,b],[c,-a]]);U=sp.Matrix([[d,e],[f,-d]])
central=T*U+U*T-sp.trace(T*U)*sp.eye(2)
assert central==sp.zeros(2)

# Exact symbolic rank-two determinant formula in unknown input basis.
a,b,c,d=sp.symbols('a b c d')
K0=sp.Matrix([[a,0],[b,0]]);K1=sp.Matrix([[0,c],[0,d]])
C=K0*K1-K1*K0
assert sp.factor(sp.det(C)-b*c*(a*d-b*c))==0

# Pauli output randomizers: average over all 4^4 choices, a nonunital rank2 channel.
ks=gad(.63,0)[:2]
pvals=[]
for ps in itertools.product(PAULIS,repeat=4):
    ch=[[pa@k for k in ks] for pa in ps]
    pvals.append(score(nested(*ch))['p'])

# Representation-invariance check by a random unitary change of Kraus basis.
inv=[]
for _ in range(30):
    ks=random_channel(rng,4);q=random_unitary(rng,4)
    rot=[sum(q[a,i]*ks[i] for i in range(4)) for a in range(4)]
    inv.append(abs(score(nested(ks,ks,ks,ks))['p']-score(nested(rot,rot,rot,rot))['p']))

stats={
 'seed':910373,'Clifford_count':len(cliff),
 'rank2_measure_prepare_cases':len(rows),
 'max_random_output_wrapper_yield_error':max(abs(r['mean_p']-r['predicted']) for r in rows),
 'Luders_unknown_basis_cases':len(meas),'Luders_mean_p_range':[min(meas),max(meas)],
 'max_rank2_yield_formula_error':max(abs(r['p']-r['predicted']) for r in r2),
 'max_pure_fixed_state_channel_yield':max(fixed),
 'max_eight_flag_TP_residual':max(complete),
 'max_GAD_yield_formula_error':max(abs(r['p']-r['predicted']) for r in gadrows),
 'max_Kraus_representation_yield_difference':max(inv),
 'output_Pauli_randomization_cases':len(pvals),'output_Pauli_randomization_average_yield':float(np.mean(pvals)),
 'symbolic_traceless_anticommutator_identity':True,'symbolic_rank2_measure_prepare_determinant':True,
 'projective_random_wrapper_99_attempts':math.ceil(math.log(.01)/math.log(11/12)),
 'projective_random_wrapper_53_success':1-(11/12)**53,
 'depolarizer_99_attempts':math.ceil(math.log(.01)/math.log(61/64)),
 'depolarizer_96_success':1-(61/64)**96}
assert stats['max_random_output_wrapper_yield_error']<1e-12
assert max(complete)<1e-12
assert max(fixed)<1e-20
(OUT/'extensions.json').write_text(json.dumps({'statistics':stats,'GAD':gadrows,'readout_errors':flagrows,'random_measure_prepare':rows},indent=2))
print(json.dumps(stats,indent=2))
print('\nTHERMAL:',[r for r in gadrows if r['gamma']==.95])
print('\nFLAG ERRORS:',json.dumps(flagrows,indent=2))
