"""Reproducible exploration of nested-switch conditional channels.
All probabilities are unnormalized: rejected histories are retained in costs.
No optimization over all ordinary circuits is claimed by this script.
"""
from __future__ import annotations
import itertools, json, math
from pathlib import Path
import numpy as np
from scipy.linalg import null_space

OUT=Path(__file__).resolve().parent
I=np.eye(2,dtype=complex)
X=np.array([[0,1],[1,0]],complex)
Y=np.array([[0,-1j],[1j,0]],complex)
Z=np.diag([1,-1]).astype(complex)
PAULIS=[I,X,Y,Z]

def random_channel(rng,rank,d=2):
    z=rng.normal(size=(d*rank,d))+1j*rng.normal(size=(d*rank,d))
    q,r=np.linalg.qr(z)
    q=q@np.diag(np.diag(r)/np.abs(np.diag(r)))
    return [q[i*d:(i+1)*d] for i in range(rank)]

def random_unitary(rng,d=2):
    return random_channel(rng,1,d)[0]

def branch(a,b,sign):
    return [(bj@ai+sign*ai@bj)/2 for ai in a for bj in b]

def nested(a,b,c,d,flags=(-1,-1,1)):
    return branch(branch(a,b,flags[0]), branch(c,d,flags[1]),flags[2])

def choi(ks):
    dim=ks[0].shape[1]
    return sum(np.outer(k.reshape(-1,order='F'),k.reshape(-1,order='F').conj())/dim for k in ks)

def score(ks):
    d=ks[0].shape[0]; J=choi(ks)
    p=float(np.trace(J).real)
    phi=np.eye(d).reshape(-1,order='F')/np.sqrt(d)
    f=float((phi.conj()@J@phi).real)
    purity=float(np.trace(J@J).real)/p**2 if p>1e-28 else 0.
    resid=max(float(np.linalg.norm(k-np.trace(k)*np.eye(d)/d)) for k in ks)
    effect=sum(k.conj().T@k for k in ks)
    inpdep=float(np.linalg.norm(effect-p*np.eye(d)))
    return {'p':p,'F_identity':f/p if p>1e-28 else None,'choi_purity':purity,
            'scalar_kraus_residual':resid,'input_probability_residual':inpdep}

def apply(ks,rho):
    return sum(k@rho@k.conj().T for k in ks)

def pure_fixed_residual(ks):
    """Minimize fixed pure-state displacement via exact candidate Bloch fixed space.
    Returns min_{fixed Bloch vectors} distance to unit sphere, or None if routine
    encounters numerical issues. Existence of pure fixed states is proved analytically.
    """
    T=np.array([[np.trace(p@apply(ks,q)).real/2 for q in PAULIS] for p in PAULIS])
    A=np.eye(3)-T[1:,1:]; b=T[1:,0]
    r=np.linalg.lstsq(A,b,rcond=1e-10)[0]
    ns=null_space(A,rcond=1e-10)
    if np.linalg.norm(A@r-b)>1e-7:return None
    if ns.shape[1]:return 0. if np.linalg.norm(r)<=1+1e-7 else abs(np.linalg.norm(r)-1)
    return float(abs(np.linalg.norm(r)-1))

def gad(gamma,excited):
    # excited = stationary excited-state population; ground weight=1-excited
    e=excited; g=gamma; s=math.sqrt(1-g)
    return [math.sqrt(1-e)*np.diag([1,s]),
            math.sqrt((1-e)*g)*np.array([[0,1],[0,0.]],complex),
            math.sqrt(e)*np.diag([s,1]),
            math.sqrt(e*g)*np.array([[0,0],[1,0.]],complex)]

def replacement(rho):
    vals,vec=np.linalg.eigh(rho)
    return [math.sqrt(max(0.,val))*np.outer(vec[:,i],I[:,j])
            for i,val in enumerate(vals) for j in range(2)]

def pauli(p): return [math.sqrt(x)*s for x,s in zip(p,PAULIS)]

def commutator_yield(ks):
    C=[a@b-b@a for a in ks for b in ks]
    return sum(abs(np.trace(a@b))**2 for a in C for b in C)/64

def twirl(ks,output_only=False):
    if output_only:return [p@k/2 for p in PAULIS for k in ks]
    return [p@k@p/2 for p in PAULIS for k in ks]

def main():
    rng=np.random.default_rng(487902)
    rows=[]
    for rank in [2,3,4]:
        for t in range(300):
            ks=random_channel(rng,rank)
            data=score(nested(ks,ks,ks,ks))
            data.update({'family':'random_CPTP','rank':rank,'index':t,
                         'pure_fixed_residual':pure_fixed_residual(ks),
                         'formula_error':abs(data['p']-commutator_yield(ks))})
            rows.append(data)
    # Four independently sampled, unrelated and nonunital channels.
    hetero=[]
    for t in range(100):
        ch=[random_channel(rng,int(rng.integers(2,5))) for _ in range(4)]
        hetero.append(score(nested(*ch)))
    models=[]
    for g in [0.001,0.01,0.1,0.5,0.9,1.0]:
      for e in [0.,0.001,0.01,0.1,0.25,0.5]:
        ks=gad(g,e); s=score(nested(ks,ks,ks,ks)); s.update({'family':'GAD','gamma':g,'excited':e})
        models.append(s)
    for r in [0.,0.2,0.6,0.9,0.99,1.]:
        ks=replacement((I+r*Z)/2); s=score(nested(ks,ks,ks,ks)); s.update({'family':'replacement','bloch_radius':r})
        models.append(s)
    for p in [[.25]*4,[0,.5,.5,0],[.5,0,0,.5],[0,1,0,0],[1,0,0,0]]:
        ks=pauli(p);s=score(nested(ks,ks,ks,ks));s.update({'family':'Pauli','weights':p})
        models.append(s)
    # Algebra outside qubits: should not return a scalar Kraus family generically.
    qutrit=[]
    for t in range(20):
        ks=random_channel(rng,3,d=3);qutrit.append(score(nested(ks,ks,ks,ks)))
    stats={
      'random_self_trials':len(rows),'heterogeneous_trials':len(hetero),
      'max_scalar_residual':max(r['scalar_kraus_residual'] for r in rows+hetero),
      'max_probability_input_dependence':max(r['input_probability_residual'] for r in rows+hetero),
      'max_yield_formula_error':max(r['formula_error'] for r in rows),
      'random_identity_F_range':[min(r['F_identity'] for r in rows),max(r['F_identity'] for r in rows)],
      'yield_quantiles':np.quantile([r['p'] for r in rows],[0,.1,.5,.9,1]).tolist(),
      'rank_yield_quantiles':{str(k):np.quantile([r['p'] for r in rows if r['rank']==k],[0,.1,.5,.9,1]).tolist() for k in [2,3,4]},
      'min_stationary_state_distance_to_pure_in_random_draws':min(r['pure_fixed_residual'] for r in rows),
      'qutrit_identity_fidelity_range':[min(r['F_identity'] for r in qutrit),max(r['F_identity'] for r in qutrit)]
    }
    (OUT/'scan.json').write_text(json.dumps({'seed':487902,'statistics':stats,'models':models,'random_self':rows,'heterogeneous':hetero,'qutrit':qutrit},indent=2))
    print(json.dumps(stats,indent=2))
    print('\nGAD gamma=1:',[(r['excited'],r['p']) for r in models if r['family']=='GAD' and r['gamma']==1])
    print('Replacement:',[(r['bloch_radius'],r['p']) for r in models if r['family']=='replacement'])

if __name__=='__main__':main()
