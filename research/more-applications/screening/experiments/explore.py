"""Reproducible channel-pair exploration; no ordinary-optimality claim from this scan."""
from core import *
import csv,json,os
from pathlib import Path
ROOT=Path(__file__).resolve().parent
rng=np.random.default_rng(5172026)
models=[]
def add(name,K,category,access):
    assert tp_error(K)<1e-9,(name,tp_error(K))
    models.append(dict(name=name,K=K,category=category,access=access,d=K[0].shape[0]))
H=(X+Z)/np.sqrt(2)
add('identity',[I2],'known-control','known unitary')
add('Rx_031',rotation([1,0,0],.31),'coherent-error','unknown physical rotation; unitary promise')
add('Rz_027',rotation([0,0,1],.27),'coherent-error','unknown physical rotation; unitary promise')
add('Hadamard',[H],'known-control','known unitary')
for name,axis in [('Z',[0,0,1]),('X',[1,0,0]),('tilted',[.3,.4,np.sqrt(.75)])]:
    add('projective_'+name,dephase_axis(axis),'unread-measurement','hidden labels; Lüders')
    add('weak_luders_'+name,weak_luders(axis,.6),'weak-measurement','outcome labels optionally readable; not projective')
for axis,v in [('Z',[0,0,1]),('X',[1,0,0])]:
    for p in [.01,.2]: add(f'phase_{axis}_{p}',dephase_axis(v,p),'Pauli-noise','known Pauli error basis, unknown rates')
for l in [.03,.6,1.]:add(f'depol_{l}',depolarize(2,l),'Pauli-noise','unknown strength; known Pauli basis')
add('biased_pauli',pauli_channel([.97,.001,.001,.028]),'biased-noise','unknown rates; known Pauli basis')
for g in [.03,.5]:
    add(f'damping_{g}',amplitude(g),'T1-noise','hidden jump labels')
    add(f'heating_{g}',amplitude(g,True),'thermal-noise','hidden jump labels')
add('thermal_02_01',thermal(.2,.1),'thermal-noise','hidden jump labels')
add('thermal_08_03',thermal(.8,.3),'thermal-noise','hidden jump labels')
for name,tau in [('0',np.diag([1,0])),('1',np.diag([0,1])),('mixed',np.diag([.8,.2]))]:
    add('reset_'+name,reset(tau),'active-reset','quantum output available; reset record optional')
add('Z_then_H',[H@p for p in [np.diag([1,0]),np.diag([0,1])]],'feedback-measurement','same POVM as Z; non-Lüders state update')
add('noisy_drive',compose(rotation([1,0,0],.3),dephase_axis([0,0,1],.05)),'noisy-native-gate','actual channel unknown; ideal drive known')
add('random_rotations',mix(rotation([1,0,0],.6),rotation([0,0,1],.4),.5),'nonPauli-random-unitary','private, non-replayable random trajectory')
# Three-level leakage/repump gadgets.
add('qutrit_identity',[np.eye(3,dtype=complex)],'leakage-control','known unitary')
for g in [.05,.5]: add(f'leak12_{g}',jump_channel(3,1,2,g),'leakage','qutrit quantum output; hidden jump')
for g in [.1,.8,1.]:add(f'repump21_{g}',jump_channel(3,2,1,g),'leakage-reduction','hidden jump')
add('leak02_01',jump_channel(3,0,2,.1),'leakage','hidden jump')
add('measure_leakage',pinching([np.diag([1,1,0]),np.diag([0,0,1])]),'leakage-detection','readable projective flag optionally available')
add('qutrit_dephase',pinching([np.diag([1,0,0]),np.diag([0,1,0]),np.diag([0,0,1])]),'three-level-readout','hidden/readable full outcome')
add('qutrit_reset',reset(np.diag([.7,.2,.1])),'thermal-reset','output accessible')
# Two-qubit physical layers.
for name,P in [('ZI',np.kron(Z,I2)),('IZ',np.kron(I2,Z)),('ZZ',np.kron(Z,Z)),('XX',np.kron(X,X)),('XI',np.kron(X,I2))]:
    add('twoq_'+name,[np.sqrt(.9)*np.eye(4),np.sqrt(.1)*P],'correlated-Pauli-noise','unknown rate; known Pauli basis')
add('local_ZZ',tensor_channels(dephase_axis([0,0,1],.1),dephase_axis([0,0,1],.1)),'product-local-noise','known support; unknown rates')
add('local_depol',tensor_channels(pauli_channel([.97,.01,.01,.01]),pauli_channel([.97,.01,.01,.01])),'product-local-noise','known local Pauli basis')
add('reset_ancilla',tensor_channels([I2],reset(np.diag([1,0]))),'syndrome-reset','data returned; ancilla reset')
# Bell basis pinching.
B=np.column_stack([(np.array([1,0,0,1])/np.sqrt(2)),(np.array([1,0,0,-1])/np.sqrt(2)),(np.array([0,1,1,0])/np.sqrt(2)),(np.array([0,1,-1,0])/np.sqrt(2))])
add('Bell_measurement',[np.outer(B[:,i],B[:,i]) for i in range(4)],'parity-readout','joint projective outcomes optionally readable')
add('ZZ_rotation',[expm(-.15j*np.kron(Z,Z))],'coherent-crosstalk','unitary promise')

# Compute all AA and unordered AB pairs of equal dimension.
rows=[]
for i,A in enumerate(models):
    for B in models[i:]:
        if A['d']!=B['d']: continue
        m=metrics(A['K'],B['K'])
        rows.append(dict(A=A['name'],B=B['name'],dimension=A['d'],category_A=A['category'],category_B=B['category'],**m))
with (ROOT/'channel_sweep.csv').open('w') as f:
    w=csv.DictWriter(f,fieldnames=list(rows[0])); w.writeheader();w.writerows(rows)
with (ROOT/'model_catalog.json').open('w') as f:
    json.dump([{k:v for k,v in x.items() if k!='K'} for x in models],f,indent=2)
summary={'seed':5172026,'model_count':len(models),'pair_count':len(rows),'dimensions':{str(d):sum(x['d']==d for x in models) for d in [2,3,4]},'max_TP_error':max(tp_error(m['K']) for m in models),'max_probability_sum_error':max(x['p_sum_error'] for x in rows),'nonzero_minus_branches':sum(x['p_minus']>1e-12 for x in rows),'input_dependent_minus_branches':sum(x['p_minus_max']-x['p_minus_min']>1e-9 for x in rows)}
# Universal ordinary Choi-commutator measurement identity.
checks=[]
for d in [2,3,4]:
    M,C=commutator_test(d)
    projerr=float(np.linalg.norm(M@M-M))
    maxerr=0.;maxqubit=0.
    for rep in range(30):
        A=random_channel(d,int(rng.integers(1,d*d+1)),rng)
        B=random_channel(d,int(rng.integers(1,d*d+1)),rng)
        p=metrics(A,B)['p_minus']
        q=float(np.trace(M@np.kron(choi(A),choi(B))).real)
        maxerr=max(maxerr,abs(q-2*p/d**2))
        if d==2:maxqubit=max(maxqubit,abs(p-qubit_quadratic_p(A,B)))
    checks.append(dict(d=d,random_pairs=30,projector_error=projerr,max_ordinary_probability_error=maxerr,max_qubit_gram_error=maxqubit,projector_rank=int(round(np.trace(M).real))))
summary['ordinary_commutator_checks']=checks
# Exact replacement-state visibility identity.
err=0
for d in [2,3,4]:
    for _ in range(10):
        T=rng.normal(size=(d,d))+1j*rng.normal(size=(d,d));T=T@T.conj().T;T/=np.trace(T)
        S=rng.normal(size=(d,d))+1j*rng.normal(size=(d,d));S=S@S.conj().T;S/=np.trace(S)
        err=max(err,abs(metrics(reset(T),reset(S))['v']-np.trace(T@S).real/d))
summary['max_replacement_overlap_identity_error']=err
# Physical single-qubit formulas.
summary['selected_rows']=[r for r in rows if (r['A'],r['B']) in [('projective_Z','projective_X'),('damping_0.03','damping_0.03'),('damping_0.5','damping_0.5'),('reset_0','reset_0'),('reset_0','reset_1'),('leak12_0.05','repump21_0.8'),('leak12_0.5','repump21_1.0'),('twoq_ZZ','twoq_XX'),('twoq_ZZ','twoq_XI')]]
(ROOT/'sweep_summary.json').write_text(json.dumps(summary,indent=2))
print(json.dumps(summary,indent=2))
