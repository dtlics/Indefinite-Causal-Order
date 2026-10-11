"""Exact first-carrier classification on both entire phase circles."""
from pathlib import Path
import json
import numpy as np
import sympy as s
from exact_fixtures import E
from phase_endpoint_circle import grams_for, laurent_table, specialize, symmetric_laurent_to_real, z, t
ROOT=Path(__file__).parent
origin=json.loads((ROOT/'phase_endpoint_exact_checks.json').read_text())['results'][0]['ports']
Ss=[s.Matrix([[s.sympify(x) for x in row] for row in p['first']['projector']]) for p in origin]
results=[]
for r,inds in [(4,[0,2,8,9]),(5,[0,4,6,8,12])]:
    for i in range(4):
        S=E[0] if r==4 and i==0 else Ss[i]
        q=np.array((12*S).tolist(),dtype=np.int64)
        assert s.Matrix(q.tolist()) == 12*S
        assert np.max(np.abs(q)) <= 12
        bit=np.array([int(a in inds) for a in range(16)],dtype=np.int64)
        exponent=bit[:,None]-bit[None,:]
        Q={e:q*(exponent==e) for e in [-1,0,1]}
        gram=grams_for(r,i,'first')
        # Verify G(z)Q(z)=0 coefficientwise, with a safe a priori int64 bound.
        gram_bound=256*25*16*784**2
        assert 3*16*12*gram_bound < 2**63
        prod={e:np.zeros((16,16),dtype=np.int64) for e in range(-5,6)}
        for e,g in gram.items():
            for f,v in Q.items(): prod[e+f] += g@v
        assert all(not np.any(m) for m in prod.values())
        # Verify exact reduction by all actual normalized single matrix units.
        coeff=laurent_table(r)
        A={e:specialize(c,[i]) for e,c in coeff.items()}
        for k in range(4):
            cm={e:np.zeros((16,16),dtype=np.int64) for e in range(-2,3)}
            for e,units in A.items():
                for f,v in Q.items(): cm[e+f] += units[(k,)]@v-v@units[(k,)]
            assert all(not np.any(m) for m in cm.values())
        G=sum((s.Matrix(g.tolist())*z**e for e,g in gram.items()),s.zeros(16))
        pivots=G.subs(z,-1).rref()[1]
        assert len(pivots) == 16-S.rank()
        det=s.factor(G.extract(pivots,pivots).det(method='domain-ge'))
        realdet=symmetric_laurent_to_real(det)
        P=s.Poly(realdet,t)
        at_identity_power=0
        while P.eval(2)==0:
            P=P.exquo(s.Poly(t-2,t));at_identity_power+=1
        assert at_identity_power == (2 if r==4 and i==0 else 0)
        roots=int(P.count_roots(-2,2)) if P.degree()>0 else 0
        assert roots==0 and P.eval(-2)>0 and P.eval(2)>0
        rec={'phase_projector_rank':r,'query':i+1,
             'first_rank_for_z_not_1':S.rank(),
             'first_rank_at_z_1':int(s.trace(Ss[i])),
             'carrier_for_z_not_1':'K_z '+('E1' if r==4 and i==0 else 'S'+str(i+1))+' K_z^*',
             'Gram_times_carrier_all_Laurent_coefficients_zero':True,
             'actual_single_commutator_all_Laurent_coefficients_zero':True,
             'nonsingular_principal_minor_indices':list(pivots),
             'principal_minor_size':len(pivots),
             'principal_minor_determinant':str(det),
             'principal_minor_determinant_in_t':str(realdet),
             'power_of_t_minus_2':at_identity_power,
             'remaining_factor_exact_root_count_on_minus2_plus2':roots,
             'remaining_factor_value_at_minus2':str(P.eval(-2)),
             'remaining_factor_value_at_plus2':str(P.eval(2))}
        results.append(rec)
        print('rank',r,'query',i+1,'first support',S.rank(),
              'identity support',int(s.trace(Ss[i])),'PASS',flush=True)
        (ROOT/'phase_endpoint_circle_first_checks.json').write_text(json.dumps({
            'status':'PASS' if len(results)==8 else 'RUNNING','results':results,
            'conclusion':'For C4 all nontrivial phases have first ranks (2,4,2,2); C5 has first ranks (4,4,2,2) for every phase.',
            'proof':'Exact coefficientwise reducing lower carriers and principal-minor upper bounds; Sturm root exclusion.'},indent=2)+'\n')
print('PASS: complete first-carrier phase-circle classification.',flush=True)
