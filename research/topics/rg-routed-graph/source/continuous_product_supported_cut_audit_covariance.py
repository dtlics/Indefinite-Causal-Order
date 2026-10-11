"""Exact parameter covariance and moving-carrier checks for the K12 phase."""
from pathlib import Path
import json
import sympy as s
from exact_fixtures import E,I16,I2,X,Y,Z,WORDS,tensor,local,R
ROOT=Path(__file__).parent
zero=s.zeros(16)
Q=tensor([I2,I2,s.Matrix([[1,-1],[-1,1]])/2,s.diag(0,1)])
assert [s.trace(e*Q) for e in E]==[s.Rational(1,2),s.Integer(1),s.Integer(0),s.Integer(0)]
dynamics=[]
for i in [0,1]:
    A=R[i]*local(i,X)*R[i]
    delta=A.H*Q*A-Q
    dynamics.append({'before_query':i+1,'input_support_defect_rank':delta.rank(),
                     'input_support_defect_HS_squared':str(s.trace(delta.H*delta))})
assert [x['input_support_defect_HS_squared'] for x in dynamics]==['3','4']

us=[s.Matrix(2,2,s.symbols(f'q{i}_0:4')) for i in range(4)]
z=s.symbols('z',nonzero=True)
K=I16+(z-1)*Q;Ki=I16+(1/z-1)*Q
assert all(s.expand(x)==0 for x in K*Ki-I16)

def F(vs,es=E):
    return tensor(vs)+sum((tensor([I2 if k==i else vs[k] for k in range(4)])*
                           local(i,Z*vs[i]*Z-vs[i])*es[i] for i in range(4)),zero)
full=F(us);fl=F([us[0],us[1],I2,I2]);fr=F([I2,I2,us[2],us[3]])
new_E=[K*E[i]*Ki if i in [0,1] else E[i] for i in range(4)]
left=(full+(z-1)*fr*Q*fl)*Ki
right=F(us,new_E)
assert all(s.expand(z*x)==0 for x in left-right)
print('Full symbolic normalized phase covariance PASS.',flush=True)

Km=I16-2*Q
Em=[Km*e*Km for e in E]
expected_E1=tensor([I2,s.diag(1,0),s.diag(1,0),s.Matrix([[1,1],[1,1]])/2])
assert Em[0]==expected_E1
assert Em[2]==E[2] and Em[3]==E[3]
for i in range(4):
    assert Em[i]**2==Em[i] and Em[i].H==Em[i]
    assert all(Em[i]*local(i,p)==local(i,p)*Em[i] for p in [X,Y,Z])
assert all(Em[i]*Em[j]==zero for i in range(4) for j in range(i))
# New eta on factors 1,3,4: 2|0,1,1>+|1,-,->, norm squared 8.
eta_new=2*tensor([s.Matrix([1,0]),s.Matrix([0,1]),s.Matrix([0,1])])+tensor([s.Matrix([0,1]),s.Matrix([1,-1]),s.Matrix([1,-1])])
eta_matrix=eta_new*eta_new.H/8
inds=[k for k,w in enumerate(WORDS) if w[1]==0]
assert Em[1].extract(inds,inds)==eta_matrix
ranks=[]
for i in range(3):
    ww=list(__import__('itertools').product(range(2),repeat=3))
    ix0=[k for k,w in enumerate(ww) if w[i]==0]
    ix1=[k for k,w in enumerate(ww) if w[i]==1]
    ranks.append(s.Matrix([list(eta_new.extract(ix0,[0])),list(eta_new.extract(ix1,[0]))]).rank())
assert ranks==[2,2,2]
report={'status':'PASS','tr_Ei_Q':['1/2','1','0','0'],
        'moving_input_support_witnesses':dynamics,
        'phase_covariance':'[F+(z-1)F_R Q F_L] K_z^{-1} is the same normalized orthogonal-cylinder formula with E1,E2 conjugated by K_z and E3,E4 unchanged',
        'generic_complex_query_entries':16,'phase_parameter':'arbitrary nonzero complex z algebraically; unitary/projector interpretation when |z|=1',
        'phase_minus_one_E1_spectator':'|0,0,+> on factors 2,3,4',
        'phase_minus_one_E2_spectator_unnormalized':'2|0,1,1>+|1,-,-> on factors 1,3,4',
        'phase_minus_one_E2_local_Schmidt_ranks':ranks,
        'scope':'Exact process-tensor covariance only; no preservation of a routed realization is asserted'}
(ROOT/'continuous_product_supported_cut_audit_covariance_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
