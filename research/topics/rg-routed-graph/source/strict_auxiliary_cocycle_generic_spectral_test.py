"""Exact rational-quaternion witnesses beyond the real-Pauli cocycle scout."""
from pathlib import Path
import json,itertools,time
import sympy as s
from exact_fixtures import E,I2,I16,X,Y,Z,tensor
ROOT=Path(__file__).parent;J=X*Z
def F(us):
    W=tensor(us)
    return (W+sum((tensor([Z*us[j]*Z-us[j] if j==i else us[j] for j in range(4)])*E[i] for i in range(4)),s.zeros(16))).applyfunc(s.expand)
qs=[(1,2,2,4),(2,1,4,2),(2,4,1,2),(4,2,2,1),(3,4,0,0),(3,0,4,0),(3,0,0,4)]
gates=[(a*I2+s.I*b*X+c*J+s.I*d*Z)/5 for a,b,c,d in qs]
assert all((u.H*u).applyfunc(s.simplify)==I2 for u in gates)
remaining=[r for r in json.loads((ROOT/'strict_auxiliary_cocycle_spectral_test_checks.json').read_text())['results'] if r['witness'] is None]
choices=[(0,1,2,3),(1,2,3,0),(4,5,6,0),(0,0,0,0),(2,3,1,0)]
x=s.Symbol('x');out=[];start=time.time()
for rec in remaining:
    left=[i-1 for i in rec['before_queries']];witness=None;tests=[]
    for choice in choices:
        us=[gates[j] for j in choice];FL=F([u if i in left else I2 for i,u in enumerate(us)]);FR=F([I2 if i in left else u for i,u in enumerate(us)]);C=(FR.H*F(us)*FL.H).applyfunc(s.expand)
        # Clear a real positive denominator without altering multiplicities.
        den=s.ilcm(*[s.denom(v) for a in C for v in a.as_real_imag()]);A=C*den
        cp=A.charpoly(x).as_expr();sqf=s.Poly(cp,x,extension=s.I).sqf_list()[1]
        multiplicities=[int(e) for f,e in sqf];tests.append({'quaternion_indices':list(choice),'scale':str(den),'multiplicities':multiplicities,'factor_degrees':[f.degree() for f,e in sqf]})
        print('before',rec['before_queries'],'test',choice,'multip',multiplicities,'seconds',time.time()-start,flush=True)
        if any(e%2 for e in multiplicities):
            witness={'quaternion_indices':list(choice),'scale':str(den),'squarefree_factors':[{'coefficients':[str(v) for v in f.all_coeffs()],'multiplicity':int(e)} for f,e in sqf]};break
    out.append({'before_queries':rec['before_queries'],'tests':tests,'odd_multiplicity_witness':witness})
(ROOT/'strict_auxiliary_cocycle_generic_spectral_test_checks.json').write_text(json.dumps({'status':'EXACT_RATIONAL_SPECTRAL_TEST','quaternions':qs,'results':out,'scope':'Odd multiplicity excludes every nontrivial unital full-matrix auxiliary obeying this strict partition. No claim if absent.'},indent=2)+'\n')
