"""Exact scalar phase concentration data for the four C^7 contexts."""
from pathlib import Path
import json
import sympy as s
from exact_fixtures import E,WORDS,I16
ROOT=Path(__file__).parent
source=json.loads((ROOT/'auxiliary_four_sector_input_flags_checks.json').read_text())
parts=source['maximal_complete_diagonal_partitions']
past=parts[1]
P=[s.diag(*[int(n in atom) for n in range(16)]) for atom in past]
assert all(q*e==e*q for q in P for e in E)
bits=[s.Matrix([w[i] for w in WORDS]) for i in [0,2,3]]
base=s.Matrix.hstack(*[s.Matrix([q[n,n] for n in range(16)]) for q in P],*bits)
assert base.rank()==10
reports=[]
for no,atoms in enumerate(parts,1):
    masks=s.Matrix.hstack(*[s.Matrix([int(n in atom) for n in range(16)]) for atom in atoms])
    coeff=base.gauss_jordan_solve(masks)[0]
    assert all(x.is_Integer for x in coeff)
    assert base*coeff==masks
    used=[i for i,row in zip([1,3,4],range(7,10)) if any(coeff[row,k] for k in range(7))]
    # The Laurent exponent identity holds pointwise for all independent
    # scalar phases. This proves the full original-query coefficient formula.
    for n,w in enumerate(WORDS):
        b=next(k for k,atom in enumerate(past) if n in atom)
        for k in range(7):
            exponent=coeff[b,k]+sum(w[i-1]*coeff[row,k] for i,row in zip([1,3,4],range(7,10)))
            assert exponent==int(n in atoms[k])
    reports.append({'context':no,'atoms':atoms,'query_input_phase_ports':used,
                    'past_phase_exponents':[[int(x) for x in row] for row in coeff[:7,:].tolist()],
                    'input_phase_exponents_query1_query3_query4':[[int(x) for x in row] for row in coeff[7:,:].tolist()],
                    'coefficientwise_scalar_Laurent_factorization':True})
    print('Context',no,'requires query-input phases at',used,flush=True)
report={'status':'PASS','past_context':past,
        'past_context_commutes_with_every_Ei':True,
        'complete_diagonal_Hermitian_dimension':10,
        'past_diagonal_dimension':7,'remaining_physical_input_ports':[1,3,4],
        'contexts':reports,
        'formula':'For scalar z, G_context(z,U)=F(U1 A1(z),U2,U3 A3(z),U4 A4(z)) B(z), where B is a fixed-past diagonal phase and Ai=diag(1,monomial(z)).',
        'scope':'Exact scalar phase factorization; repeated and inverse appearances of the same z do not define a native single-use C^7 realization and cannot be extended by assuming private ancillary matrices commute.'}
(ROOT/'seven_context_synthesis_reduction_checks.json').write_text(json.dumps(report,indent=2)+'\n')
