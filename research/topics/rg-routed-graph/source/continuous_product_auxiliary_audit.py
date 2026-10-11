"""Independent row-tensor reconstruction of the full-boundary cut witnesses."""
from pathlib import Path
from itertools import combinations
import json
import sympy as s
from exact_fixtures import E, I2, I16, X, Y, Z, WORDS, tensor
ROOT = Path(__file__).parent
zero=s.zeros(16)
Vs=[I16-2*sum((o[i]*E[i] for i in range(4)),zero) for o in WORDS]
D0=s.Matrix.vstack(*[Vs[k][k,:] for k in range(16)])
assert D0*D0==I16 and D0==D0.H

def F(us):
    W=tensor(us)
    raw=s.Matrix.vstack(*[(W[k,:]*Vs[k]) for k in range(16)])
    return raw*D0

P={'X':X,'Y':Y,'Z':Z}
def single(i,u):
    us=[I2]*4;us[i]=u
    return F(us)

checks=[]
source=json.loads((ROOT/'auxiliary_full_boundary_checks.json').read_text())
assert len(source)==12
for row in source:
    i,j=row['before']-1,row['after']-1
    a,b=P[row['before_query']],P[row['after_query']]
    us=[I2]*4;us[i]=a;us[j]=b
    defect=F(us)-single(j,b)*single(i,a)
    hs=s.simplify(s.trace(defect.H*defect))
    assert hs>0 and hs==s.sympify(row['defect_HS_squared'])
    r,c,value=row['nonzero_entry']
    assert defect[r,c]==s.sympify(value)
    checks.append({'before':i+1,'after':j+1,'defect_HS_squared':str(hs)})
assert len({(r['before'],r['after']) for r in checks})==12
cuts=[]
for size in [1,2,3]:
    for before in combinations(range(1,5),size):
        after=tuple(i for i in range(1,5) if i not in before)
        witness=next(r for r in checks if r['before'] in before and r['after'] in after)
        cuts.append({'before':before,'after':after,'excluded_by':witness})
assert len(cuts)==14
out={'status':'PASS','row_tensor_reconstruction':'Independent of the original checker formula and R_i construction',
     'ordered_pair_witnesses_verified':checks,'all_fourteen_nontrivial_ordered_cuts_excluded':cuts,
     'theorem_audit':'PASS under the stated complete bipartite unitary-process theorem; no larger slot, graph deletion, or proper-support branch inference is made'}
(ROOT/'continuous_product_auxiliary_audit_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
