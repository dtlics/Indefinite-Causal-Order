"""Test natural conditional-output-qubit promotion of C4 at complete tangent level."""
import json,numpy as np,sympy as s
from exact_fixtures import I16,E,local,Z,WORDS
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16));T=[]
for o in WORDS:
 v=I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16));T.append(np.array(4*v*D0,dtype=np.int64))
T=np.array(T);P=[int((n[0]==0 and n[3]==0) or(n[0]==1 and n[2]==0)) for n in WORDS];p=1000003
out=[]
for mask,kind,label in [(0,'real','active identity'),(4,'real','active X'),(4,'imag','active Y/i')]:
 v=[]
 for r in range(16):
  for n in range(16):
   for q in range(16):v.append(int(T[r,n,q])*P[n]*(1 if kind=='real' or WORDS[r][1]==0 else -1))
 rows={int(k):{int(j):x for j,x in row.items()} for k,row in json.load(open(f'auxiliary_tangent_echelon_{mask}_{kind}.json')).items()}
 defects=[(k,sum(x*v[j] for j,x in row.items())%p) for k,row in rows.items()];bad=[x for x in defects if x[1]]
 out.append({'candidate':label,'xor_mask':mask,'mode':kind,'nonzero_retained_modular_constraints':len(bad),'first_defect':bad[0] if bad else None})
print(json.dumps(out,indent=2));json.dump(out,open('auxiliary_new_active_qubit_probe_checks.json','w'),indent=2)
