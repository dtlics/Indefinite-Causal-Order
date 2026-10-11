from itertools import product,combinations
from pathlib import Path
import json
import sympy as s
from exact_fixtures import E,I16,WORDS,local,tensor
v={'0':s.Matrix([1,0]),'1':s.Matrix([0,1]),'+':s.Matrix([1,1]),'-':s.Matrix([1,-1])}
def vec(t):return tensor([v[x] for x in t])
d=json.loads(Path(__file__).with_name('safe_pauli_orbit_table.json').read_text());safe=d['safe_rays'];rays={w:vec(w) for w in safe}
Vs={o:I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16)) for o in WORDS};D0=I16-2*sum((local(i,s.diag(0,1))*E[i] for i in range(4)),s.zeros(16))
allowed={}
for i in [2,3]:
 for name,K in [('zero',s.zeros(16)),('active',E[i]),('passive',I16-E[i]),('identity',I16)]:
  aa=[]
  for w in safe:
   target=K*D0*rays[w]
   okay=True
   for oi,o in enumerate(WORDS):
    state=Vs[o]*rays[w];ray=d['table'][w][oi]
    c=state[oi] if ray[i] in '+-' else 0
    if c!=target[oi]:okay=False;break
   if okay:aa.append(w)
  allowed[i,name]=set(aa)
rows=[]
for a,b in product(['zero','active','passive','identity'],repeat=2):
 compatible=sorted(allowed[2,a]&allowed[3,b]);rank=s.Matrix.hstack(*[rays[w] for w in compatible]).rank() if compatible else 0
 rows.append({'query3_marker':a,'query4_marker':b,'compatible_ray_count':len(compatible),'compatible_span_rank':rank,'compatible_rays':compatible})
report={'safe_ray_count':len(safe),'per_marker_compatible_ray_counts':{str(k):len(v) for k,v in allowed.items()},'per_marker_span_ranks':{str(k):s.Matrix.hstack(*[rays[w] for w in sorted(v)]).rank() if v else 0 for k,v in allowed.items()},'simultaneous_marker_cases':rows,'full_span_possible':any(r['compatible_span_rank']==16 for r in rows)}
print(json.dumps(report,indent=2));Path(__file__).with_name('safe_pauli_allowed_markers_checks.json').write_text(json.dumps(report,indent=2)+'\n')
