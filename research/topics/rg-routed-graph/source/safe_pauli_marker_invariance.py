from itertools import product
from pathlib import Path
import json
import sympy as s
from exact_fixtures import E,I16,WORDS,local,tensor
v={'0':s.Matrix([1,0]),'1':s.Matrix([0,1]),'+':s.Matrix([1,1]),'-':s.Matrix([1,-1])}
def word(t):return tensor([v[x] for x in t])
def key(a):
 z=next(x for x in a if x!=0);return tuple(x/z for x in a)
labels=list(product('01+-',repeat=4));rays={t:word(t) for t in labels};lookup={key(a):t for t,a in rays.items()}
Vs={o:I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16)) for o in WORDS}
D0=I16-2*sum((local(i,s.diag(0,1))*E[i] for i in range(4)),s.zeros(16))
safe=[];table={};bad=[]
for t in labels:
 outputs={};ok=True
 for o,V in Vs.items():
  a=V*rays[t];k=key(a)
  if k not in lookup:ok=False;break
  outputs[o]=(a,lookup[k])
 if ok:safe.append(t);table[t]=outputs
basis=[tuple(t) for t in ['001-','10+0','0001','11-+','0100','0110','11+0','11+1','0000','001+','0101','0111','10+1','10-+','10--','11--']]
B=s.Matrix.hstack(*[rays[t]/s.sqrt((rays[t].T*rays[t])[0]) for t in basis]);G=D0*B
Ks={}
for i in [2,3]:
 C=s.Matrix(16,16,lambda oi,p:table[basis[p]][WORDS[oi]][0][oi]/s.sqrt((rays[basis[p]].T*rays[basis[p]])[0]) if table[basis[p]][WORDS[oi]][1][i] in '+-' else 0)
 K=(C*G.H).applyfunc(s.simplify);Ks[i]=K
 assert K==K.H and K*K==K
viol={i:[] for i in Ks}
for t in safe:
 for i,K in Ks.items():
  target=K*D0*rays[t]
  for oi,o in enumerate(WORDS):
   vv,ray=table[t][o];lhs=vv[oi] if ray[i] in '+-' else 0
   if s.expand(lhs-target[oi])!=0:viol[i].append({'ray':''.join(t),'output':o,'lhs':str(lhs),'rhs':str(target[oi])})
report={'safe_ray_count':len(safe),'safe_rays':[''.join(t) for t in safe],'safe_span_rank':s.Matrix.hstack(*[rays[t] for t in safe]).rank(),'marker_tests':[{ 'query':i+1,'baseline_rank':Ks[i].rank(),'mismatch_count':len(viol[i]),'first_mismatches':viol[i][:5]} for i in Ks]}
Path(__file__).with_name('safe_pauli_marker_invariance_checks.json').write_text(json.dumps(report,indent=2)+'\n')
Path(__file__).with_name('safe_pauli_orbit_table.json').write_text(json.dumps({'safe_rays':[''.join(t) for t in safe],'table':{''.join(t):[''.join(table[t][o][1]) for o in WORDS] for t in safe}},indent=2)+'\n')
print(json.dumps(report,indent=2))
