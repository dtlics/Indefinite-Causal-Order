"""Exact36 aggregate carrier patterns; uniform support identities for F=BA."""
from pathlib import Path
from itertools import product
import json
import sympy as s
from exact_fixtures import E,R,I16,WORDS,local
ROOT=Path(__file__).parent
O=s.zeros(16)
def cylinder(i,vecs):
 others=[j for j in range(4) if j!=i]
 cols=[]
 for bit in (0,1):
  for v in vecs:
   cols.append(s.Matrix([v[sum(w[j]<<(2-k) for k,j in enumerate(others))] if w[i]==bit else 0 for w in WORDS]))
 B=s.Matrix.hstack(*cols)
 return B*(B.H*B).inv()*B.H
S=[cylinder(0,[[1,0,1,0,0,0,0,0],[1,0,0,1,0,0,0,0]]),
 cylinder(1,[[0,1,0,0,0,0,0,0],[0,0,0,0,1,1,-1,-1]]),E[2],E[3]]
units=[]
for a,b in product(range(2),repeat=2):
 x=s.zeros(2);x[a,b]=1;units.append(x)
def options(i):
 return [('E','0',E[i],O),('E','E',E[i],E[i]),
 ('S','0',S[i],O),('S','E',S[i],E[i]),
 ('S','S-E',S[i],S[i]-E[i]),('S','S',S[i],S[i])]
out=[];checks=0
for p,q in product(options(0),options(1)):
 Q=[p[2],q[2],E[2],E[3]];T=[p[3],q[3],E[2],E[3]]
 C=[a-b for a,b in zip(Q,T)];res=I16-sum(Q,O)
 assert res*res==res and res.H==res
 for i in range(4):
  assert Q[i]*Q[i]==Q[i] and T[i]*T[i]==T[i] and C[i]*C[i]==C[i]
  assert T[i]*C[i]==O and T[i]+C[i]==Q[i]
  assert Q[i]*E[i]==E[i]
  for x in units:
   a=R[i]*local(i,x)*R[i]
   assert T[i]*a==a*T[i] and C[i]*a==a*C[i]
   assert res*a*T[i]==O
   for j in range(4):
    if i!=j: assert Q[j]*a*T[i]==O
   checks+=1
  for j in range(4):
   if i!=j: assert Q[i]*Q[j]==O
 out.append({'Q1':p[0],'T1':p[1],'Q2':q[0],'T2':q[1],
  'upstream_rank':int(sum(t.trace() for t in T)),
  'core_active_rank':int(sum(c.trace() for c in C)),
  'all_passive_rank':int(res.trace())})
assert len(out)==36
data={'status':'PASS','aggregate_patterns':out,'matrix_unit_support_checks':checks,
 'scope':'Exact support certificate for the uniform parameter identity in bounded_layer_tensor_normal_form_candidate.md; not a routed realization.'}
(ROOT/'aggregate_core_carrier_checks.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({'status':'PASS','aggregate_patterns':len(out),'matrix_unit_support_checks':checks},indent=2))
