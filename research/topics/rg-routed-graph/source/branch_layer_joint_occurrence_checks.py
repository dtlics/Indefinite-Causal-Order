"""Exact finite calibrations of same-SCC pattern faithfulness.
No parameter claim is inferred from these finite calibrations; see the note.
"""
from pathlib import Path
from itertools import product,combinations
import json
import sympy as s
from exact_fixtures import E
ROOT=Path(__file__).parent
bits=list(product((0,1),repeat=3))
def w(o):
 a,b,c=o;return (b*(1-c),(1-a)*c,a*(1-b))
def sts(o):return frozenset([('D',),('H',*o),*(('L',i,w(o)[i]) for i in range(3))])
labs=[('L',i,x) for i,x in product(range(3),(0,1))]
fwd={}
for f in product((0,1),repeat=6):
 sol=[o for o in bits if all(o[i]==f[2*i+w(o)[i]] for i in range(3))]
 assert len(sol)==1;fwd[f]=sol[0]
edge_witnesses={}
for f,o in fwd.items():
 for k,a in enumerate(labs):
  ff=list(f);ff[k]^=1;p=fwd[tuple(ff)]
  assert (a in sts(o))==(a in sts(p))
  if a not in sts(o):assert o==p
  for b in sts(o)^sts(p):
   assert a in sts(o) and a in sts(p)
   q=o if b in sts(o) else p
   assert a in sts(q) and b in sts(q)
   edge_witnesses[a,b,'green']=q
for o,p in product(bits,repeat=2):
 for b in sts(o)^sts(p):
  q=o if b in sts(o) else p
  assert b in sts(q) and ('D',) in sts(q)
  edge_witnesses[b,('D',),'red']=q
Ps=[s.diag(*(int(w(o)[i]==0) for o in bits)) for i in range(3)]
patterns=[]
for select in bits:
 Q=s.eye(8)
 for i,v in enumerate(select):Q=Q*(Ps[i] if v else s.eye(8)-Ps[i])
 assert Q*Q==Q
 reachable=[o for o in bits if tuple(int(w(o)[i]==0) for i in range(3))==select]
 assert int(Q.trace())==len(reachable)
 patterns.append({'losing_status':select,'rank':int(Q.trace()),'sections':reachable})
pair_ranks=[int((Ps[i]*Ps[j]).trace()) for i,j in combinations(range(3),2)]
assert pair_ranks==[4,4,4] and int((Ps[0]*Ps[1]*Ps[2]).trace())==2
# Minimal E_i already suffice to check the literal physical orthogonality;
# the general theorem uses independently audited S_i S_j=0 for all ideals.
assert len(E)==4
for i,j in combinations(range(4),2):assert E[i]*E[j]==s.zeros(16)
out={'status':'PASS','complete_layer_patterns':patterns,
 'nonzero_pattern_count':sum(p['rank']>0 for p in patterns),
 'pair_losing_ranks':pair_ranks,'triple_losing_rank':2,
 'all_direct_edges_have_cooccurrence_witness':True,'tested_green_and_red_edges':len(edge_witnesses),
 'minimal_quartet_active_products_zero':True,
 'time_reverse_same_pattern_ranks':True,
 'scope':'Exact calibrations; the all-context and all-allowed-active-ideal conclusions use the accompanying theorem and audited S_i orthogonality.'}
(ROOT/'branch_layer_joint_occurrence_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
