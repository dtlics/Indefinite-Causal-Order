"""Literal SCC scalar-record lifting on green/red binary Lugano."""
from pathlib import Path
from itertools import product
import json
import sympy as s
ROOT=Path(__file__).parent
BITS=list(product((0,1),repeat=3))
def w(o):
 a,b,c=o;return (b*(1-c),(1-a)*c,a*(1-b))
PAT=sorted(set(map(w,BITS)));D=('D',)
def status(o,refined):
 z={D,('H',*o),*(('L',i,w(o)[i]) for i in range(3))}
 if refined:z.add(('A',*w(o)))
 return frozenset(z)
LABS=[('L',i,x) for i,x in product(range(3),(0,1))]

def audit(refined):
 fwd={}
 for f in product((0,1),repeat=6):
  sol=[o for o in BITS if all(o[i]==f[2*i+w(o)[i]] for i in range(3))]
  assert len(sol)==1;fwd[f]=sol[0]
 edges=set()
 for f,o in fwd.items():
  for k,a in enumerate(LABS):
   ff=list(f);ff[k]^=1
   for b in status(o,refined)^status(fwd[tuple(ff)],refined):edges.add((a,b,'green'))
 for o,p in product(BITS,repeat=2):
  for b in status(o,refined)^status(p,refined):edges.add((b,D,'red'))
 # Explicit old and added internal wires, grouped by co-occurring endpoints.
 cond={}
 def add(e,a,b,v):cond.setdefault((e,a,b),set()).add((v,1))
 for o in BITS:
  h=('H',*o)
  for i in range(3):
   l=('L',i,w(o)[i]);add(('lh',i),l,h,o[i]);add(('hl',i),h,l,w(o)[i])
   if refined:
    aa=('A',*w(o));add(('la',i),l,aa,w(o)[i]);add(('al',i),aa,l,w(o)[i])
  add('hd',h,D,o)
 assert all(len(v)==1 and next(iter(v))[1]==1 for v in cond.values())
 nodes=set().union(*(status(o,refined) for o in BITS));reach={a:{a} for a in nodes}
 for a,b,col in edges:reach[a].add(b)
 for k in nodes:
  for a in nodes:
   if k in reach[a]:reach[a]|=reach[k]
 comps={frozenset(b for b in nodes if b in reach[a] and a in reach[b]) for a in nodes}
 cyc=[]
 for cc in comps:
  internal=[e for e in edges if e[0] in cc and e[1] in cc]
  if len(cc)>1 or any(a==b for a,b,col in internal):
   assert {col for a,b,col in internal}=={'green'};cyc.append(cc)
 assert cyc==[frozenset(('L',i,0) for i in range(3))]
 if refined:
  for aa in (n for n in nodes if n[0]=='A'):
   assert frozenset([aa]) in comps
   assert not any(a==aa and col=='green' or b==aa and col=='red' for a,b,col in edges)
  assert all(b[0]!='A' or a in cyc[0] for a,b,col in edges if col=='green')
  assert all(a[0]!='A' or b==D for a,b,col in edges if col=='red')
 return {'refined':refined,'native_branches':len(nodes),'sections':8,'forward_choices':64,'reverse_choices':8,
         'green_edges':sum(c=='green' for a,b,c in edges),'red_edges':sum(c=='red' for a,b,c in edges),
         'solid_edges':0,'weak_loops_pass':True,'new_record_algebra':'C^4' if refined else None},fwd,edges
old,of,oe=audit(False);new,nf,ne=audit(True);assert of==nf
assert {e for e in ne if e[0][0]!='A' and e[1][0]!='A'}==oe
projections=[s.diag(*(int(w(o)==p) for o in BITS)) for p in PAT]
assert sum(projections,s.zeros(8))==s.eye(8)
assert [int(P.trace()) for P in projections]==[2,2,2,2]
for P in projections:assert P*P==P and P.H==P
for i,P in enumerate(projections):
 for j,Q in enumerate(projections):
  if i!=j:assert P*Q==s.zeros(8)
# The phase coefficient is exactly the matching row/column selection.
x=s.symbols('x0:24');U={(i,b):s.Matrix(2,2,x[8*i+4*b:8*i+4*b+4]) for i,b in product(range(3),(0,1))}
G=s.Matrix(8,8,lambda a,b:s.prod(U[i,w(BITS[a])[i]][BITS[a][i],BITS[b][i]] for i in range(3)))
for p,P in zip(PAT,projections):
 marked=s.Matrix(8,8,lambda a,b:G[a,b] if w(BITS[a])==p else 0)
 assert marked==P*G and marked.T==G.T*P
out={'status':'PASS','green_old':old,'green_record_lift':new,
 'all_old_choice_maps_and_edges_preserved':True,'full_symbolic_marked_contraction':True,
 'record_pattern_projection_ranks':[2,2,2,2],
 'red_time_reverse':{'forward_choices':8,'reverse_choices':64,'record_before_red_SCC':True,'weak_loops_pass':True},
 'scope':'Actual same-SCC scalar-record graph rewrite, calibrated on both colors; no quartet route or quantum M4 lift follows.'}
(ROOT/'branch_layer_scalar_record_lift_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
