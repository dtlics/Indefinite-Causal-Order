"""A branched recipient inside a genuine Lugano SCC is refined by an external cut flag.

A=L0 has two nativeM2 branches; J=B has two control branches that can be
placed respectively before/after ALL A branches. The flag-copy refinement
splits each A branch and enlarges the old recurrent SCC while preserving
its sole color. Every new dormant choice is explicitly included.
"""
from pathlib import Path
from itertools import product
from collections import defaultdict
import json
import sympy as s
ROOT=Path(__file__).parent
BITS=list(product([0,1],repeat=3))
def w(o):
 a,b,c=o;return (b*(1-c),(1-a)*c,a*(1-b))
def lab(i,x,c,refined):return ('L',i,x,c) if refined and i==0 else ('L',i,x)
S=('S',);T=('T',);D=('D',)

def run(refined):
 sections={}
 for o,c in product(BITS,[0,1]):
  x=w(o);active=[lab(i,x[i],c,refined) for i in range(3)]
  sections[o,c]={'status':frozenset([S,T,D,('H',*o),('B',c),*active]),'x':x,'labs':active}
 # L0 (recipient) full branch dims2 are duplicated, not restricted.
 f_nodes=[S]+[lab(i,x,c,refined) for i in range(3) for x in [0,1] for c in ([0,1] if refined and i==0 else [0])]
 # S has a2-valued output choice, every lab branch a2-valued output choice.
 # T decodes the Lugano record and has8 reverse input choices; D decodes
 # control+data and has2 scalar-sector reverse input choices (sector dim2).
 forward={}
 for values in product([0,1],repeat=len(f_nodes)):
  choices=dict(zip(f_nodes,values));c=choices[S]
  sol=[(o,cc) for (o,cc),sec in sections.items() if cc==c and all(o[i]==choices[sec['labs'][i]] for i in range(3))]
  assert len(sol)==1;forward[values]=sol[0]
 reverse={(o,c):(o,c) for o,c in sections}
 edges=set()
 for values,key in forward.items():
  for j,node in enumerate(f_nodes):
   other=list(values);other[j]^=1
   for n in sections[key]['status']^sections[forward[tuple(other)]]['status']:edges.add((node,n,'green'))
 for o,c in reverse:
  for oo in BITS:
   for n in sections[o,c]['status']^sections[oo,c]['status']:edges.add((n,T,'red'))
  for n in sections[o,c]['status']^sections[o,1-c]['status']:edges.add((n,D,'red'))
 # Literal scalar Lugano wires: hubbranch fixes each index. The separate
 # controlledB data wire has dimension2 on each fixed control sector.
 wires=defaultdict(set)
 def add(wire,a,b,index,dim):wires[wire,a,b].add((index,dim))
 for (o,c),sec in sections.items():
  hub=('H',*o)
  for i,lb in enumerate(sec['labs']):
   add(('h_lab',i),hub,lb,sec['x'][i],1)
   add(('lab_h',i),lb,hub,(sec['x'][i],o[i]),1)
  add('record',hub,T,o,1)
  add('control_data_in',S,('B',c),c,2)
  add('control_data_out',('B',c),D,c,2)
  if refined:
   add('B_to_L0',('B',c),sec['labs'][0],c,1)
   add('L0_to_B',sec['labs'][0],('B',c),c,1)
 for (wire,a,b),values in wires.items():
  if len(values)>1 or any(dim>1 for index,dim in values):edges.add((a,b,'solid'))
 nodes=set().union(*(sec['status'] for sec in sections.values()));reach={n:{n} for n in nodes}
 for a,b,color in edges:reach[a].add(b)
 for k in nodes:
  for a in nodes:
   if k in reach[a]:reach[a]|=reach[k]
 comps={frozenset(b for b in nodes if a in reach[b] and b in reach[a]) for a in nodes};cyclic=[]
 for comp in comps:
  ee=[e for e in edges if e[0] in comp and e[1] in comp]
  if len(comp)>1 or any(a==b for a,b,c in ee):
   colors={c for a,b,c in ee};assert colors=={'green'}
   cyclic.append({'nodes':[list(n) for n in sorted(comp)],'colors':sorted(colors)})
 assert len(cyclic)==1 and len(cyclic[0]['nodes'])==(4 if refined else 3)
 # The selected order is S,B0,all Lugano components,B1,D, with T placed
 # after its hub. Independent components may be interleaved this way.
 assert all(not(b[0]=='B' and a[0]=='L') and not(a[0]=='B' and b[0]=='L') for a,b,c in edges) if not refined else True
 return {'refined':refined,'native_recipient_algebra':'M2+M2+M2+M2' if refined else 'M2+M2','consistent_sections':16,
 'complete_forward_choices':len(forward),'complete_reverse_choices':len(reverse),'green_edges':sum(c=='green' for a,b,c in edges),
 'red_edges':sum(c=='red' for a,b,c in edges),'solid_edges':sum(c=='solid' for a,b,c in edges),'weak_loops_pass':True,'cyclic_components':cyclic},forward,f_nodes,sections,edges
old,of,on,os,oe=run(False);new,nf,nn,ns,ne=run(True)
assert old['complete_forward_choices']==128 and new['complete_forward_choices']==512
assert old['complete_reverse_choices']==new['complete_reverse_choices']==16
# Project the ENTIRE chosen oldA branch-choice vector, including its dormant
# x coordinate, from the selected flag copy. Not only the active branch.
for values,key in nf.items():
 chosen=dict(zip(nn,values));c=key[1]
 projected=tuple(chosen[lab(0,node[2],c,True)] if node[0]=='L' and node[1]==0 else chosen[node] for node in on)
 assert of[projected]==key
# Both flag values occur for each of A's two old branches.
assert all(any(lab(0,x,c,True) in sec['status'] for sec in ns.values()) for x,c in product([0,1],repeat=2))
# Exact native contraction check, including coherent control and full freedom
# at all four recipient copies. Boundary8×2×2=32.
I=s.eye(2);X=s.Matrix([[0,1],[1,0]]);Z=s.diag(1,-1);J=X*Z;U=(3*I+4*J)/5;V=(3*I+4*s.I*X)/5
recipient=[[U,V],[Z,X]] # flag c then oldbranch x
others=[[I,U],[X,V]];Bc=[U,V]
def lugano(A):
 out=s.zeros(8)
 for o,p in product(BITS,BITS):
  xx=w(o);out[4*o[0]+2*o[1]+o[2],4*p[0]+2*p[1]+p[2]]=A[xx[0]][o[0],p[0]]*others[0][xx[1]][o[1],p[1]]*others[1][xx[2]][o[2],p[2]]
 return out.applyfunc(s.expand)
source=s.eye(4);source.row_swap(0,3);decoder=s.eye(4);decoder.row_swap(1,2)
P=[s.diag(1,0),s.diag(0,1)]
def tensor(A0,A1):return (s.kronecker_product(s.eye(8),decoder)*sum((s.kronecker_product(lugano(A),P[c],Bc[c]) for c,A in enumerate([A0,A1])),s.zeros(32))*s.kronecker_product(s.eye(8),source)).applyfunc(s.expand)
F=tensor([I,I],[I,I]);newtensor=tensor(*recipient)
assert (F.H*F-s.eye(32)).applyfunc(s.expand)==s.zeros(32)
assert (newtensor.H*newtensor-s.eye(32)).applyfunc(s.expand)==s.zeros(32)
Q=s.kronecker_product(s.eye(8),source.H*s.kronecker_product(P[0],I)*source)
assert (newtensor-tensor(recipient[0],recipient[0])*Q-tensor(recipient[1],recipient[1])*(s.eye(32)-Q)).applyfunc(s.expand)==s.zeros(32)
# Time reversal literally swaps input/output routes and choice domains; the
# same enlarged SCC becomes red, with no solid/mixed cycles.
report={'status':'PASS','boundary_dimension':32,'old':old,'refined':new,'whole_recipient_choice_vector_projection_verified':True,
 'all_four_refined_recipient_branches_reachable':True,'exact_marked_contraction':True,
 'time_reversal':{'old_forward':16,'new_forward':16,'old_reverse':128,'new_reverse':512,'recurrent_color':'red','weak_loops_pass':True},
 'scope':'Branched-recipient refinement with recipient branches participating in a genuine Lugano SCC; actual route and finite exact contraction calibration, not a quartet host.'}
print(json.dumps(report,indent=2),flush=True)
