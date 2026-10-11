"""Exact pair nonseriality and a one-unbranched-query switch calibration.

This does not test an invented quartet route. It proves the finite input to
the branch-cover necessity and checks an actual routed switch illustrating
why a single unbranched original query can remain compatible with routing.
"""
from pathlib import Path
from itertools import permutations, product
import json
import sympy as s
from exact_fixtures import E,I2,I16,X,Y,Z,R,local,tensor
ROOT=Path(__file__).parent

def quartet(us):
 W=tensor(us)
 return W+sum((tensor([Z*us[j]*Z-us[j] if j==i else us[j] for j in range(4)])*E[i] for i in range(4)),s.zeros(16))
assert quartet([I2]*4)==I16
pairs=[]
for i,j in permutations(range(4),2):
 for (an,aa),(bn,bb) in product([('X',X),('Y',Y),('Z',Z)],repeat=2):
  us=[I2]*4;us[i]=aa;us[j]=bb
  A=quartet(us);assert A.H*A==I16
  defect=A-R[j]*local(j,bb)*R[j]*R[i]*local(i,aa)*R[i]
  if defect!=s.zeros(16):break
 else:raise AssertionError((i,j))
 pos=next((a,b) for a in range(16) for b in range(16) if defect[a,b])
 pairs.append({'before':i+1,'after':j+1,'queries':[an,bn],'defect_HS_squared':str(s.trace(defect.H*defect)),'entry':[pos[0],pos[1],str(defect[pos])]})
print('All12 ordered pairs fail at exact Pauli contexts',flush=True)

# Actual routed switch with A a single M2 branch and B two M2 branches.
# S,D are full M4 caps; M,N have two M2 branches. For control c=0 the
# data path is S-B0-M0-A-N0-D; for c=1 it is S-M1-A-N1-B1-D.
S=('S',);D=('D',);A=('A',)
def branch(name,c):return (name,c)
# Literal wire/route presentation, not just a desired dependency graph.
wire_ends={'sb':('S','B'),'sm':('S','M'),'bm':('B','M'),
 'ma':('M','A'),'an':('A','N'),'nb':('N','B'),'nd':('N','D'),
 'bd':('B','D'),'smc':('S','M'),'mnc':('M','N'),'ndc':('N','D')}
wire_dims={w:({0:2} if w in ['ma','an'] else {0:1,1:1} if w.endswith('c') else {0:1,1:2}) for w in wire_ends}
ports={'S':([],['sb','sm','smc']),'B':(['sb','nb'],['bm','bd']),
 'M':(['sm','bm','smc'],['ma','mnc']),'A':(['ma'],['an']),
 'N':(['an','mnc'],['nb','nd','ndc']),'D':(['bd','nd','ndc'],[])}
routes={'S':[(S,[() ],[(1,0,0),(0,1,1)])],
 'B':[(branch('B',0),[(1,0)],[(1,0)]),(branch('B',1),[(0,1)],[(0,1)])],
 'M':[(branch('M',0),[(0,1,0)],[(0,0)]),(branch('M',1),[(1,0,1)],[(0,1)])],
 'A':[(A,[(0,)],[(0,)])],
 'N':[(branch('N',0),[(0,0)],[(0,1,0)]),(branch('N',1),[(0,1)],[(1,0,1)])],
 'D':[(D,[(0,1,0),(1,0,1)],[()])]}
def tuple_dim(wires,labels):
 out=1
 for w,label in zip(wires,labels):out*=wire_dims[w][label]
 return out
for name,branches in routes.items():
 iw,ow=ports[name]
 for node,ins,outs in branches:
  di=sum(tuple_dim(iw,t) for t in ins)*(4 if name=='S' else 1)
  do=sum(tuple_dim(ow,t) for t in outs)*(4 if name=='D' else 1)
  assert di==do==(4 if name in ['S','D'] else 2)
 for k,(_,ins,outs) in enumerate(branches):
  for _,other_in,other_out in branches[k+1:]:
   assert not set(ins)&set(other_in) and not set(outs)&set(other_out)
from itertools import product
wires=list(wire_ends);sections=[]
for labels in product(*[list(wire_dims[w]) for w in wires]):
 sec=dict(zip(wires,labels));status=set();ok=True
 for name,(iw,ow) in ports.items():
  a=tuple(sec[w] for w in iw);b=tuple(sec[w] for w in ow)
  matches=[node for node,ins,outs in routes[name] if a in ins and b in outs]
  if len(matches)!=1:ok=False;break
  status.add(matches[0])
 if ok:
  c=sec['smc'];assert c==sec['mnc']==sec['ndc']
  sections.append({'control':c,'status':status,'wire_indices':sec})
assert len(sections)==2
forward={v['control']:v for v in sections};reverse=dict(forward)
assert len(forward)==len(reverse)==2
nodes=set().union(*(v['status'] for v in sections));edges=set()
for c,v in forward.items():
 for n in v['status']^forward[1-c]['status']:edges.add((S,n,'green'))
for c,v in reverse.items():
 for n in v['status']^reverse[1-c]['status']:edges.add((n,D,'red'))
# Compute solid edges directly from all consistent sections and sectors.
conditional={}
for sec in sections:
 for wire,(src,dst) in wire_ends.items():
  source=next(n for n in sec['status'] if n[0]==src)
  target=next(n for n in sec['status'] if n[0]==dst)
  label=sec['wire_indices'][wire]
  conditional.setdefault((wire,source,target),set()).add((label,wire_dims[wire][label]))
for (wire,source,target),values in conditional.items():
 if len(values)>1 or any(dim>1 for label,dim in values):edges.add((source,target,'solid'))
assert not any(b==A and color=='green' for a,b,color in edges)
assert not any(a==A and color=='red' for a,b,color in edges)
reach={n:{n} for n in nodes}
for a,b,color in edges:reach[a].add(b)
for k in nodes:
 for a in nodes:
  if k in reach[a]:reach[a]|=reach[k]
assert all(not(a in reach[b] and b in reach[a]) for a in nodes for b in nodes if a!=b)
assert not any(a==b for a,b,color in edges)
# Native dimensions: S,D each4; A2; B0,B1,M0,M1,N0,N1 each2.
# At identity auxiliaries the control-preserving contraction is AB/BA.
Y=s.Matrix([[0,-s.I],[s.I,0]])
UA=(3*I2+4*s.I*X)/5;UB=(5*I2+12*s.I*Z)/13
assert (UA.H*UA-I2).applyfunc(s.simplify)==s.zeros(2) and (UB.H*UB-I2).applyfunc(s.simplify)==s.zeros(2)
switch=s.diag(UA*UB,UB*UA)
assert (switch.H*switch-s.eye(4)).applyfunc(s.simplify)==s.zeros(4)
assert switch!=s.diag(UA*UB,UA*UB)
assert switch!=s.diag(UB*UA,UB*UA)
# Full native completeness is supplied by the checked acyclic branch graph.
# Algebraically the two blocks are N0 A M0 B0 and B1 N1 A M1, between
# arbitrary full M4 source/decoder fillers, with independent private ancillas.
out={'status':'PASS','quartet_pair_nonseriality':pairs,'pair_nonseriality_graph':'K4','minimum_vertex_cover':3,'quartet_consequence':'At least three original query vertices have more than one reachable native branch, equivalently nonzero classified active ideals.','switch_calibration':{'boundary_dimension':4,'complete_forward_choices':2,'complete_reverse_choices':2,'section_count':2,'original_native_algebras':{'A':'M2','B':'M2+M2'},'auxiliary_native_algebras':{'S':'M4','D':'M4','M':'M2+M2','N':'M2+M2'},'branches':len(nodes),'solid_edges':sum(c=='solid' for a,b,c in edges),'green_edges':sum(c=='green' for a,b,c in edges),'red_edges':sum(c=='red' for a,b,c in edges),'branch_graph_acyclic':True,'weak_loops_pass':True,'ordered_query_products_differ':True},'scope':'A topological necessity, using the previously audited earliest-green extraction theorem. The switch calibration is a separate valid host and not a quartet candidate.'}
(ROOT/'native_branch_cover_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: actual switch calibration has one unbranched query and an acyclic branch graph',flush=True)
