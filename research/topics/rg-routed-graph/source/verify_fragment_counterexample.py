"""Exact local whole-SCC counterexample to host-boundary domain inheritance.
No floating-point arithmetic; all native branches remain unrestricted and square.
"""
from itertools import product, combinations
from pathlib import Path
import json

BITS=list(product(range(2), repeat=3))
SHIFTS=[(0,0,0),(1,0,0),(0,1,0),(0,0,1)]
CHOICES=list(product(range(2),repeat=6))
def w(o):
 a,b,c=o
 return ((1-b)*c,(1-c)*a,(1-a)*b)
def x_for(s,o):return tuple(a^b for a,b in zip(w(o),SHIFTS[s]))
def A(i,x):return ('A',i,x)
def X(s,o):return ('X',s,*o)
S=('S',);D=('D',)
NODES=[S,D]+[A(i,x) for i in range(3) for x in range(2)]+[X(s,o) for s in range(4) for o in BITS]
sections=[]
for s,o in product(range(4),BITS):
 x=x_for(s,o)
 sections.append(dict(s=s,o=o,x=x,status=frozenset([S,D,X(s,o)]+[A(i,x[i]) for i in range(3)])))
forward={}
for s,f in product(range(4),CHOICES):
 sol=[v for v in sections if v['s']==s and all(v['o'][i]==f[2*i+v['x'][i]] for i in range(3))]
 assert len(sol)==1
 forward[s,f]=sol[0]
# Reverse choice at D is (s,o); all other reverse choices are singleton.
assert len(sections)==len({(v['s'],v['o']) for v in sections})==32
edges=set()
for (s,f),v in forward.items():
 for t in range(4):
  for target in v['status']^forward[t,f]['status']:edges.add((S,target,'green'))
 for b in range(6):
  ff=list(f);ff[b]^=1
  for target in v['status']^forward[s,tuple(ff)]['status']:edges.add((A(b//2,b%2),target,'green'))
for b in NODES:
 if len({b in v['status'] for v in sections})>1:edges.add((b,D,'red'))
# For each internal wire, confirm fixed one-dimensional value conditional
# on the endpoints' branches. Hence the exact primary solid graph is empty.
wire_records={}
for v in sections:
 s,o,x=v['s'],v['o'],v['x']; hub=X(s,o)
 records=[('SX',S,hub,s),('XD',hub,D,(s,o))]
 for i in range(3):
  records += [(f'R{i}',hub,A(i,x[i]),x[i]),(f'T{i}',A(i,x[i]),hub,(x[i],o[i]))]
 for e,src,dst,value in records:wire_records.setdefault((e,src,dst),set()).add(value)
assert all(len(vals)==1 for vals in wire_records.values())
reach={a:{a} for a in NODES}
for a,b,c in edges:reach[a].add(b)
for k in NODES:
 for a in NODES:
  if k in reach[a]:reach[a]|=reach[k]
comps={frozenset(b for b in NODES if b in reach[a] and a in reach[b]) for a in NODES}
C=frozenset(A(i,x) for i in range(3) for x in range(2))
assert C in comps
assert all(color=='green' for a,b,color in edges if a in C and b in C)
assert all(color=='green' or a not in reach[b] for a,b,color in edges)
assert sorted(map(len,comps))==[1]*34+[6]
rin={v['x'] for v in sections};rout={(v['x'],v['o']) for v in sections}
assert rin==set(BITS)-{(1,1,1)} and len(rout)==32
# After opening C, each lab is a rectangular native U(2) branch.
# For EVERY r in BITS and complete f, the one section has o_i=f_i(r_i).
opened={(r,f):(r,tuple(f[2*i+r[i]] for i in range(3))) for r,f in product(BITS,CHOICES)}
assert len(opened)==512
bad=(1,1,1); fzero=(0,)*6
assert (bad,fzero) in opened and bad not in rin
# A stronger witness: input r is host-reachable, but independent choices
# produce an output that the proposed coherent decoder would reject.
r=(1,1,0);o=(0,0,0)
assert r in rin and opened[r,fzero]==(r,o) and (r,o) not in rout
# Any quantum external past has dimension 4*2^3=32. D has native U(32).
# S is U(4), all A branches U(2), all X branches U(1).
report={
 'forward_complete_choice_count':len(forward),
 'reverse_complete_choice_count':32,
 'consistent_host_section_count':32,
 'green_edge_count':sum(c=='green' for a,b,c in edges),
 'red_edge_count':sum(c=='red' for a,b,c in edges),
 'solid_edge_count':0,
 'SCC_sizes':sorted(map(len,comps)),
 'whole_laboratory_SCC':sorted(C),
 'SCC_internal_green_edges':sorted((a,b) for a,b,c in edges if a in C and b in C),
 'host_input_index_tuples':sorted(rin),
 'host_output_index_tuple_count':len(rout),
 'opened_input_index_tuple_count':len(BITS),
 'opened_output_index_tuple_count':64,
 'opened_boundary_choice_pair_count':len(opened),
 'outside_input_witness':{'input':bad,'forward_choices':fzero,'output':opened[bad,fzero][1]},
 'cap_rejection_witness':{'input':r,'forward_choices':fzero,'output':o},
 'native_branch_dimensions':{'S':4,'each_A_branch':2,'each_X_branch':1,'D':32},
 'external_dimension':32,
 'scope':'Selected SCC contains whole vertices; global whole-vertex condition fails at X. Not a nonroutability counterexample.'
}
path=Path(__file__).with_name('fragment_counterexample_checks.json');path.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
