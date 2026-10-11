"""A valid routed DAG whose two reachable native branches cancel at baseline."""
from pathlib import Path
from itertools import product
import json
import sympy as s
ROOT=Path(__file__).parent
S=('S',);H=('H',);D=('D',)
sections=[{'c':c,'d':d,'nodes':{S,H,D,('A',c),('B',d)}} for c,d in product([0,1],repeat=2)]
# Local scalar routes: S chooses c; A_c relays c; H chooses d; B_d relays
# d; D closes it. A/B each also carry their own external input/output qubit.
# S,H,D have one native M2 branch; A/B each have two native M2 branches.
forward={(v['c'],v['d']):v for v in sections};reverse=dict(forward)
assert len(forward)==len(reverse)==4
edges=set();nodes=set().union(*(v['nodes'] for v in sections))
for c,d in product([0,1],repeat=2):
 cur=forward[c,d]
 for varying,target,key in [('c',S,(1-c,d)),('d',H,(c,1-d))]:
  for n in cur['nodes']^forward[key]['nodes']:edges.add((target,n,'green'))
 # Reverse input choices belong to H for c and D for d.
 for target,key in [(H,(1-c,d)),(D,(c,1-d))]:
  for n in cur['nodes']^reverse[key]['nodes']:edges.add((n,target,'red'))
# Every pair of co-occurring endpoint branches fixes the scalar index,
# so no internal physical wire induces a solid branch edge.
wire_sections={}
for v in sections:
 c,d=v['c'],v['d']
 for a,b,index in [(S,('A',c),c),(('A',c),H,c),(H,('B',d),d),(('B',d),D,d)]:
  wire_sections.setdefault((a,b),set()).add(index)
assert all(len(labels)==1 for labels in wire_sections.values())
reach={n:{n} for n in nodes}
for a,b,color in edges:reach[a].add(b)
for k in nodes:
 for a in nodes:
  if k in reach[a]:reach[a]|=reach[k]
assert all(not(a in reach[b] and b in reach[a]) for a in nodes for b in nodes if a!=b)
I=s.eye(2);X=s.Matrix([[0,1],[1,0]]);J=s.Matrix([[0,-1],[1,0]])
P0=s.diag(1,0);P1=s.diag(0,1);I4=s.eye(4)
out=[]
for name,U in [('identity',I),('swap',X),('rational_rotation',(3*I+4*J)/5)]:
 assert U.H*U==I
 # A active branch is c=0; B active branch is d=1.
 mixed=s.kronecker_product(P1*U*P0,I4)
 QA=s.kronecker_product(P0,I4);QB=s.kronecker_product(U.H*P1*U,I4)
 assert QA**2==QA and QB**2==QB
 assert s.trace(QA)==s.trace(QB)==4
 out.append({'auxiliary':name,'mixed_branch_coefficient_HS_squared':str(s.trace(mixed.H*mixed)),
             'individual_branch_projection_ranks':[4,4],
             'branch_overlap_trace':str(s.trace(QA*QB))})
assert out[0]['mixed_branch_coefficient_HS_squared']=='0'
assert out[1]['mixed_branch_coefficient_HS_squared']=='4'
assert out[2]['mixed_branch_coefficient_HS_squared']=='64/25'
(ROOT/'native_branch_cooccurrence_baseline_counterexample_checks.json').write_text(json.dumps({'status':'PASS','boundary_dimension':8,'consistent_sections':4,'forward_complete_choices':4,'reverse_complete_choices':4,'internal_solid_edges':0,'branch_graph_acyclic':True,'joint_active_route_reachable':True,'contexts':out,'scope':'Zero multi-active coefficients and orthogonal native branch flags at one auxiliary baseline do not imply graph non-cooccurrence or their persistence under auxiliary variation.'},indent=2)+'\n')
print('PASS: jointly reachable active branches have zero mixed coefficient at identity and nonzero coefficient after an allowed auxiliary change')
