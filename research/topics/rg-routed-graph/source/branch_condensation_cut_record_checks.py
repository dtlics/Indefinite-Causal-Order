"""Exact multi-flag scalar pivots at ALL condensation cuts of valid test hosts.

Also exhaust the four-endpoint poset criterion, including every possible
SCC identification, against order ideals and all linear extensions.
"""
from pathlib import Path
from itertools import product,permutations
from collections import defaultdict
import json
import sympy as s
ROOT=Path(__file__).parent

def graph_edges(sections,forward,fnodes,domains,reverse,rnodes,rdomains):
 edges=set()
 for mapping,nodes,doms,color in [(forward,fnodes,domains,'green'),(reverse,rnodes,rdomains,'red')]:
  for key,sec in mapping.items():
   for j,node in enumerate(nodes):
    for value in doms[j]:
     other=list(key);other[j]=value
     for target in sections[sec]^sections[mapping[tuple(other)]]:
      edges.add((node,target,color) if color=='green' else (target,node,color))
 return edges

def condense(nodes,edges):
 reach={v:{v} for v in nodes}
 for a,b,c in edges:reach[a].add(b)
 for k in nodes:
  for a in nodes:
   if k in reach[a]:reach[a]|=reach[k]
 comps=list({frozenset(b for b in nodes if a in reach[b] and b in reach[a]) for a in nodes})
 comps.sort(key=lambda c:str(sorted(c)));which={v:i for i,c in enumerate(comps) for v in c}
 deps={(which[a],which[b]) for a,b,c in edges if which[a]!=which[b]}
 cyclic=[]
 for c in comps:
  ee=[e for e in edges if e[0] in c and e[1] in c]
  if len(c)>1 or any(a==b for a,b,col in ee):
   colors={col for a,b,col in ee};assert colors in [{'green'},{'red'}]
   cyclic.append({'nodes':[list(v) for v in sorted(c)],'colors':sorted(colors)})
 return comps,which,deps,reach,cyclic

def all_ideals(n,deps):
 return [frozenset(i for i in range(n) if mask>>i&1) for mask in range(1<<n)
         if all(not(mask>>b&1) or bool(mask>>a&1) for a,b in deps)]

def audit_pivots(name,sections,forward,fnodes,fdomains,reverse,rnodes,rdomains,query_branches,passive):
 nodes=set().union(*sections.values());edges=graph_edges(sections,forward,fnodes,fdomains,reverse,rnodes,rdomains)
 comps,which,deps,reach,cycles=condense(nodes,edges);ideals=all_ideals(len(comps),deps)
 records={};patterns_seen={};overlaps=0
 for ideal in ideals:
  js=[j for j,bs in enumerate(query_branches) if len({which[b] in ideal for b in bs})==2]
  selected={j:frozenset(b for b in query_branches[j] if (which[b] in ideal)!=(which[passive[j]] in ideal)) for j in js}
  key=tuple((j,tuple(sorted(selected[j]))) for j in js)
  if key not in records:
   augmented={sec:status|{('PIVOT',)+tuple(int(bool(status&selected[j])) for j in js)} for sec,status in sections.items()}
   newnodes=set().union(*augmented.values());newedges=graph_edges(augmented,forward,fnodes,fdomains,reverse,rnodes,rdomains)
   # All new pivot branches are singleton->singleton in their flag pattern;
   # each old query branch receives/sends its fixed selected-set indicator.
   # Hence no new choice coordinates or dimensions and no new solid edge.
   for sec,status in sections.items():
    flag=next(v for v in augmented[sec] if v[0]=='PIVOT')[1:]
    for jj,j in enumerate(js):
     b=next(b for b in query_branches[j] if b in status)
     assert flag[jj]==int(b in selected[j])
   cc,ww,dd,rr,newcycles=condense(newnodes,newedges)
   assert not any(any(v[0]=='PIVOT' for v in c) and len(c)>1 for c in cc)
   records[key]={'straddling_queries':js,'reachable_patterns':sorted({tuple(int(bool(status&selected[j])) for j in js) for status in sections.values()}),
     'complete_forward_choices':len(forward),'complete_reverse_choices':len(reverse),'new_pivot_coordinates':0,'weak_loops_pass':True,'cycles':newcycles}
  # Native event sets selected on opposite sides from their passive anchors
  # must agree exactly with cut crossings for every chosen section.
  for sec,status in sections.items():
   event=[]
   for j,bs in enumerate(query_branches):
    b=next(b for b in bs if b in status)
    cross=(which[b] in ideal)!=(which[passive[j]] in ideal)
    if j in selected:assert cross==bool(status&selected[j])
    else:assert not cross
    event.append(int(cross))
   overlaps=max(overlaps,sum(event))
 # All calibrations use baseline-orthogonal chosen active flags. The Lugano
 # host has genuine mutual exclusion; the DAG counterexample has coactive
 # flags but they can never both straddle one ideal.
 assert overlaps<=1
 return {'host':name,'old_sections':len(sections),'condensation_components':len(comps),'all_order_ideals_checked':len(ideals),
  'distinct_record_partitions_checked':len(records),'largest_straddling_query_count':max((len(v['straddling_queries']) for v in records.values()),default=0),
  'maximum_simultaneous_selected_cut_events':overlaps,'record_partitions':list(records.values()),'old_cycles':cycles},(which,reach)

# Time-reversed Lugano, where branch1 is active and branch0 passive.
WORDS=list(product([0,1],repeat=3))
def w(p):
 a,b,c=p;return (b*(1-c),(1-a)*c,a*(1-b))
S=('S',)
sections={p:frozenset({S,('H',)+p}|{('L',i,w(p)[i]) for i in range(3)}) for p in WORDS}
forward={(k,):p for k,p in enumerate(WORDS)};reverse={}
rnodes=[('L',i,x) for i in range(3) for x in [0,1]]
for f in product([0,1],repeat=6):
 sol=[p for p in WORDS if all(p[i]==f[2*i+w(p)[i]] for i in range(3))]
 assert len(sol)==1;reverse[f]=sol[0]
qb=[[('L',i,0),('L',i,1)] for i in range(3)];passive=[b[0] for b in qb]
rev_report,unused=audit_pivots('reversed_Lugano',sections,forward,[S],[list(range(8))],reverse,rnodes,[[0,1]]*6,qb,passive)
fwd_report,unused=audit_pivots('forward_Lugano',sections,reverse,rnodes,[[0,1]]*6,forward,[S],[list(range(8))],qb,passive)
assert rev_report['largest_straddling_query_count']==fwd_report['largest_straddling_query_count']==3
# Exact source-conjugated record projections and arbitrary phase factors.
I=s.eye(2);X=s.Matrix([[0,1],[1,0]]);Z=s.diag(1,-1);J=X*Z;U=(3*I+4*J)/5;V=(3*I+4*s.I*X)/5
labs=[[I,U],[X,V],[Z,U.T]];v=s.Matrix(range(1,9));source=s.eye(8)-2*v*v.T/(v.T*v)[0]
G=s.Matrix(8,8,lambda o,p:s.prod(labs[i][w(WORDS[p])[i]][WORDS[o][i],WORDS[p][i]] for i in range(3)))*source
G=G.applyfunc(s.expand);assert (G.H*G-s.eye(8)).applyfunc(s.expand)==s.zeros(8)
flags=[s.diag(*[w(p)[i] for p in WORDS]) for i in range(3)];P=[source.H*f*source for f in flags]
assert all(P[i]*P[j]==s.zeros(8) for i in range(3) for j in range(3) if i!=j)
pattern_projections=[]
for bits in product([0,1],repeat=3):
 Q=s.eye(8)
 for bit,Pi in zip(bits,P):Q=Q*(Pi if bit else s.eye(8)-Pi)
 Q=Q.applyfunc(s.factor);assert Q**2==Q and Q.H==Q
 expected=source.H*s.diag(*[int(w(p)==bits) for p in WORDS])*source
 assert Q==expected
 assert (Q==s.zeros(8))==(sum(bits)>=2)
 if Q!=s.zeros(8):pattern_projections.append(Q)
assert [int(s.trace(Q)) for Q in pattern_projections]==[2]*4
phases=[1,-1,s.I,-s.I];K=sum((z*Q for z,Q in zip(phases,pattern_projections)),s.zeros(8));assert (K.H*K-s.eye(8)).applyfunc(s.expand)==s.zeros(8)
assert ((G*K).H*(G*K)-s.eye(8)).applyfunc(s.expand)==s.zeros(8)
# Noncommuting private record fillers give a unitary too.
private=[I,X,Z,U];H=sum((s.kronecker_product(G*Q,Vv) for Q,Vv in zip(pattern_projections,private)),s.zeros(16))
assert (H.H*H-s.eye(16)).applyfunc(s.expand)==s.zeros(16)

# The known baseline-zero DAG counterexample: A0 and B1 really co-occur,
# yet no condensation cut separates each from its passive anchor at once.
S=('S',);Hn=('H',);D=('D',)
ss={(c,d):frozenset({S,Hn,D,('A',c),('B',d)}) for c,d in product([0,1],repeat=2)}
ff={(c,d):(c,d) for c,d in ss};rr=dict(ff)
dag_report,unused=audit_pivots('baseline_zero_DAG',ss,ff,[S,Hn],[[0,1]]*2,rr,[Hn,D],[[0,1]]*2,
 [[('A',0),('A',1)],[('B',0),('B',1)]],[('A',1),('B',0)])
assert dag_report['largest_straddling_query_count']==1 and ('A',0) in ss[0,1] and ('B',1) in ss[0,1]

# Strong intrinsic endpoint criterion. Enumerate all equivalence patterns
# of four endpoint labels, then every partial order on their distinct SCCs.
def partitions(seq):
 if not seq:yield [];return
 first,*tail=seq
 for rest in partitions(tail):
  yield [[first]]+[list(b) for b in rest]
  for j in range(len(rest)):
   out=[list(b) for b in rest];out[j]=[first]+out[j];yield out

def posets(n):
 seen=set()
 for order in permutations(range(n)):
  pairs=[(order[i],order[j]) for i in range(n) for j in range(i+1,n)]
  for mask in range(1<<len(pairs)):
   rel={(i,i) for i in range(n)}|{e for k,e in enumerate(pairs) if mask>>k&1}
   for k in range(n):
    rel|={(i,j) for i in range(n) for j in range(n) if (i,k) in rel and (k,j) in rel}
   key=tuple(sorted(rel))
   if key not in seen:seen.add(key);yield set(key)
checked=0;orders_checked=0
for part in partitions(list(range(4))):
 n=len(part);where={v:i for i,b in enumerate(part) for v in b};a,p,b,q=[where[i] for i in range(4)]
 for rel in posets(n):
  ideals=all_ideals(n,{(i,j) for i,j in rel if i!=j})
  bad_ideal=any(((a in I)!=(p in I)) and ((b in I)!=(q in I)) for I in ideals)
  # A separating ideal exists iff an orientation has no excluded endpoint
  # below an included endpoint; choose the downward closure of the included.
  bad_orientation=False
  for included_i,excluded_i in [(a,p),(p,a)]:
   for included_j,excluded_j in [(b,q),(q,b)]:
    if all((e,u) not in rel for e in [excluded_i,excluded_j] for u in [included_i,included_j]):bad_orientation=True
  assert bad_ideal==bad_orientation
  bad_interval=False
  for order in permutations(range(n)):
   position={v:i for i,v in enumerate(order)}
   if any(position[i]>=position[j] for i,j in rel if i!=j):continue
   orders_checked+=1
   cuts_i=set(range(min(position[a],position[p]),max(position[a],position[p])))
   cuts_j=set(range(min(position[b],position[q]),max(position[b],position[q])))
   bad_interval|=bool(cuts_i&cuts_j)
  assert bad_interval==bad_ideal
  if a!=p and b!=q:
   pair_ordered=(all((u,v) in rel for u in [a,p] for v in [b,q]) or all((v,u) in rel for u in [a,p] for v in [b,q]))
   assert pair_ordered==(not bad_ideal)
  checked+=1
assert checked==355
out={'status':'PASS','framework_source':'https://arxiv.org/html/2206.10042v3, Definitions B.5, B.7, B.12','isolated_M1_pivot_allowed':True,
 'calibrations':[rev_report,fwd_report,dag_report],'three_flag_record_projection_ranks':[2,2,2,2],
 'exact_private_record_unitarity_checked':True,'endpoint_posets_with_SCC_identifications_checked':checked,'linear_extensions_checked':orders_checked,'nondegenerate_endpoint_pairs_are_completely_ordered_verified':True,
 'scope':'All condensation order ideals of the three actual host calibrations; exact intrinsic four-endpoint cut criterion including ties. These support the general cut-record proof but do not construct a quartet host or resolve shared-SCC/interleaved survivors.'}
(ROOT/'branch_condensation_cut_record_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS:',[(r['host'],r['all_order_ideals_checked'],r['distinct_record_partitions_checked']) for r in out['calibrations']],'endpoint posets',checked,'linear extensions',orders_checked,flush=True)
