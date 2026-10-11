"""Exact flag-loop refinement on a genuinely cyclic routed host.

A Lugano feedback component supplies g=o1 to a controlled-order data segment.
The unbranched M2 auxiliary A has nontrivial forward AND reverse choices;
refinement exposes both dormant copies, while every old native branch keeps
its full freedom. No tensor completeness is used to assert graph validity.
"""
from pathlib import Path
from itertools import product
from collections import defaultdict
import json
import sympy as s
ROOT=Path(__file__).parent
BITS=list(product([0,1],repeat=3));V=-1

def w(o):
 a,b,c=o;return (b*(1-c),(1-a)*c,a*(1-b))
def node(name,*xs):return (name,*xs)
A=node('A');D=node('D')
def record(o):return 4*o[0]+2*o[1]+o[2]

def audit(refined):
 # All sectors on internal wires have dimension one. Summed correlated
 # practical spaces still carry the full indicated matrix algebras.
 ends={**{f'h{i}':('H',f'L{i}') for i in range(3)},
       **{f'l{i}':(f'L{i}','H') for i in range(3)},
       'ht':('H','T'),'hd':('H','D'),'tb':('T','B'),'tm':('T','M'),
       'bm':('B','M'),'ma':('M','A'),'an':('A','N'),'nb':('N','B'),
       'nd':('N','D'),'bd':('B','D'),'tc':('T','M'),'mc':('M','N'),'nc':('N','D')}
 if refined:ends.update({'ba_flag':('B','A'),'ab_flag':('A','B')})
 ports={}
 for name in ['H','L0','L1','L2','T','B','M','A','N','D']:
  ports[name]=([e for e,(a,b) in ends.items() if b==name],[e for e,(a,b) in ends.items() if a==name])
 # Native rectangular routes, listed as dictionaries of wire indices.
 routes=defaultdict(list)
 def add(name,branch,ins,outs,expected,external_in=1,external_out=1):
  iw,ow=ports[name];ins=[tuple(d[e] for e in iw) for d in ins];outs=[tuple(d[e] for e in ow) for d in outs]
  assert len(ins)*external_in==len(outs)*external_out==expected
  for _,ii,oo,dd in routes[name]:assert not set(ii)&set(ins) and not set(oo)&set(outs)
  routes[name].append((branch,ins,outs,expected))
 for o in BITS:
  x=w(o);add('H',node('H',*o),[{f'l{i}':(x[i],o[i]) for i in range(3)}],
      [{**{f'h{i}':x[i] for i in range(3)},'ht':o[0],'hd':o[1:]}],1)
 for i in range(3):
  for x in [0,1]:add(f'L{i}',node(f'L{i}',x),[{f'h{i}':x}],[{f'l{i}':(x,o)} for o in [0,1]],2,external_in=2)
 for g in [0,1]:
  add('T',node('T',g),[{'ht':g}],[{'tb':t if g==0 else V,'tm':t if g==1 else V,'tc':g} for t in [0,1]],2,external_in=2)
  ins=[{'tb':p if g==0 else V,'nb':p if g==1 else V} for p in [0,1]]
  outs=[{'bm':q if g==0 else V,'bd':q if g==1 else V} for q in [0,1]]
  if refined:
   for d in ins:d['ab_flag']=g
   for d in outs:d['ba_flag']=g
  add('B',node('B',g),ins,outs,2)
  for q in [0,1]:add('M',node('M',g,q),[{'tm':q if g==1 else V,'bm':q if g==0 else V,'tc':g}],[{'ma':q,'mc':g}],1)
  for k in [0,1]:add('N',node('N',g,k),[{'an':k,'mc':g}],[{'nb':k if g==1 else V,'nd':k if g==0 else V,'nc':g}],1)
 if refined:
  for g in [0,1]:add('A',node('A',g),[{'ma':q,'ba_flag':g} for q in [0,1]],[{'an':k,'ab_flag':g} for k in [0,1]],2)
 else:add('A',A,[{'ma':q} for q in [0,1]],[{'an':k} for k in [0,1]],2)
 add('D',D,[{'hd':o[1:],'nc':o[0],'nd':z if o[0]==0 else V,'bd':z if o[0]==1 else V} for o in BITS for z in [0,1]],[{}],16,external_out=16)
 # All consistent sections are parametrized by (o,q,k,t); t is the source
 # data index p when g=0 and the output data index z when g=1. The hub fixes
 # all lab indices, the control relays fix g, and each exclusive data path
 # is a chain. Thus there are no additional section degrees of freedom.
 sections={}
 for o,q,k,t in product(BITS,[0,1],[0,1],[0,1]):
  g=o[0];x=w(o);idx={**{f'h{i}':x[i] for i in range(3)},**{f'l{i}':(x[i],o[i]) for i in range(3)},
   'ht':g,'hd':o[1:],'tb':t if g==0 else V,'tm':q if g==1 else V,
   'bm':q if g==0 else V,'ma':q,'an':k,'nb':k if g==1 else V,
   'nd':k if g==0 else V,'bd':t if g==1 else V,'tc':g,'mc':g,'nc':g}
  if refined:idx.update({'ba_flag':g,'ab_flag':g})
  active={}
  for name,(iw,ow) in ports.items():
   a=tuple(idx[e] for e in iw);b=tuple(idx[e] for e in ow)
   choices=[br for br,ins,outs,dim in routes[name] if a in ins and b in outs]
   assert len(choices)==1;active[name]=choices[0]
  sections[o,q,k,t]={'indices':idx,'active':active,'status':frozenset(active.values())}
 assert len(sections)==64
 # Exhaust all complete choices, including dormant coordinates.
 fnodes=[br for branches in routes.values() for br,ins,outs,dim in branches if len(outs)>1]
 rnodes=[br for branches in routes.values() for br,ins,outs,dim in branches if len(ins)>1]
 lookup={br:(ins,outs) for branches in routes.values() for br,ins,outs,dim in branches}
 def enumerate_choices(nodes,forward):
  maps={}
  for values in product(*[range(len(lookup[br][1 if forward else 0])) for br in nodes]):
   assignments=dict(zip(nodes,values));matches=[]
   for key,sec in sections.items():
    good=True
    for name,br in sec['active'].items():
     iw,ow=ports[name];wires=ow if forward else iw;tuples=lookup[br][1 if forward else 0]
     wanted=tuples[assignments.get(br,0)]
     if tuple(sec['indices'][e] for e in wires)!=wanted:good=False;break
    if good:matches.append(key)
   assert len(matches)==1,(forward,values,matches)
   maps[values]=matches[0]
  return maps
 fm=enumerate_choices(fnodes,True);rm=enumerate_choices(rnodes,False)
 edges=set()
 for nodes,mapping,forward in [(fnodes,fm,True),(rnodes,rm,False)]:
  for choices,key in mapping.items():
   status=sections[key]['status']
   for j,br in enumerate(nodes):
    size=len(lookup[br][1 if forward else 0])
    for value in range(size):
     if value==choices[j]:continue
     other=list(choices);other[j]=value;status2=sections[mapping[tuple(other)]]['status']
     for b in status^status2:edges.add((br,b,'green') if forward else (b,br,'red'))
 conditional=defaultdict(set)
 for sec in sections.values():
  for wire,(src,dst) in ends.items():conditional[wire,sec['active'][src],sec['active'][dst]].add(sec['indices'][wire])
 for (wire,src,dst),values in conditional.items():
  if len(values)>1:edges.add((src,dst,'solid'))
 nodes=set().union(*(sec['status'] for sec in sections.values()));reach={n:{n} for n in nodes}
 for a,b,color in edges:reach[a].add(b)
 for k in nodes:
  for a in nodes:
   if k in reach[a]:reach[a]|=reach[k]
 comps={frozenset(b for b in nodes if a in reach[b] and b in reach[a]) for a in nodes}
 cyclic=[]
 for comp in comps:
  internal=[e for e in edges if e[0] in comp and e[1] in comp]
  if len(comp)>1 or any(a==b for a,b,c in internal):
   colors={c for a,b,c in internal};assert colors in [{'green'},{'red'}]
   cyclic.append({'nodes':[list(n) for n in sorted(comp)],'colors':sorted(colors)})
 assert cyclic and any(len(c['nodes'])>1 for c in cyclic)
 assert all(not any(n[0]=='A' for n in c['nodes']) for c in cyclic)
 result={'refined':refined,'section_count':64,'forward_complete_choices':len(fm),'reverse_complete_choices':len(rm),
  'forward_choice_coordinates':len(fnodes),'reverse_choice_coordinates':len(rnodes),
  'native_branch_count':len(nodes),'green_edges':sum(c=='green' for a,b,c in edges),'red_edges':sum(c=='red' for a,b,c in edges),'solid_edges':sum(c=='solid' for a,b,c in edges),
  'cyclic_components':cyclic,'weak_loops_pass':True,'native_auxiliary_algebra':'M2+M2' if refined else 'M2'}
 return result,sections,edges,{'forward_nodes':fnodes,'reverse_nodes':rnodes,'forward':fm,'reverse':rm}

old,sections,oldedges,oldchoices=audit(False);new,newsections,newedges,newchoices=audit(True)
assert set(sections)==set(newsections)
assert old['forward_complete_choices']==2048 and new['forward_complete_choices']==4096
assert old['reverse_complete_choices']==128 and new['reverse_complete_choices']==256
# Check the theorem's conditional-choice formulas explicitly, including all
# dormant copied coordinates and bidirectional independence of the selector.
for direction in ['forward','reverse']:
 oldnodes=oldchoices[direction+'_nodes'];newnodes=newchoices[direction+'_nodes']
 aa=oldnodes.index(A)
 for values,key in oldchoices[direction].items():
  flipped=list(values);flipped[aa]^=1
  assert oldchoices[direction][tuple(flipped)][0][0]==key[0][0]
 for values,key in newchoices[direction].items():
  assignment=dict(zip(newnodes,values));g=key[0][0]
  projected=tuple(assignment[node('A',g)] if br==A else assignment[br] for br in oldnodes)
  assert oldchoices[direction][projected]==key
# A topological order of the old SCC condensation verifies every newly
# exposed edge has the precise inherited-or-cross-separator classification.
oldnodes=set().union(*(v['status'] for v in sections.values()));reach={n:{n} for n in oldnodes}
for a,b,c in oldedges:reach[a].add(b)
for k in oldnodes:
 for a in oldnodes:
  if k in reach[a]:reach[a]|=reach[k]
comps={frozenset(b for b in oldnodes if a in reach[b] and b in reach[a]) for a in oldnodes}
compof={n:c for c in comps for n in c};dag={c:set() for c in comps}
for a,b,color in oldedges:
 if compof[a]!=compof[b]:dag[compof[a]].add(compof[b])
ordered=[];remaining=set(comps)
while remaining:
 candidates=sorted((c for c in remaining if not any(c in dag[d] for d in remaining)),key=lambda c:str(sorted(c)))
 assert candidates
 c=candidates[0];ordered.append(c);remaining.remove(c)
level={n:i for i,c in enumerate(ordered) for n in c};ka=level[A]
assert level[node('B',0)]<ka<level[node('B',1)]
extra=0
for a,b,color in newedges:
 aa=A if a[0]=='A' else a;bb=A if b[0]=='A' else b
 if (aa,bb,color) in oldedges:continue
 extra+=1
 if bb==A:assert color=='green' and level[aa]<ka
 elif aa==A:assert color=='red' and level[bb]>ka
 else:assert color in ['green','red'] and level[aa]<ka<level[bb]
# Exact marked contraction with nontrivial rational native fillers. The future
# decoder mixes the record sectors; no measurement of the selector is made.
I=s.eye(2);X=s.Matrix([[0,1],[1,0]]);Z=s.diag(1,-1);J=X*Z
U=(3*I+4*J)/5;Vq=(3*I+4*s.I*X)/5
labs=[[I,U],[X,Vq],[Z,U.T]];Ts=[U,Vq];Bs=[Vq,U.T]
As=[U,X*Vq];dec=s.eye(16);dec.row_swap(0,13);dec[2,2]=-1
assert dec.H*dec==s.eye(16)
def contraction(a0,a1):
 out=s.zeros(16)
 for o,q,k,t in sections:
  g=o[0];x=w(o);source=t if g==0 else q;z=k if g==0 else t
  # scalar M/N/hub phases vary with their real native branch labels
  phase=(-1)**(record(o)+g+q+k)
  for p in product([0,1],repeat=4):
   c=phase*s.prod(labs[i][x[i]][o[i],p[i]] for i in range(3))
   c*=Ts[g][source,p[3]]*(a0 if g==0 else a1)[k,q]
   c*=Bs[0][q,t] if g==0 else Bs[1][t,k]
   out[2*record(o)+z,8*p[0]+4*p[1]+2*p[2]+p[3]]+=c
 return (dec*out).applyfunc(s.expand)
F=contraction(I,I);assert (F.H*F-s.eye(16)).applyfunc(s.expand)==s.zeros(16)
mark=contraction(I,s.zeros(2));P=(F.H*mark).applyfunc(s.expand)
assert P.H==P and (P**2-P).applyfunc(s.expand)==s.zeros(16) and s.trace(P)==8
G0=contraction(As[0],As[0]);G1=contraction(As[1],As[1]);lift=contraction(*As)
assert (lift-G0*P-G1*(s.eye(16)-P)).applyfunc(s.expand)==s.zeros(16)
assert (lift.H*lift-s.eye(16)).applyfunc(s.expand)==s.zeros(16)
assert all((F.H*G*P-P*F.H*G).applyfunc(s.expand)==s.zeros(16) for G in [G0,G1])
# Literal time reversal exchanges full forward/reverse domains, reverses
# every solid edge, and exchanges the colors of reversed dashed edges.
# Check its recurrent components too, so both loop colors are calibrated.
def reversed_cycles(edges):
 rev={(b,a,{'green':'red','red':'green','solid':'solid'}[color]) for a,b,color in edges}
 nodes={a for a,b,c in rev}|{b for a,b,c in rev};reach={n:{n} for n in nodes}
 for a,b,c in rev:reach[a].add(b)
 for k in nodes:
  for a in nodes:
   if k in reach[a]:reach[a]|=reach[k]
 comps={frozenset(b for b in nodes if a in reach[b] and b in reach[a]) for a in nodes};cyclic=[]
 for comp in comps:
  ee=[e for e in rev if e[0] in comp and e[1] in comp]
  if len(comp)>1 or any(a==b for a,b,c in ee):
   colors={c for a,b,c in ee};assert colors=={'red'}
   cyclic.append({'nodes':[list(n) for n in sorted(comp)],'colors':sorted(colors)})
 assert cyclic
 return cyclic
reverse_report={'old_forward_choices':old['reverse_complete_choices'],'new_forward_choices':new['reverse_complete_choices'],
 'old_reverse_choices':old['forward_complete_choices'],'new_reverse_choices':new['forward_complete_choices'],
 'old_cyclic_components':reversed_cycles(oldedges),'new_cyclic_components':reversed_cycles(newedges),'weak_loops_pass':True}
out={'status':'PASS','boundary_dimension':16,'calibration':'Lugano feedback controls the B-before/after-A data segment; all dormant native choices retained','old':old,'refined':new,'time_reversed_calibration':reverse_report,'section_forgetting_bijection':True,'conditional_choice_formula_both_directions':True,'bidirectional_selector_independence':True,'new_dependency_edges_classified':extra,'full_native_routes_dimension_balanced':True,'marked_contraction_identity_exact':True,'marked_input_projection_rank':8,'new_tensor_unitary_at_exact_rational_test':True,'scope':'Actual nontrivial cyclic route calibration and exact tensor check of the proposed graph rewrite, not a quartet host.'}
(ROOT/'branch_flag_loop_cyclic_calibration_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2),flush=True)
