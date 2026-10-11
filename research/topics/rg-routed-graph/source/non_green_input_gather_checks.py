"""Exact split-layer input gather; red/acyclic positive, green negative."""
from pathlib import Path
from itertools import product
import json

ROOT=Path(__file__).parent
BITS=list(product((0,1),repeat=3))
LABS=[('L',i,x) for i,x in product(range(3),(0,1))]
P=('P',); F=('F',)
def w(o):
 a,b,c=o
 return b*(1-c),(1-a)*c,a*(1-b)
def lab_st(o):
 return {('L',i,w(o)[i]) for i in range(3)}
choice={}
for q in product((0,1),repeat=6):
 sol=[o for o in BITS if all(o[i]==q[2*i+w(o)[i]] for i in range(3))]
 assert len(sol)==1
 choice[q]=sol[0]

def components(nodes,edges):
 reach={a:{a} for a in nodes}
 for a,b,_ in edges: reach[a].add(b)
 for k in nodes:
  for a in nodes:
   if k in reach[a]: reach[a]|=reach[k]
 return {frozenset(b for b in nodes if b in reach[a] and a in reach[b]) for a in nodes}
def cyclic_colors(nodes,edges):
 out=[]
 for cc in components(nodes,edges):
  ins=[e for e in edges if e[0] in cc and e[1] in cc]
  if len(cc)>1 or any(a==b for a,b,_ in ins):
   out.append((cc,{c for _,_,c in ins}))
 return out

def audit_reverse(tapped=(2,),flagged=(0,)):
 # Actual reverse Lugano: each lab input is the scalar tuple (x_i,o_i).
 # Losing lab branches form one red SCC; winning siblings are acyclic.
 def label(o):
  return tuple((i,w(o)[i],o[i]) for i in tapped)+tuple(('flag',i,w(o)[i]) for i in flagged)
 def st(o): return {P,F,('H',*o),*lab_st(o),('A',label(o))}
 edges=set()
 for o,p in product(BITS,repeat=2):
  for b in st(o)^st(p): edges.add((P,b,'green'))
 for q,o in choice.items():
  for i,c in enumerate(LABS):
   qq=list(q);qq[i]^=1
   for b in st(o)^st(choice[tuple(qq)]): edges.add((b,c,'red'))
 cond={}
 def wire(e,a,b,val,dim=1): cond.setdefault((e,a,b),set()).add((val,dim))
 for o in BITS:
  h=('H',*o);aa=('A',label(o));xx=w(o)
  wire('ph',P,h,o);wire('hf',h,F,0)
  for i in range(3):
   ll=('L',i,xx[i]);wire(('lh',i),ll,h,xx[i])
   if i in tapped:
    wire(('ha',i),h,aa,(xx[i],o[i]));wire(('al',i),aa,ll,(xx[i],o[i]))
   else: wire(('hl',i),h,ll,(xx[i],o[i]))
   if i in flagged:
    wire(('la_flag',i),ll,aa,xx[i]);wire(('al_flag',i),aa,ll,xx[i])
 assert all(len(vals)==1 and next(iter(vals))[1]==1 for vals in cond.values())
 nodes=set().union(*(st(o) for o in BITS))
 cyc=cyclic_colors(nodes,edges)
 assert cyc==[(frozenset(('L',i,0) for i in range(3)),{'red'})]
 assert all(frozenset([n]) in components(nodes,edges) for n in nodes if n[0]=='A')
 # Any record using a winning tuple is the same event with or without
 # the other lab's losing-status flag: winning events are exclusive.
 for o in BITS:
  if w(o)[tapped[0]]==1:
   assert all(w(o)[i]==0 for i in flagged)
 pats=set(map(label,BITS))
 # Projection certificate in normalized boundary coordinates.
 vectors={p:tuple(int(label(o)==p) for o in BITS) for p in pats}
 assert all(sum(v[k] for v in vectors.values())==1 for k in range(8))
 return {'sections':8,'forward_choices':8,'reverse_choices':len(choice),
  'native_vertex_split_between_red_and_acyclic':True,
  'record_branches':len(pats),'record_ranks':sorted(sum(v) for v in vectors.values()),
  'joint_input_and_status_record':True,'red_SCC_preserved':True,'new_solid_edges':0}

def audit_forward_negative():
 # Forward Lugano branch input has one M2 sector (x_i); gathering it
 # introduces an M2 identity branch. Its outgoing solid edge makes the
 # old recurrent-green status loop strong, exactly the excluded case.
 j=2
 def st(o): return {P,F,('H',*o),*lab_st(o),('A',w(o)[j])}
 edges=set()
 for q,o in choice.items():
  for i,c in enumerate(LABS):
   qq=list(q);qq[i]^=1
   for b in st(o)^st(choice[tuple(qq)]): edges.add((c,b,'green'))
 for o,p in product(BITS,repeat=2):
  for b in st(o)^st(p): edges.add((b,F,'red'))
 for x in (0,1): edges.add((('A',x),('L',j,x),'solid'))
 nodes=set().union(*(st(o) for o in BITS))
 bad=[(cc,col) for cc,col in cyclic_colors(nodes,edges) if 'solid' in col]
 assert len(bad)==1 and ('A',0) in bad[0][0]
 return {'excluded_recurrent_green_case_fails':True,
  'bad_cycle_colors':sorted(bad[0][1]),'bad_SCC':sorted(bad[0][0],key=str)}

out={'status':'PASS','reverse_split_vertex':audit_reverse(),
 'all_reverse_inputs':audit_reverse((0,1,2),()),
 'forward_negative_control':audit_forward_negative(),
 'scope':'Exact cyclic calibration only. General non-green gather proof requires independent review.'}
(ROOT/'non_green_input_gather_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
