"""Exact full-input record rewrite on WHOLE red-SCC lab vertices."""
from pathlib import Path
from itertools import product
import json
import sympy as s
ROOT=Path(__file__).parent
BITS=list(product((0,1),repeat=3));SH=[(0,0,0),(1,0,0),(0,1,0),(0,0,1)]
P=('P',);F=('F',)
def w(o):
 a,b,c=o;return (b*(1-c),(1-a)*c,a*(1-b))
def x(ss,o):return tuple(a^b for a,b in zip(w(o),SH[ss]))
def status(ss,o):return frozenset([P,F,('H',ss,*o),*(('L',i,x(ss,o)[i]) for i in range(3))])
SECS=list(product(range(4),BITS));LABS=[('L',i,b) for i,b in product(range(3),(0,1))]
reverse={}
for ss,f in product(range(4),product((0,1),repeat=6)):
 sol=[o for o in BITS if all(o[i]==f[2*i+x(ss,o)[i]] for i in range(3))]
 assert len(sol)==1;reverse[ss,*f]=(ss,sol[0])

def label(ss,o,tapped,flagged):
 return tuple((i,x(ss,o)[i],o[i]) for i in tapped)+tuple(('flag',i,x(ss,o)[i]) for i in flagged)

def audit(tapped=(),flagged=()):
 refined=bool(tapped or flagged)
 def st(sec):
  ss,o=sec;stt=set(status(ss,o))
  if refined:stt.add(('A',label(ss,o,tapped,flagged)))
  return frozenset(stt)
 edges=set()
 for a,b in product(SECS,repeat=2):
  for c in st(a)^st(b):edges.add((P,c,'green'))
 for vv,sec in reverse.items():
  for k,c in enumerate([F]+LABS):
   for val in range(4 if k==0 else 2):
    ww=list(vv);ww[k]=val
    for b in st(sec)^st(reverse[tuple(ww)]):edges.add((b,c,'red'))
 # Exact conditional wire values, all sectors one-dimensional.
 cond={}
 def wire(e,a,b,val):cond.setdefault((e,a,b),set()).add((val,1))
 for ss,o in SECS:
  xx=x(ss,o);h=('H',ss,*o);aa=('A',label(ss,o,tapped,flagged))
  wire('ph',P,h,(ss,o));wire('hf',h,F,ss)
  for i in range(3):
   ll=('L',i,xx[i]);wire(('lh',i),ll,h,xx[i])
   if i in tapped:
    wire(('ha',i),h,aa,(xx[i],o[i]));wire(('al',i),aa,ll,(xx[i],o[i]))
   else:wire(('hl',i),h,ll,(xx[i],o[i]))
   if i in flagged:
    wire(('la_flag',i),ll,aa,xx[i]);wire(('al_flag',i),aa,ll,xx[i])
 assert all(len(v)==1 and next(iter(v))[1]==1 for v in cond.values())
 nodes=set().union(*(st(sec) for sec in SECS));reach={a:{a} for a in nodes}
 for a,b,col in edges:reach[a].add(b)
 for k in nodes:
  for a in nodes:
   if k in reach[a]:reach[a]|=reach[k]
 comps={frozenset(b for b in nodes if b in reach[a] and a in reach[b]) for a in nodes}
 cycles=[]
 for cc in comps:
  inside=[e for e in edges if e[0] in cc and e[1] in cc]
  if len(cc)>1 or any(a==b for a,b,col in inside):
   assert {col for a,b,col in inside}=={'red'};cycles.append(cc)
 assert cycles==[frozenset(LABS)]
 if refined:
  assert all(a==P for a,b,col in edges if b[0]=='A' and col=='green')
  assert all(b in set(LABS)|{F} for a,b,col in edges if a[0]=='A' and col=='red')
  assert all(frozenset([a]) in comps for a in nodes if a[0]=='A')
  assert not any(a[0]=='A' and col=='green' or b[0]=='A' and col=='red' for a,b,col in edges)
 pats=sorted(set(label(ss,o,tapped,flagged) for ss,o in SECS),key=str) if refined else []
 Ps=[s.diag(*(int(label(ss,o,tapped,flagged)==p) for ss,o in SECS)) for p in pats]
 if refined:
  assert sum(Ps,s.zeros(32))==s.eye(32)
  assert all(q*q==q and q.H==q for q in Ps)
  for i in flagged:
   Q=s.diag(*(int(x(ss,o)[i]==1) for ss,o in SECS))
   for j in tapped:
    for branch,bit in product((0,1),repeat=2):
     D=s.diag(*(int(x(ss,o)[j]==branch and o[j]==bit) for ss,o in SECS))
     assert Q*D==D*Q
 return {'tapped_whole_vertices':tapped,'status_flag_vertices':flagged,'forward_choices':32,
  'reverse_choices':len(reverse),'sections':32,'native_branches':len(nodes),'record_branches':len(pats),
  'record_ranks':[int(q.trace()) for q in Ps],'green_edges':sum(c=='green' for a,b,c in edges),
  'red_edges':sum(c=='red' for a,b,c in edges),'solid_edges':0,'six_branch_red_SCC_unchanged':True,
  'choice_and_section_bijections':True,'coarse_status_and_input_tuple_markers_commute':True},edges
old,oe=audit();whole,we=audit((0,1,2));combined,ce=audit((2,),(0,))
for ee in (we,ce):assert {e for e in ee if e[0][0]!='A' and e[1][0]!='A'}==oe
assert whole['record_branches']==32 and set(whole['record_ranks'])=={1}
out={'status':'PASS','boundary_dimension':32,'old':old,'whole_input_record':whole,
 'combined_one_input_and_one_status_record':combined,
 'scope':'Actual whole-red-SCC full-input scalar record rewrites. No conditional tapping of a split native vertex is tested or inferred.'}
(ROOT/'branch_red_full_input_record_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
