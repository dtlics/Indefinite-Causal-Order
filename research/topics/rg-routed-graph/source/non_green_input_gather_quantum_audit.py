"""Independent literal route audit: split red/acyclic labs, quantum winner inputs.

This constructs local rectangular routes, enumerates every internal assignment,
then independently evaluates both complete choice functions and Definition 3.6
solid edges. No precomputed section map is assumed. The example is a modified
reverse Lugano graph with a genuinely quantum M2 winning-sector hub.
"""
from pathlib import Path
from itertools import product
from collections import defaultdict
import json
import sympy as s
ROOT=Path(__file__).parent
BITS=list(product((0,1),repeat=3))
def w(o):
 a,b,c=o
 return b*(1-c),(1-a)*c,a*(1-b)
def num(o):return 4*o[0]+2*o[1]+o[2]
def hsector(o,i):return 2 if w(o)[i] else o[i]

class Route:
 def __init__(self):
  self.edges={};self.local={};self.extin={};self.extout={}
 def edge(self,name,src,dst,dims):self.edges[name]=(src,dst,tuple(dims))
 def branch(self,v,name,ins,outs):
  # Tuples are dictionaries; their keys give the actual physical wires.
  self.local.setdefault(v,{})[(v,name)]=(tuple(ins),tuple(outs))
 def finalize(self):
  self.inedges={v:tuple(e for e,(a,b,_) in self.edges.items() if b==v) for v in self.local}
  self.outedges={v:tuple(e for e,(a,b,_) in self.edges.items() if a==v) for v in self.local}
  self.branches={};self.native_dims={}
  for v,bs in self.local.items():
   usedin=set();usedout=set()
   for name,(ins,outs) in bs.items():
    ii=tuple(tuple(z[e] for e in self.inedges[v]) for z in ins)
    oo=tuple(tuple(z[e] for e in self.outedges[v]) for z in outs)
    assert len(set(ii))==len(ii) and len(set(oo))==len(oo)
    assert not usedin.intersection(ii) and not usedout.intersection(oo)
    usedin.update(ii);usedout.update(oo)
    din=sum(s.prod(self.edges[e][2][val] for e,val in zip(self.inedges[v],t)) for t in ii)*self.extin.get(v,1)
    dout=sum(s.prod(self.edges[e][2][val] for e,val in zip(self.outedges[v],t)) for t in oo)*self.extout.get(v,1)
    assert din==dout and din>0,(name,din,dout)
    self.native_dims[name]=int(din);self.branches[name]=(ii,oo)
  return self
 def sections(self):
  edges=tuple(self.edges);out=[]
  for values in product(*(range(len(self.edges[e][2])) for e in edges)):
   vals=dict(zip(edges,values));st={};ok=True
   for v,bs in self.local.items():
    it=tuple(vals[e] for e in self.inedges[v]);ot=tuple(vals[e] for e in self.outedges[v])
    found=[b for b in bs if it in self.branches[b][0] and ot in self.branches[b][1]]
    if len(found)!=1:ok=False;break
    st[v]=found[0]
   if ok:out.append((vals,st))
  return out

def build(refined):
 r=Route();r.edge('p','P','H',[1]*8)
 for i in range(3):
  r.edge(f'b{i}',f'L{i}','H',[1,1])
  r.edge(f'h{i}','H','A' if refined and i==2 else f'L{i}',[1,1,2])
 if refined:
  r.edge('bundle','A','L2',[1,1,2]);r.edge('flag_to_A','L0','A',[1,1]);r.edge('flag_to_L','A','L0',[1,1])
 r.extin['P']=8;r.branch('P','all',[{}],[{'p':i} for i in range(8)])
 # All old o=000/111 hub branches are scalar; each one-hot winner pair
 # becomes one honest M2 branch, whose output contains a quantum2 sector.
 for pat in sorted(set(map(w,BITS))):
  os=[o for o in BITS if w(o)==pat]
  groups=[os] if sum(pat)==1 else [[o] for o in os]
  for group in groups:
   tag='winner'+str(pat.index(1)) if sum(pat)==1 else 'zero'+str(num(group[0]))
   ins=[dict(p=num(o),**{f'b{i}':pat[i] for i in range(3)}) for o in group]
   out={f'h{i}':hsector(group[0],i) for i in range(3)}
   assert all(out=={f'h{i}':hsector(o,i) for i in range(3)} for o in group)
   r.branch('H',tag,ins,[out])
 for i in range(3):
  r.extout[f'L{i}']=2;ie='bundle' if refined and i==2 else f'h{i}'
  for b in (0,1):
   ins=[{ie:v} for v in ((0,1) if b==0 else (2,))]
   outs=[{f'b{i}':b}]
   if refined and i==0:
    ins=[dict(z,flag_to_L=b) for z in ins];outs=[dict(z,flag_to_A=b) for z in outs]
   r.branch(f'L{i}',b,ins,outs)
 if refined:
  # Include every locally possible flag/h pair, even the unreachable
  # winner2/winner0 pair. Reachability reduction is checked independently.
  for h,f in product(range(3),range(2)):
   r.branch('A',(h,f),[{'h2':h,'flag_to_A':f}],[{'bundle':h,'flag_to_L':f}])
 return r.finalize()

def inspect(r):
 secs=r.sections();bs=tuple(r.branches);choice=[];edges=set()
 for rev in (False,True):
  side=0 if rev else 1
  domains=[r.branches[b][side] for b in bs];mapping={}
  for q in product(*domains):
   qc=dict(zip(bs,q));hits=[]
   for ix,(vals,st) in enumerate(secs):
    if all(qc[b]==tuple(vals[e] for e in (r.inedges[v] if rev else r.outedges[v])) for v,b in st.items()):hits.append(ix)
   assert len(hits)==1,('reverse' if rev else 'forward',q,hits)
   mapping[q]=hits[0]
  for q,ix in mapping.items():
   st=set(secs[ix][1].values())
   for k,b in enumerate(bs):
    for val in domains[k]:
     qq=list(q);qq[k]=val
     for a in st.symmetric_difference(secs[mapping[tuple(qq)]][1].values()):
      edges.add((a,b,'red') if rev else (b,a,'green'))
  choice.append(mapping)
 cond=defaultdict(set)
 for vals,st in secs:
  for e,(src,dst,dims) in r.edges.items():cond[e,st[src],st[dst]].add((vals[e],dims[vals[e]]))
 for (e,a,b),vals in cond.items():
  if len(vals)>1 or any(d>1 for _,d in vals):edges.add((a,b,'solid'))
 nodes=set().union(*(set(st.values()) for _,st in secs));reach={a:{a} for a in nodes}
 for a,b,_ in edges:reach[a].add(b)
 for k in nodes:
  for a in nodes:
   if k in reach[a]:reach[a]|=reach[k]
 comps={frozenset(b for b in nodes if b in reach[a] and a in reach[b]) for a in nodes}
 cycles=[]
 for cc in comps:
  ee={col for a,b,col in edges if a in cc and b in cc}
  if len(cc)>1 or any(a==b and a in cc for a,b,_ in edges):
   assert ee in ({'green'},{'red'}),(cc,ee)
   cycles.append((cc,ee))
 expected=frozenset((f'L{i}',0) for i in range(3))
 assert cycles==[(expected,{'red'})]
 assert all(frozenset([b]) in comps for b in nodes if b[0]=='A')
 return secs,choice,edges,nodes

old=build(False);new=build(True)
os,oc,oe,on=inspect(old);ns,nc,ne,nn=inspect(new)
assert len(os)==len(ns)==8
# Forgetting the new physical edges and branch gives an exact section
# bijection. Choice coordinates agree under the native input-tuple rename.
old_by_p={v['p']:(v,st) for v,st in os};new_by_p={v['p']:(v,st) for v,st in ns}
for p,(nv,nst) in new_by_p.items():
 ov,ost=old_by_p[p]
 assert {e:nv[e] for e in old.edges}==ov
 assert {v:b for v,b in nst.items() if v!='A'}==ost
for rev in (0,1):
 oldbranches=tuple(old.branches);newbranches=tuple(new.branches)
 om=oc[rev];nm=nc[rev]
 def tuple_map(graph,b,t):
  es=graph.inedges[b[0]] if rev else graph.outedges[b[0]]
  return {('h2' if e=='bundle' else e):val for e,val in zip(es,t) if not e.startswith('flag_')}
 canon_old={tuple(tuple(sorted(tuple_map(old,b,t).items())) for b,t in zip(oldbranches,q)):os[ix][0]['p'] for q,ix in om.items()}
 canon_new={tuple(tuple(sorted(tuple_map(new,b,dict(zip(newbranches,q))[b]).items())) for b in oldbranches):ns[ix][0]['p'] for q,ix in nm.items()}
 assert canon_old==canon_new
assert {e for e in ne if e[0][0]!='A' and e[1][0]!='A' and e[2]!='solid'}=={e for e in oe if e[2]!='solid'}
assert (('H','winner2'),('L2',1),'solid') in oe
assert (('H','winner2'),('A',(2,0)),'solid') in ne
assert (('A',(2,0)),('L2',1),'solid') in ne
assert not any(a[0]=='A' and c=='green' or b[0]=='A' and c=='red' for a,b,c in ne)
assert len([n for n in nn if n[0]=='A'])==4
assert ('A',(2,1)) not in nn
# Baseline coefficient projectors and status commutation, with an actual
# quantum M2 branch among A's independent native direct-sum summands.
labels={p:new_by_p[p][1]['A'] for p in range(8)}
projectors={b:s.diag(*(int(labels[p]==b) for p in range(8))) for b in nn if b[0]=='A'}
assert sum(projectors.values(),s.zeros(8))==s.eye(8)
assert all(P*Q==(P if b==c else s.zeros(8)) for b,P in projectors.items() for c,Q in projectors.items())
passive0=s.diag(*(int(w(o)[0]==0) for o in BITS))
for h in (0,1):
 D=sum((P for b,P in projectors.items() if b[1][0]==h),s.zeros(8))
 assert passive0*D==D*passive0

# An independent private qubit at A, with full noncommuting native quantum
# and scalar-branch operations, is calibrated exactly. Other native fillers
# vary independently, including H's M2 winner branches and all six lab M2s.
I=s.eye(2);X=s.Matrix([[0,1],[1,0]]);R=s.Matrix([[3,-4],[4,3]])/5
CNOT=s.Matrix([[1,0,0,0],[0,1,0,0],[0,0,0,1],[0,0,1,0]])
U={(i,b):[R,R.T,X,R*X,X*R,X*R.T][2*i+b] for i,b in product(range(3),(0,1))}
H={i:[R.T,X,R*X][i] for i in range(3)}
V=CNOT*s.kronecker_product(R,R.T)
A={(h,f):[R,X,R.T,R*X][2*h+f] for h,f in product(range(2),range(2))}
Psource=s.kronecker_product(R,X,R.T)
G=s.zeros(16)
# Internal P label p is fixed before composing arbitrary Psource on right.
for p,o in enumerate(BITS):
 pat=w(o);win=pat.index(1) if sum(pat) else None;hb=(hsector(o,2),pat[0])
 for y in BITS:
  for ai,ao in product(range(2),repeat=2):
   z=0
   if win==2:
    for q,t in product(range(2),repeat=2):
     z+=U[0,0][y[0],o[0]]*U[1,0][y[1],o[1]]*U[2,1][y[2],t]*V[2*t+ao,2*q+ai]*H[2][q,o[2]]
   else:
    z=A[hb][ao,ai]
    for i in range(3):
     z*=((U[i,1]*H[i])[y[i],o[i]] if win==i else U[i,0][y[i],o[i]])
   G[2*num(y)+ao,2*p+ai]=z
G=G*s.kronecker_product(Psource,I)
assert G.H*G==s.eye(16) and G*G.H==s.eye(16)
assert A[0,0]*A[0,1]!=A[0,1]*A[0,0]
assert V[:2,:2]*V[2:,:2]!=V[2:,:2]*V[:2,:2]

out={'status':'PASS','construction':'Reverse Lugano with quantum M2 winning-sector hubs',
 'local_route_rectangularity_and_native_dimension_balance':True,
 'sections_before':len(os),'sections_after':len(ns),
 'complete_forward_choices':len(oc[0]),'complete_reverse_choices':len(oc[1]),
 'all_dormant_coordinates_retained':True,'literal_section_and_choice_bijections':True,
 'old_native_algebras':{'P':'M8','H':'M2+M2+M2+C+C','labs':'(M2+M2)^3'},
 'new_reachable_record_algebra':'C+C+C+M2',
 'record_ranks':sorted(int(P.trace()) for P in projectors.values()),
 'old_solid_edges':sorted(oe.difference({e for e in oe if e[2]!='solid'}),key=str),
 'new_solid_edges':sorted(ne.difference({e for e in ne if e[2]!='solid'}),key=str),
 'red_losing_SCC_unchanged':True,'all_new_branches_acyclic':True,
 'winning_status_implies_other_lab_losing':True,
 'joint_quantum_and_scalar_branch_unit_projections':True,
 'joint_passive_status_and_scalar_input_commutation':True,
 'independent_A_private_ancilla_dimension':2,'exact_amplified_matrix_dimension':16,
 'independent_noncommuting_A_scalar_and_quantum_fillers':True,'exact_amplified_unitarity':True,
 'scope':'Finite independent calibration of actual local routes, including a quantum acyclic input subdivision. General completeness comes from the graph proof, not this single amplified test.'}
(ROOT/'non_green_input_gather_quantum_audit_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
