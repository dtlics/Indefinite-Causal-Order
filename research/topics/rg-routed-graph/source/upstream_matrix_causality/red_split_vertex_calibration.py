"""Exact full-matrix red-SCC calibration with genuinely split native vertices.

A coherent direct sum of controlled Lugano and a 32-dimensional bypass,
with full M64 source/sink caps. Reverse it. Every lab has two active M2
branches and a scalar bypass sibling. The scalar hub has 32 active scalar
branches and an M32 bypass sibling. Source query is U2 tensor I32 on M64.
"""
from itertools import product
from pathlib import Path
import json
import sympy as s
ROOT=Path(__file__).parent
BITS=list(product((0,1),repeat=3));SHIFTS=[(0,0,0),(1,0,0),(0,1,0),(0,0,1)]
def w(o): a,b,c=o; return (b*(1-c),(1-a)*c,a*(1-b))
def xx(t,o): return tuple(a^b for a,b in zip(w(o),SHIFTS[t]))
def idx(o):return 4*o[0]+2*o[1]+o[2]
E=('E',);Z=('Z',);S=('S',1);S0=('S',0);D=('D',1);D0=('D',0);H0=('H',0)
LABS=[('L',i,x) for i,x in product(range(3),(0,1))]
LAB0=[('L0',i) for i in range(3)]
HUBS=[('H',1,t,*o) for t,o in product(range(4),BITS)]
NODES=[E,Z,S,S0,D,D0,H0]+LABS+LAB0+HUBS

def status(sec):
    if sec is None:return frozenset([E,Z,S0,D0,H0,*LAB0])
    t,o=sec
    return frozenset([E,Z,S,D,('H',1,t,*o),*(('L',i,x) for i,x in enumerate(xx(t,o)))])

def vertex(a):
    if a[0]=='L':return ('L',a[1])
    if a[0]=='L0':return ('L',a[1])
    return a[0]
forward={}
for m,t,f in product((0,1),range(4),product((0,1),repeat=6)):
    sol=[o for o in BITS if all(o[i]==f[2*i+xx(t,o)[i]] for i in range(3))]
    assert len(sol)==1
    forward[(m,t,*f)]=(t,sol[0]) if m else None
edges=set()
for q,sec in forward.items():
    for k,source,values in [(0,E,range(2)),(1,S,range(4)),*[(j+2,b,range(2)) for j,b in enumerate(LABS)]]:
        for z in values:
            r=list(q);r[k]=z
            for a in status(sec)^status(forward[tuple(r)]):edges.add((source,a,'green'))
reverse={(m,t,*o):((t,o) if m else None) for m,t,o in product((0,1),range(4),BITS)}
for q,sec in reverse.items():
    for m in range(2):
        for a in status(sec)^status(reverse[(m,*q[1:])]):edges.add((a,Z,'red'))
    for t,o in product(range(4),BITS):
        for a in status(sec)^status(reverse[(q[0],t,*o)]):edges.add((a,D,'red'))
# The only nontrivial physical sectors are source quantum payloads and sink
# payloads. All active hub links have a fixed scalar index at each pair.
solid={(E,S),(E,H0),(D,Z),(H0,Z),*[(E,b) for b in LABS]}
for a,b in solid:edges.add((a,b,'solid'))
reach={a:{a} for a in NODES}
for a,b,col in edges:reach[a].add(b)
for k in NODES:
    for a in NODES:
        if k in reach[a]:reach[a]|=reach[k]
comps={frozenset(b for b in NODES if b in reach[a] and a in reach[b]) for a in NODES}
cyclic=[cc for cc in comps if len(cc)>1]
assert cyclic==[frozenset(LABS)]
assert {col for a,b,col in edges if a in LABS and b in LABS}=={'green'}
assert set().union(*(status(sec) for sec in forward.values()))==set(NODES)
b=LABS[0]
A=reach[b] # ancestors of b in reverse host
assert E not in A and all(a in A for a in LABS)
assert H0 not in A and any(h in A for h in HUBS)
assert D in A and D0 not in A
assert b in A and LAB0[0] not in A
for a,c,col in edges: # reverse edge c->a cannot enter A from outside
    assert not(c not in A and a in A)

R=s.Matrix([[3,-4],[4,3]])/5
SS=s.kronecker_product(R,R.T)
base={(i,x):R**(1+2*i+x) for i,x in product(range(3),(0,1))}
h={(t,o):s.Integer((-1)**((t+idx(o))%3)) for t,o in product(range(4),BITS)}

def module(changes={},marks=[]):
    uu=dict(base);uu.update(changes)
    return s.Matrix(32,32,lambda a,p: h[a//8,BITS[a%8]]*SS[a//8,p//8]*s.prod(uu[i,xx(a//8,BITS[a%8])[i]][BITS[a%8][i],BITS[p%8][i]] for i in range(3)) if all(x==xx(a//8,BITS[a%8])[i] for i,x in marks) else 0)
M=module();assert M.T*M==s.eye(32)
# Nontrivial pinned native bypass sibling, preserving its full M32 freedom.
H=s.zeros(32)
for j in range(32):H[(5*j+3)%32,j]=1
G0=s.diag(H,M)
assert G0.T*G0==s.eye(64)
units=[s.Matrix(2,2,lambda k,l:int((k,l)==(i,j))) for i,j in product(range(2),repeat=2)]
query=[s.kronecker_product(x,s.eye(32)) for x in units]
checks=0; ranks={}
Fs=[G0*U*G0.T for U in query]
print("Route and baseline unitary checks PASS",flush=True)
for lab in LABS[:1]:
    _,i,x=lab
    Mmark=module(marks=[(i,x)])
    Q=G0*s.diag(s.zeros(32),Mmark.T)
    assert Q.T==Q and Q*Q==Q
    ranks[str(lab)]=int(s.trace(Q))
    for aa in units:
        # Reverse filler baseline is base.T, so its u0*a corresponds in the
        # original forward host to a.T*base.
        Mb=module({(i,x):aa.T*base[i,x]},[(i,x)])
        B=s.diag(s.zeros(32),Mb.T)
        beta=G0*B
        for U,F in zip(query,Fs):
            # Query E_reverse uses U tensor I32, baseline identity.
            marked=G0*U*B
            assert marked==F*beta
            checks+=1
            print("matrix-unit check",checks,flush=True)
# Reachable-pair negative control: wrongly asserting reverse order for
# another active branch in the same red SCC must fail in some basis pair.
neg=None
for aa,cc in product(units,repeat=2):
    bkey=(0,0);ckey=(1,0)
    Mb=module({bkey:aa.T*base[bkey]},[bkey])
    Mc=module({ckey:cc.T*base[ckey]},[ckey])
    Mbc=module({bkey:aa.T*base[bkey],ckey:cc.T*base[ckey]},[bkey,ckey])
    defect=M*Mbc.T-(M*Mc.T)*(M*Mb.T)
    if defect!=s.zeros(32):neg=str(s.trace(defect.T*defect));break
assert neg is not None
out={'status':'PASS','boundary_dimension':64,'full_forward_choice_count':len(forward),'full_reverse_choice_count':len(reverse),'globally_reachable_branches':len(NODES),'forward_cyclic_component_size':6,'reverse_cyclic_component_color':'red','ancestral_downset_size':len(A),'split_native_vertices':[str(v) for v in sorted({vertex(a) for a in A}&{vertex(a) for a in set(NODES)-A},key=str)],'marked_branch_rank':ranks,'native_marked_branch_dimension':2,'representation_multiplicity':{k:v//2 for k,v in ranks.items()},'exact_native_matrix_unit_identities':checks,'original_query_native_dimension':64,'original_query_inclusion':'M2 tensor I32','red_same_SCC_negative_control_squared_HS_defect':neg}
(ROOT/'red_split_vertex_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2),flush=True)
