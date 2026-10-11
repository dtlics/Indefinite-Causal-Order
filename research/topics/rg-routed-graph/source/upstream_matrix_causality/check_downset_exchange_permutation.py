"""Exact standard-library calibration of all-exchange downset quantum closure.

The literal binary Lugano host includes all six M2 lab branches, the eight
scalar hub branches, and the M8 decoder.  Both orientations are tested.
We test every full matrix-unit generator, not merely basis-state signalling.
"""
from itertools import product
from pathlib import Path
import json
BITS=list(product((0,1),repeat=3))
LABS=[('L',i,x) for i,x in product(range(3),(0,1))]
D=('D',)
HUBS=[('H',*o) for o in BITS]
NODES=LABS+HUBS+[D]
NONTRIVIAL=LABS+[D]
DIMS=[8]+[2]*6+[8]
def w(o):
 a,b,c=o
 return b*(1-c),(1-a)*c,a*(1-b)
def status(o):return {D,('H',*o),*(('L',i,w(o)[i]) for i in range(3))}
fwd={}
for f in product((0,1),repeat=6):
 sol=[o for o in BITS if all(o[i]==f[2*i+w(o)[i]] for i in range(3))]
 assert len(sol)==1
 fwd[f]=sol[0]
edges=set()
for f,o in fwd.items():
 for k,b in enumerate(LABS):
  ff=list(f);ff[k]^=1
  for c in status(o)^status(fwd[tuple(ff)]):edges.add((b,c,'green'))
for o,p in product(BITS,repeat=2):
 for b in status(o)^status(p):edges.add((b,D,'red'))
# Each co-occurring original physical link has a singleton scalar sector,
# so there are no solid edges. This includes L_i->H_o, H_o->L_i and H_o->D.
inputs=list(product(*(range(d) for d in DIMS)))
T={}
for z in inputs:
 p,f,d=BITS[z[0]],z[1:7],z[7]
 o=fwd[f];s=w(o)
 lab=tuple(p[i] if x==s[i] else f[2*i+x] for i,x in product(range(3),(0,1)))
 T[z]=(d,*lab,BITS.index(o))
assert len(T)==4096 and len(set(T.values()))==4096
Tinv={v:k for k,v in T.items()}

def closure(reverse=False):
 reach={b:{b} for b in NODES}
 for a,b,col in edges:
  if reverse:a,b=b,a
  reach[a].add(b)
 for k in NODES:
  for b in NODES:
   if k in reach[b]:reach[b]|=reach[k]
 return reach

checks=[]
def check(A,b,perm,inv,active=None):
 # Generator E_ij acts on the output exchange input of branch b.
 # Its pullback is a partial permutation. Compare it for every R basis.
 pos=1+NONTRIVIAL.index(b)
 apos=[0]+[1+i for i,c in enumerate(NONTRIVIAL) if c in A]
 rpos=[1+i for i,c in enumerate(NONTRIVIAL) if c not in A]
 data={}
 for z in inputs:
  out=perm[z];j=out[pos]
  key=tuple(z[k] for k in apos)
  r=tuple(z[k] for k in rpos)
  if active is not None and not active(z):
   signature=('inactive',)
   if key in data and data[key]!=signature:
    return {'pass':False,'reason':'active support depends on outside factor','branch':b,'input':z}
   data[key]=signature
   continue
  value=[]
  for i in range(DIMS[pos]):
   changed=list(out);changed[pos]=i
   zz=inv[tuple(changed)]
   if tuple(zz[k] for k in rpos)!=r:
    return {'pass':False,'reason':'off-diagonal matrix unit changes R output','branch':b,'i':i,'j':j,'input':z}
   value.append(tuple(zz[k] for k in apos))
  signature=(j,tuple(value))
  if key in data and data[key]!=signature:
   return {'pass':False,'reason':'matrix-unit pullback depends on R output','branch':b,'input':z}
  data[key]=signature
 return {'pass':True,'branch':b,'downset':sorted(A),'exchange_dimension':4096,
         'matrix_units':DIMS[pos]**2,'full_domain_inputs_checked':len(inputs)}

for reverse in (False,True):
 perm,inv=(Tinv,T) if reverse else (T,Tinv)
 reach=closure(reverse)
 for b in NONTRIVIAL:
  A={c for c in NODES if b in reach[c]}
  result=check(A,b,perm,inv)
  assert result['pass'],result
  result['orientation']='reverse' if reverse else 'forward'
  checks.append(result)
red_checks=[]
reach=closure(True)
for b in LABS[::2]:
 K={c for c in NODES if b in reach[c] and c!=b}
 result=check(K,b,Tinv,T,active=lambda z,b=b: b in status(BITS[z[7]]))
 assert result['pass'],result
 red_checks.append(result)
# Matrix algebras for branches generate each arbitrary downset algebra.
# It therefore suffices to check the minimal ancestral downset for each b.
negative=check({LABS[0]},LABS[0],Tinv,T)
assert not negative['pass']
out={'status':'PASS','full_all_exchange_dimension':4096,'all_forward_choices':64,
     'all_reverse_choices':8,'full_reachable_branches':15,'checks':checks,
     'minimal_downset_checks':len(checks),'red_active_full_past_checks':red_checks,'matrix_units_checked':sum(x['matrix_units'] for x in checks),
     'input_generator_actions_checked':sum(x['full_domain_inputs_checked']*int(x['matrix_units']**0.5) for x in checks),
     'negative_control_non_downset_reverse_losing_singleton':negative,
     'scope':'Exact finite calibration, with every matrix unit tested. The general result requires the proof.'}
path=Path(__file__).with_name('downset_exchange_permutation_checks.json')
path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
