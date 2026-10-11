from context_closure import *
import json

def coefficient_nullspace(bs,mats):
 for a in mats:
  V=s.Matrix.hstack(*[((a*b-b*a).applyfunc(s.expand)).reshape(64,1) for b in bs])
  ns=V.nullspace()
  bs=[sum((v[k]*bs[k] for k in range(len(bs))),s.zeros(8)) for v in ns]
 return bs

if __name__=='__main__':
 records=[]
 for i in [2,3]:
  edges=[ij for ij in choices if i in ij and ij!=(2,3)]
  for bits in product(range(2),repeat=len(edges)):
   ps={next(j for j in e if j!=i):(I16-choices[e][bit] if e[0]!=i else choices[e][bit]) for e,bit in zip(edges,bits)}
   row=[remove(i,p) for p in ps.values()];mats=list(row)
   vs={j:[transport(i,j,p,c) for c in origins] for j,p in ps.items()}
   for j, vv in vs.items():
    for v in vv:mats += [(v.H*q*v).applyfunc(s.expand) for q in row]
   bs=cb(mats)
   for j,k in combinations(ps,2):
    for v,w in product(vs[j],vs[k]):
     vw=(v*w).applyfunc(s.expand);wv=(w*v).applyfunc(s.expand)
     hol=(wv.H*vw).applyfunc(s.expand)
     extra=[hol]+[(vw.H*q*vw).applyfunc(s.expand) for q in row]
     bs=coefficient_nullspace(bs,extra)
   cs=simple_components(bs)
   profile=sorted((n,int(s.trace(p))) for n,p in cs)
   print('HOLONOMY',i+1,bits,'dim',len(bs),'profile',profile,flush=True)
   for n,p in cs:
    if n>1:print('CARRIER',n,p.tolist(),flush=True)
   records.append({'query':i+1,'bits':bits,'dim':len(bs),'profile':profile})
 with open(Path(__file__).with_name('holonomy_contexts.json'),'w') as f:json.dump(records,f,indent=2)
