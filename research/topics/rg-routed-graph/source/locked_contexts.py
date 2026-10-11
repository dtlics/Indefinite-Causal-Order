from context_closure import *
if __name__=='__main__':
 for i in range(4):
  edges=[ij for ij in choices if i in ij and ij!=(2,3)]
  for bits in product(range(2),repeat=len(edges)):
   ps={e:(I16-choices[e][bit] if e[0]!=i else choices[e][bit]) for e,bit in zip(edges,bits)}
   row=[remove(i,p) for p in ps.values()];mats=list(row)
   for e,p in ps.items():
    j=next(j for j in e if j!=i)
    for c in origins:
     v=transport(i,j,p,c)
     mats += [(v.H*q*v).applyfunc(s.expand) for q in row]
   bs=cb(mats);cs=simple_components(bs)
   print('LOCKED',i+1,bits,'dim',len(bs),'profile',sorted((n,int(s.trace(p))) for n,p in cs),flush=True)
