from context_closure import *
from exact_m6_exclusion import F

def embed(i,a,b):
 out=s.zeros(16)
 for r,x in enumerate(WORDS):
  rr=sum(x[k]<<(2-list(j for j in range(4) if j!=i).index(k)) for k in range(4) if k!=i)
  for c,y in enumerate(WORDS):
   cc=sum(y[k]<<(2-list(j for j in range(4) if j!=i).index(k)) for k in range(4) if k!=i)
   out[r,c]=a[x[i],y[i]]*b[rr,cc]
 return R[i]*out*R[i]

def lr(i,ps,xs,order):
 U=tensor(xs);V=I16
 for j in order:
  c=local(j,xs[j]);v=c.H*(ps[j]+(I16-ps[j])*R[j]*c*R[j]);V=(v*V).applyfunc(s.expand)
 return (U*V).applyfunc(s.expand),(V.H*U.H*F(xs)).applyfunc(s.expand)

def kernel(i,q):
 j=5-i;edges=[e for e in choices if i in e and e!=(2,3)]
 ps={next(k for k in e if k!=i):I16-choices[e][0] for e in edges}
 pp=envelopes[2,3][1]+tensor([q,s.diag(1,0),I2,I2]);ps[j]=pp if i==2 else I16-pp
 row=[remove(i,ps[k]) for k in [0,1]];mats=list(row)+[remove(i,ps[j])]
 for k,p in ps.items():
  for c in origins:
   v=transport(i,k,p,c);mats += [(v.H*a*v).applyfunc(s.expand) for a in row]
 bs=cb(mats);print('INITIAL',i+1,'q',q.tolist(),'dim',len(bs),flush=True)
 order=[j,0,1];units=[s.diag(1,0),s.Matrix([[0,1],[0,0]]),s.diag(0,1),s.Matrix([[0,0],[1,0]])]
 for vary in order:
  for axis in [X,Y,Z]:
   for idx in product(range(4),repeat=2):
    xs=[I2]*4
    for k,t in zip([k for k in order if k!=vary],idx):xs[k]=[I2,X,Y,Z][t]
    triples=[]
    for c in [(3*I2+4*s.I*axis)/5,I2,axis]:
     xs[vary]=c;triples.append(lr(i,ps,xs,order))
    for a in units:
     aa=[embed(i,a,b) for b in bs]
     defects=[]
     for A in aa:
      vals=[l*A*r for l,r in triples];defects.append((vals[0]-(3*vals[1]+4*s.I*vals[2])/5).applyfunc(s.expand).reshape(256,1))
     ns=s.Matrix.hstack(*defects).nullspace()
     if len(ns)<len(bs):
      bs=[sum((v[k]*bs[k] for k in range(len(bs))),s.zeros(8)) for v in ns]
      print('DROP','vary',vary+1,'axis',[X,Y,Z].index(axis),'others',idx,'dim',len(bs),flush=True)
    if len(bs)<=2:break
   if len(bs)<=2:break
  if len(bs)<=2:break
 print('FINAL',i+1,'q',q.tolist(),'dim',len(bs),'commutative',all(a*b==b*a for a in bs for b in bs),flush=True)
 for b in bs:print('BASIS',b.tolist(),flush=True)
 return bs
if __name__=='__main__':
 for i,q in [(2,s.zeros(2)),(2,s.ones(2)/2),(2,s.diag(1,0)),(2,s.diag(0,1)),(2,s.Matrix([[9,12],[12,16]])/25)]:kernel(i,q)
