"""Exact coefficient helpers. Importing this file does not run a certificate."""
from context_closure import *

def F(xs):
 W=tensor(xs);D=I16+sum(((local(k,Z)-I16)*E[k] for k in range(4)),s.zeros(16))
 return (W+sum(((local(k,Z)-I16)*W*E[k] for k in range(4)),s.zeros(16)))*D

def embed(i,a,b):
 out=s.zeros(16)
 for r,x in enumerate(WORDS):
  rr=sum(x[k]<<(2-list(j for j in range(4) if j!=i).index(k)) for k in range(4) if k!=i)
  for c,y in enumerate(WORDS):
   cc=sum(y[k]<<(2-list(j for j in range(4) if j!=i).index(k)) for k in range(4) if k!=i)
   out[r,c]=a[x[i],y[i]]*b[rr,cc]
 return R[i]*out*R[i]
