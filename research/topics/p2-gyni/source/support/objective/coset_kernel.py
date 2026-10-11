"""Outcome-resolved universal NS completion on dihedral left-coset words."""
import numpy as np

def reduce_word(seq):
 out=[]
 for x in seq:
  if out and out[-1]==x:out.pop()
  else:out.append(x)
 return tuple(out)

class CosetKernel:
 def __init__(self,L):
  self.L=L;self.n=L+1;self.s=self.n**2;n=self.n
  self.ws={x:[tuple((1-x+j)%2 for j in range(k)) for k in range(n)] for x in [0,1]}
  cols=[];allw=set()
  for x in [0,1]:
   for a in [0,1]:
    for i in range(n):
     for j in range(n):
      u,v=self.ws[x][i],self.ws[x][j];terms=[(reduce_word(tuple(reversed(v))+u),1),(reduce_word(tuple(reversed(v))+(x,)+u),(-1)**a)];cols.append(terms);allw.update(w for w,c in terms if w)
  self.overlaps=sorted(allw,key=lambda w:(len(w),w));ix={w:i for i,w in enumerate(self.overlaps)};M=np.zeros((len(ix),4*n*n))
  for j,terms in enumerate(cols):
   for w,c in terms:
    if w:M[ix[w],j]+=c
  self.M=M;weights=np.array([4*n-2*len(w) for w in self.overlaps]);assert np.array_equal(M@M.T,np.diag(weights));self.inv=np.diag(1/weights);self.rank=len(M)
  self.D={(x,y):np.array([(-1)**(y*i+x*j) for i in range(n) for j in range(n)]) for x in [0,1] for y in [0,1]}
  ss=[];aa=[]
  for i in range(n):
   for j in range(i,n):
    v=np.zeros(n*n)
    if i==j:v[i*n+j]=1;ss.append(v)
    else:v[i*n+j]=v[j*n+i]=2**-.5;ss.append(v.copy());v[j*n+i]*=-1;aa.append(v)
  self.bases=[np.array(ss).T,np.array(aa).T];self.target=np.zeros((2,2,self.s,self.s));self.target[0,0,0,0]=1/16
 def expand(self,B):
  H=np.zeros((4,4,self.s,self.s))
  for x in [0,1]:
   for y in [0,1]:
    d=self.D[x,y]
    for a in [0,1]:
     for b in [0,1]:H[2*x+a,2*y+b]=d[:,None]*B[a^y,b^x]*d[None,:]
  return H
 def base(self,H):
  B=np.zeros((2,2,self.s,self.s))
  for x in [0,1]:
   for y in [0,1]:
    d=self.D[x,y]
    for e in [0,1]:
     for f in [0,1]:B[e,f]+=d[:,None]*H[2*x+(e^y),2*y+(f^x)]*d[None,:]/4
  n=self.n;swap=lambda z:z.reshape(n,n,n,n).transpose(1,0,3,2).reshape(z.shape)
  for e in [0,1]:B[e,e]=(B[e,e]+swap(B[e,e]))/2
  B[0,1]=(B[0,1]+swap(B[1,0]))/2;B[1,0]=swap(B[0,1]);return B
 def tensor(self,H):
  n=self.n;return H.reshape(4,4,n,n,n,n).transpose(0,2,4,1,3,5).reshape(4*n*n,4*n*n)
 def untensor(self,T):
  n=self.n;return T.reshape(4,n,n,4,n,n).transpose(0,3,1,4,2,5).reshape(4,4,n*n,n*n)
 def ns(self,H):
  T=self.tensor(H);T=T-(T@self.M.T)@self.inv@self.M;T=T-self.M.T@self.inv@(self.M@T);return self.expand(self.base(self.untensor(T)))
 def psd(self,H):
  B=self.base(H);out=self.target.copy();B-=self.target;mn=0
  for e in [0,1]:
   for U in self.bases:
    z=U.T@B[e,e]@U;ev,V=np.linalg.eigh((z+z.T)/2);mn=min(mn,float(ev.min()));out[e,e]+=U@(V*np.maximum(ev,0)[None,:])@V.T@U.T
  z=(B[0,1]+B[0,1].T)/2;ev,V=np.linalg.eigh(z);mn=min(mn,float(ev.min()));out[0,1]=(V*np.maximum(ev,0)[None,:])@V.T;n=self.n;out[1,0]=out[0,1].reshape(n,n,n,n).transpose(1,0,3,2).reshape(z.shape)
  return self.expand(out),mn
 def trace(self,H):return np.trace(H,axis1=-2,axis2=-1).sum()
 def to_word(self,H):
  L=self.L+1;words=[()]+[tuple((start+j)%2 for j in range(k)) for k in range(1,L+1) for start in [0,1]];nw=len(words);C={}
  for x in [0,1]:
   for a in [0,1]:
    c=np.zeros((nw,self.n))
    for i,u in enumerate(self.ws[x]):c[words.index(u),i]+=2**-.5;c[words.index(reduce_word((x,)+u)),i]+=(-1)**a*2**-.5
    C[x,a]=c
  out=np.zeros((4,nw*nw,nw*nw))
  for x in [0,1]:
   for y in [0,1]:
    for a in [0,1]:
     for b in [0,1]:
      c=np.kron(C[x,a],C[y,b]);out[2*x+y]+=c@H[2*x+a,2*y+b]@c.T
  return words,out
