from exact_fixtures import *
import json

def cb0(mats):
 V=s.eye(64)
 for A in mats:
  Q=(s.kronecker_product(A,s.eye(8))-s.kronecker_product(s.eye(8),A.T))*V
  V=V*s.Matrix.hstack(*Q.nullspace())
 return V

def reshape(v):return s.Matrix(8,8,v)
def restrict(V,fun):
 Q=s.Matrix.hstack(*[fun(reshape(V[:64,k]),reshape(V[64:,k])).reshape(128 if fun is side else 256,1) for k in range(V.cols)])
 return V*s.Matrix.hstack(*Q.nullspace())
def image(V):return V[:64,:].columnspace()
def Emap(i,t,x):
 inds=[]
 for w in WORDS:
  rest=[w[k] for k in range(4) if k!=i]
  inds.append(8*w[i]+4*rest[0]+2*rest[1]+rest[2])
 M=s.kronecker_product(t,x).extract(inds,inds)
 return R[i]*M*R[i]

D=s.zeros(16)
for r,w in enumerate(WORDS):
 rec=I16-2*sum((E[k] for k in range(4) if w[k]),s.zeros(16))
 D[r,:]=rec[r,:]

def original(xs):
 W=tensor(xs);O=s.zeros(16)
 for r,w in enumerate(WORDS):
  rec=I16-2*sum((E[k] for k in range(4) if w[k]),s.zeros(16))
  O[r,:]=(W*rec)[r,:]
 return O*D.H

def context(i,ps,xs):
 j=5-i;c=local(j,xs[j]);aj=R[j]*c*R[j]
 vv=[]
 for k in (0,1):
  u=local(k,xs[k]);vv.append(u.H*(ps[k]+(I16-ps[k])*R[k]*u*R[k]))
 U=tensor(xs);tail=U.H*original(xs)
 def evaluate(A,B):
  rho=c.H*(B+aj*(A-B)*aj.H)*c
  for v in vv:rho=v*rho*v.H
  return (U*rho*tail).applyfunc(s.expand)
 return evaluate

results=[]
for i in (2,3):
 for bits in product((0,1),repeat=2):
  pp={k:I16-choices[k,i][b] for k,b in zip((0,1),bits)}
  row=[remove(i,p) for p in pp.values()]
  mats=row+[(v.H*q*v).applyfunc(s.expand) for k,p in pp.items() for v in [transport(i,k,p,c) for c in origins] for q in row]
  B=cb0(mats);V=s.diag(B,s.eye(64))
  C=remove(i,envelopes[2,3][2]);H=remove(i,envelopes[2,3][1 if i==2 else 0])
  def side(x,y):return s.Matrix.vstack((s.eye(8)-C)*y-H*x,y*(s.eye(8)-C)-x*H)
  V=restrict(V,side)
  print('INITIAL',i+1,bits,V.cols,len(image(V)),flush=True)
  ntests=0
  for axis in (X,Y):
   for a,b in ((I2,X),(X,I2),(X,X)):
    xs=[I2]*4;xs[0]=a;xs[1]=b;ev=[]
    for c in (I2,axis,(3*I2+4*s.I*axis)/5):
     xs[5-i]=c;ev.append(context(i,pp,xs))
    for t in (s.diag(1,0),s.Matrix([[0,1],[0,0]])):
     def defect(x,y):
      A=Emap(i,t,x);Q=Emap(i,t,y)
      return ev[2](A,Q)-(3*ev[0](A,Q)+4*s.I*ev[1](A,Q))/5
     V=restrict(V,defect);ntests+=1
    if len(image(V))<=2:break
   if len(image(V))<=2:break
  out=image(V);e=remove(i,E[i]);target=s.Matrix.hstack(s.eye(8).reshape(64,1),e.reshape(64,1))
  assert len(out)==2 and target.row_join(s.Matrix.hstack(*out)).rank()==2
  report={'query':i+1,'bits':bits,'pair_dimension':V.cols,'X_dimension':len(out),'test_count':ntests,'target_match':True}
  print('PASS',report,flush=True);results.append(report)
Path('/workspace/shared/conjectures/routed_graph_new/independent_maximality_check.json').write_text(json.dumps(results,indent=2))
print('ALL EIGHT MAXIMALITY CASES PASS',flush=True)
