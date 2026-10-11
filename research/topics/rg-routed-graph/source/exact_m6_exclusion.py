from context_closure import *
from pathlib import Path
import json

def F(xs):
 W=tensor(xs);D=I16+sum(((local(k,Z)-I16)*E[k] for k in range(4)),s.zeros(16))
 return (W+sum(((local(k,Z)-I16)*W*E[k] for k in range(4)),s.zeros(16)))*D

def predict(i,pi,ps,xs,order):
 U=tensor(xs);V=I16
 for j in order:
  c=local(j,xs[j]);v=c.H*(ps[j]+(I16-ps[j])*R[j]*c*R[j]);V=(v*V).applyfunc(s.expand)
 return (U*V*pi*V.H*U.H*F(xs)).applyfunc(s.expand)

records=[]
# query3 witness, with rational c4 and x1=x2=X.
i=2;ps={j:I16-choices[tuple(sorted((i,j)))][0] for j in [0,1]};ps[3]=envelopes[2,3][1]
pi=s.zeros(16);pi[1,1]=1
xs=[X,X,I2,(3*I2+4*s.I*X)/5]
out=predict(i,pi,ps,xs,[3,0,1]);xs[3]=I2;a=predict(i,pi,ps,xs,[3,0,1]);xs[3]=X;b=predict(i,pi,ps,xs,[3,0,1]);diff=(out-(3*a+4*s.I*b)/5).applyfunc(s.expand)
assert diff[0,12]==s.Rational(48,125)
records.append({'query':3,'witness_entry':[0,12],'difference':str(diff[0,12]),'rank':diff.rank(),'norm_squared':str(s.trace(diff.H*diff))})
print(records[-1],flush=True)
# query4 witness: |00-,0><00-,0|, c3=(3I+4iY)/5, x1=I,x2=X.
i=3;ps={j:I16-choices[tuple(sorted((i,j)))][0] for j in [0,1]};ps[2]=envelopes[2,3][0]
pi=s.zeros(16);pi[0,0]=pi[2,2]=s.Rational(1,2);pi[0,2]=pi[2,0]=-s.Rational(1,2)
xs=[I2,X,(3*I2+4*s.I*Y)/5,I2]
out=predict(i,pi,ps,xs,[2,0,1]);xs[2]=I2;a=predict(i,pi,ps,xs,[2,0,1]);xs[2]=Y;b=predict(i,pi,ps,xs,[2,0,1]);diff=(out-(3*a+4*s.I*b)/5).applyfunc(s.expand)
assert diff[2,4]==s.Rational(96,125)
records.append({'query':4,'witness_entry':[2,4],'difference':str(diff[2,4]),'rank':diff.rank(),'norm_squared':str(s.trace(diff.H*diff))})
print(records[-1],flush=True)
# Verify the opposite q=I case has commutative necessary algebra.
for i in [2,3]:
 j=5-i;edges=[ij for ij in choices if i in ij and ij!=(2,3)]
 ps={next(k for k in e if k!=i):I16-choices[e][0] for e in edges}
 row=[remove(i,p) for p in ps.values()];mats=list(row)
 for k,p in ps.items():
  for c in origins:
   v=transport(i,k,p,c);mats.extend([(v.H*q*v).applyfunc(s.expand) for q in row])
 # Opposite endpoint: q=I for i3, q=0 before complement for i4.
 pp=envelopes[2,3][1]+(envelopes[2,3][2] if i==2 else s.zeros(16));p=pp if i==2 else I16-pp
 mats.append(remove(i,p))
 for c in origins:
  v=transport(i,j,p,c);mats.extend([(v.H*q*v).applyfunc(s.expand) for q in row])
 bs=cb(mats);assert all(x*y==y*x for x in bs for y in bs)
 records.append({'query':i+1,'opposite_comparison_commutant_dim':len(bs),'abelian':True})
 print(records[-1],flush=True)
Path(__file__).with_name('exact_m6_exclusion.json').write_text(json.dumps(records,indent=2))
