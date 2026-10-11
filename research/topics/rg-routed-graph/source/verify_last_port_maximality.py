from context_closure import *
from tensor_tools import embed, F
import json

def refine(pairs,fun):
 vals=[fun(x,y).applyfunc(s.expand) for x,y in pairs]
 M=s.Matrix.hstack(*[v.reshape(len(v),1) for v in vals]);ns=M.nullspace()
 return [(sum((v[k]*pairs[k][0] for k in range(len(pairs))),s.zeros(8)),sum((v[k]*pairs[k][1] for k in range(len(pairs))),s.zeros(8))) for v in ns]

def xdim(pairs):
 return s.Matrix.hstack(*[x.reshape(64,1) for x,y in pairs]).rank()

_cache={}
def eval_linear(i,ps,xs,A,B):
 key=(i,tuple(tuple(ps[k]) for k in [0,1]),tuple(tuple(x) for x in xs))
 if key not in _cache:
  j=5-i;c=local(j,xs[j]);aj=R[j]*c*R[j]
  V=I16
  for k in [0,1]:
   cc=local(k,xs[k]);v=cc.H*(ps[k]+(I16-ps[k])*R[k]*cc*R[k]);V=(v*V).applyfunc(s.expand)
  U=tensor(xs);left=(U*V*c.H).applyfunc(s.expand);right=(c*V.H*U.H*F(xs)).applyfunc(s.expand)
  _cache[key]=(left,right,(left*aj).applyfunc(s.expand),(aj.H*right).applyfunc(s.expand))
 l,r,la,ar=_cache[key]
 return (l*B*r+la*(A-B)*ar).applyfunc(s.expand)

if __name__=='__main__':
 results=[]
 for i in [2,3]:
  j=5-i;edges=[e for e in choices if i in e and e!=(2,3)]
  for bits in product([0,1],repeat=2):
   ps={next(k for k in e if k!=i):I16-choices[e][b] for e,b in zip(edges,bits)}
   row=[remove(i,p) for p in ps.values()];mats=list(row)
   for k,p in ps.items():
    for c in origins:
     v=transport(i,k,p,c);mats += [(v.H*q*v).applyfunc(s.expand) for q in row]
   bs=cb(mats)
   pairs=[(x,s.zeros(8)) for x in bs]+[(s.zeros(8),s.eye(8)[:,r]*s.eye(8)[c,:]) for r in range(8) for c in range(8)]
   C=remove(i,envelopes[2,3][2]);H=remove(i,envelopes[2,3][1 if i==2 else 0])
   pairs=refine(pairs,lambda x,y:s.Matrix.vstack((s.eye(8)-C)*y-H*x,y*(s.eye(8)-C)-x*H))
   print('START',i+1,bits,'pairs',len(pairs),'xdim',xdim(pairs),flush=True)
   for axis in [X,Y,Z]:
    for idx in product(range(4),repeat=2):
     xs=[I2]*4;xs[0]=[I2,X,Y,Z][idx[0]];xs[1]=[I2,X,Y,Z][idx[1]]
     for unit in [s.diag(1,0),s.Matrix([[0,1],[0,0]])]:
      def constraint(x,y):
       A=embed(i,unit,x);B=embed(i,unit,y);vals=[]
       for cc in [(3*I2+4*s.I*axis)/5,I2,axis]:
        xs[j]=cc;vals.append(eval_linear(i,ps,xs,A,B))
       return vals[0]-(3*vals[1]+4*s.I*vals[2])/5
      n=len(pairs);pairs=refine(pairs,constraint)
      if len(pairs)!=n:print('DROP',i+1,bits,'axis',[X,Y,Z].index(axis),'idx',idx,'pairs',len(pairs),'xdim',xdim(pairs),flush=True)
     if xdim(pairs)<=2:break
    if xdim(pairs)<=2:break
   xx=[s.Matrix(8,8,v) for v in s.Matrix.hstack(*[x.reshape(64,1) for x,y in pairs]).columnspace()]
   print('FINAL',i+1,bits,'xdim',len(xx),'abelian',all(a*b==b*a for a in xx for b in xx),flush=True)
   target=remove(i,E[i]);target_space=s.Matrix.hstack(s.eye(8).reshape(64,1),target.reshape(64,1))
   assert len(xx)==2
   assert all(target_space.row_join(x.reshape(64,1)).rank()==2 for x in xx)
   results.append({'query':i+1,'bits':list(bits),'residual_pair_dimension':len(pairs),'projected_X_dimension':len(xx),'equals_identity_and_own_cylinder':True,'own_relative_cylinder_rank':int(s.trace(target))})
   Path(__file__).with_name('last_port_maximality_checks.json').write_text(json.dumps(results,indent=2))
