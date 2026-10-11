"""Exact contextual commutants. Inputs are copied as imported, never modified."""
import json
from exact_fixtures import *

def cb(mats):
 n=mats[0].rows
 basis=[s.eye(n*n)[:,k] for k in range(n*n)]
 V=s.Matrix.hstack(*basis)
 for a in mats:
  blocks=[]
  for col in range(V.cols):
   b=s.Matrix(n,n,V[:,col]); blocks.append((a*b-b*a).reshape(n*n,1))
  M=s.Matrix.hstack(*blocks)
  ns=M.nullspace()
  V=V*s.Matrix.hstack(*ns)
 return [s.Matrix(n,n,V[:,col]) for col in range(V.cols)]

def intersect(a,b):
 aa=s.Matrix.hstack(*[x.reshape(64,1) for x in a]);bb=s.Matrix.hstack(*[x.reshape(64,1) for x in b])
 return [s.Matrix(8,8,aa*v[:len(a),:]) for v in aa.row_join(-bb).nullspace()]

def contextual(i,j):
 edges=[ij for ij in choices if i in ij and ij!=(2,3)]
 out=[]
 for bit in [0,1]:
  pp=choices[tuple(sorted((i,j)))][bit];p=I16-pp if j<i else pp
  vs=[transport(i,j,p,c) for c in origins]
  for bits in product(range(2),repeat=len(edges)):
   row=[remove(i,choices[e][b]) for e,b in zip(edges,bits)]
   mats=[remove(i,p)]+[(v.H*q*v).applyfunc(s.expand) for v in vs for q in row]
   bs=cb(mats)
   out.append(((bit,bits),bs))
   print('row',i+1,j+1,bit,bits,'dim',len(bs),flush=True)
 return out

if __name__=='__main__':
 results={}
 for i,js in [(1,[0,2,3]),(2,[0,1]),(3,[0,1])]:
  algebras=[(('start',),[s.eye(8)[:,r]*s.eye(8)[c,:] for r in range(8) for c in range(8)])]
  for j in js:
   cc=contextual(i,j);new=[];unique=set()
   for ka,a in algebras:
    for kb,b in cc:
     bs=intersect(a,b)
     # Canonical reduced row space to de-duplicate exact algebras.
     key=tuple(s.Matrix.hstack(*[x.reshape(64,1) for x in bs]).T.rref()[0])
     if key in unique:continue
     unique.add(key);new.append(((ka,kb),bs))
   algebras=new
   print('STAGE',i+1,j+1,'unique',len(algebras),'dims',[len(bs) for _,bs in algebras],flush=True)
  records=[]
  for label,bs in algebras:
   cs=simple_components(bs)
   profile=sorted((n,int(s.trace(p))) for n,p in cs)
   print('FINAL',i+1,label,'dim',len(bs),'profile',profile,flush=True)
   for n,p in cs:
    if n>1:print('CARRIER',n,p.tolist(),flush=True)
   records.append({'label':str(label),'dimension':len(bs),'profile':profile,'noncommutative_carriers':[{'size':n,'matrix':[[str(z) for z in row] for row in p.tolist()]} for n,p in cs if n>1]})
  results[i+1]=records
  with open(Path(__file__).with_name('context_closure.json'),'w') as f:json.dump(results,f,indent=2)
