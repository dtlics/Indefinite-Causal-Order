from context_closure import *
import json

def insert_identity(i,a):
 out=s.zeros(16)
 for r,x in enumerate(WORDS):
  for c,y in enumerate(WORDS):
   if x[i]==y[i]:
    rr=int(''.join(str(x[k]) for k in range(4) if k!=i),2)
    cc=int(''.join(str(y[k]) for k in range(4) if k!=i),2)
    out[r,c]=a[rr,cc]
 return out
qC=choices[0,1][0].extract(range(4),range(4))
S1=tensor([I2,s.diag(1,0),s.eye(4)-qC])
g0=s.zeros(8,1);g0[1]=1;g1=s.Matrix([0,0,0,0,1,1,-1,-1])/2
S2=insert_identity(1,g0*g0.H+g1*g1.H)
Ss=[S1,S2,E[2],E[3]]
assert [s.trace(p) for p in Ss]==[4,4,2,2]
assert all(p*p==p and p.H==p for p in Ss)
assert all(Ss[i]*Ss[j]==s.zeros(16) for i,j in combinations(range(4),2))
records=[]
i=0;edges=[e for e in choices if i in e]
for bits in product([0,1],repeat=3):
 ps={e[1]:choices[e][b] for e,b in zip(edges,bits)}
 row=[remove(i,p) for p in ps.values()];mats=list(row)
 for j,p in ps.items():
  for c in origins:
   v=transport(i,j,p,c);mats += [(v.H*q*v).applyfunc(s.expand) for q in row]
 bs=cb(mats)
 target=remove(i,S1 if bits[0]==0 else E[0])
 if bits[0]==0:
  tb=[target[:,r]*target[c,:] for r in range(8) for c in range(8)]+[s.eye(8)-target]
 else:tb=[target,s.eye(8)-target]
 V=s.Matrix.hstack(*[x.reshape(64,1) for x in tb]);r=V.rank()
 assert r==(5 if bits[0]==0 else 2)==len(bs)
 assert all(V.row_join(x.reshape(64,1)).rank()==r for x in bs)
 physical=S1 if bits[0]==0 else E[0]
 assert all(p*physical==s.zeros(16) for p in ps.values())
 records.append({'bits':bits,'relative_algebra_dimension':r,'all_comparisons_annihilate_serial_support':True})
for e in choices:
 if 1 not in e:continue
 for p in choices[e]:
  if e[0]!=1:p=I16-p
  assert p*S2==s.zeros(16)
Path(__file__).with_name('first_port_serial_ideals_checks.json').write_text(json.dumps({'query1':records,'query2_all_comparisons_annihilate_S2':True,'four_serial_supports_pairwise_orthogonal':True},indent=2))
print('All exact first-port serial-ideal and support-orthogonality checks passed.')
