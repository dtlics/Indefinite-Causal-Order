import sympy as s,itertools,json
from exact_fixtures import I16,I2,X,Y,Z,E,R,local,tensor
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16))
assert D0.H*D0==I16
P=[I2,X,Y,Z];names=['I','X','Y','Z']
def F(us):
 W=tensor(us);return (W+sum(((local(i,Z)-I16)*W*E[i] for i in range(4)),s.zeros(16)))*D0
out=[]
for i,j in itertools.permutations(range(4),2):
 for a,b in itertools.product(range(1,4),repeat=2):
  us=[I2]*4;us[i]=P[a];us[j]=P[b];C=F(us)-R[j]*local(j,P[b])*R[j]*R[i]*local(i,P[a])*R[i]
  if C!=s.zeros(16):
   n=s.trace(C.H*C);entry=next((rr,cc,C[rr,cc]) for rr in range(16) for cc in range(16) if C[rr,cc]!=0)
   out.append({'before':i+1,'after':j+1,'before_query':names[a],'after_query':names[b],'defect_HS_squared':str(n),'nonzero_entry':[entry[0],entry[1],str(entry[2])]});break
 else:raise AssertionError((i,j))
print(json.dumps({'status':'PASS','all_ordered_cross_pairs_excluded':12,'witnesses':out},indent=2));json.dump(out,open('auxiliary_full_boundary_checks.json','w'),indent=2)
