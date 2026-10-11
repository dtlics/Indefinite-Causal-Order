import sympy as s,itertools,json
from exact_fixtures import I16,I2,X,Y,Z,E,R,local,tensor
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16));Ps=[I2,X,Y,Z]
def F(us):
 W=tensor(us);return (W+sum(((local(i,Z)-I16)*W*E[i] for i in range(4)),s.zeros(16)))*D0
pairs={}
for i,j in itertools.permutations(range(4),2):
 gram=s.zeros(16)
 for a,b in itertools.product(Ps[1:],repeat=2):
  us=[I2]*4;us[i]=a;us[j]=b
  ai=R[i]*local(i,a)*R[i];aj=R[j]*local(j,b)*R[j]
  C=aj.H*F(us)*ai.H-I16;gram+=C.H*C
 pairs[i,j]=gram
print('pair grams done',flush=True)
out=[]
for bits in itertools.product(range(2),repeat=4):
 L=[i for i in range(4) if bits[i]];rr=[i for i in range(4) if not bits[i]]
 if not L or not rr:continue
 gram=sum((pairs[i,j] for i in L for j in rr),s.zeros(16));ns=gram.nullspace();K=s.Matrix.hstack(*ns) if ns else s.zeros(16,0)
 print(L,rr,'pair cut dim',K.cols,flush=True)
 # Test additional three/four-party Pauli contexts only on surviving small spaces.
 tested=0
 for aa in itertools.product(range(4),repeat=4):
  if not K.cols:break
  if sum(a!=0 for a in aa)<3:continue
  us=[Ps[a] for a in aa];left=[us[i] if i in L else I2 for i in range(4)];right=[us[i] if i in rr else I2 for i in range(4)]
  C=F(right).H*F(us)*F(left).H-I16;N=(C*K).nullspace();K=K*s.Matrix.hstack(*N) if N else s.zeros(16,0);tested+=1
 print('full Pauli dim',K.cols,'tested',tested,flush=True)
 out.append({'before_queries':[i+1 for i in L],'after_queries':[i+1 for i in rr],'pair_cut_dimension':len(ns),'pauli_cut_dimension':K.cols,'higher_contexts_tested':tested,'basis':[[str(x) for x in K[:,k]] for k in range(K.cols)]})
json.dump(out,open('auxiliary_supported_cut_spaces_checks.json','w'),indent=2)
