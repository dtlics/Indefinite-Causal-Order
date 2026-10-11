import sympy as s,json,itertools
from exact_fixtures import I16,I2,X,Y,Z,E,R,local,tensor,origins
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16))
def F(us):
 W=tensor(us);return (W+sum(((local(i,Z)-I16)*W*E[i] for i in range(4)),s.zeros(16)))*D0
j=json.load(open('auxiliary_supported_cut_spaces_checks.json'));out=[]
for old in j:
 if not old['pauli_cut_dimension']:continue
 LL=[i-1 for i in old['before_queries']];RR=[i for i in range(4) if i not in LL]
 K=s.Matrix.hstack(*[s.Matrix([s.sympify(x) for x in col]) for col in old['basis']]);tests=0;witnesses=[]
 # One non-Pauli rotation and every other party a Pauli, then two rotation tests.
 contexts=[]
 for rot_i in range(4):
  for ri in range(4,7):
   for other in itertools.product(range(4),repeat=3):
    aa=list(other);aa.insert(rot_i,ri);contexts.append(aa)
 for aa in contexts:
  if not K.cols:break
  us=[origins[a] for a in aa];l=[us[i] if i in LL else I2 for i in range(4)];r=[us[i] if i in RR else I2 for i in range(4)]
  C=F(r).H*F(us)*F(l).H-I16;M=C*K
  if M!=s.zeros(16,K.cols):
   N=M.nullspace();K=K*s.Matrix.hstack(*N) if N else s.zeros(16,0);witnesses.append({'context':aa,'remaining_dimension':K.cols});print(LL,aa,'dim',K.cols,flush=True)
  tests+=1
 print('DONE',LL,K.cols,tests,flush=True)
 out.append({'before_queries':old['before_queries'],'initial_dimension':old['pauli_cut_dimension'],'remaining_dimension':K.cols,'tests':tests,'strict_witnesses':witnesses,'basis':[[str(x) for x in K[:,k]] for k in range(K.cols)]})
json.dump(out,open('auxiliary_supported_cut_continuous_test_checks.json','w'),indent=2)
