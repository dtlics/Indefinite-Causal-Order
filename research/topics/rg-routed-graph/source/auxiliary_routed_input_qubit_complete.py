"""Complete M2 auxiliary test for a controlled laboratory-input qubit routing."""
import itertools,json,numpy as np,sympy as s
from exact_fixtures import I16,I2,E,X,Y,Z,local,tensor,WORDS
P0=s.diag(1,0);P1=s.diag(0,1);beta=lambda A:tensor([P0,I2,I2,A])+tensor([P1,I2,A,I2]);units=[s.Matrix([[int(r==a and c==b) for c in range(2)] for r in range(2)]) for a,b in itertools.product(range(2),repeat=2)]
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16));T=[]
for o in WORDS:
 V=I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16));T.append(np.array(4*V*D0,dtype=np.int64))
T=np.array(T);Cs=[np.array([np.array(beta(e),dtype=np.int64)@t for t in T],dtype=np.int64) for e in units]
opts=[[(1,a,1,a,1) for a in range(2)]]+[[(0,a,0,b,1),(1,a,1,b,-1)] for a,b in itertools.product(range(2),repeat=2)]
terms=[]
for key in itertools.product(range(5),repeat=4):
 ts=[]
 for term in itertools.product(*[opts[key[i]] for i in range(4)]):
  r=sum(term[i][0]<<(3-i) for i in range(4));n=sum(term[i][1]<<(3-i) for i in range(4));m=sum(term[i][3]<<(3-i) for i in range(4));sg=int(np.prod([x[4] for x in term]));ts.append((r,n,m,sg))
 terms.append((key,ts))
out=[]
for ab,cd in itertools.product(range(4),repeat=2):
 a,b=divmod(ab,2);c,d=divmod(cd,2);bad=[]
 for key,ts in terms:
  M=np.zeros((16,16),dtype=np.int64)
  for r,n,m,sg in ts:
   M+=sg*np.outer(Cs[ab][r,n],Cs[cd][r,m])
   if a==c:M-=sg*np.outer(T[r,n],Cs[2*b+d][r,m])
  if np.any(M):bad.append({'key':key,'maxabs':int(np.max(np.abs(M)))})
 out.append({'left_unit':[a,b],'right_unit':[c,d],'bad_word_keys':len(bad),'first_bad':bad[:1]});print(out[-1],flush=True)
 if bad:break
json.dump({'status':'PASS' if all(x['bad_word_keys']==0 for x in out) and len(out)==16 else 'FAIL','matrix_unit_products':out,'scope':'If PASS, all16 exact matrix-unit products hold at arbitrary independent private dimensions and define a full M2 auxiliary extension.'},open('auxiliary_routed_input_qubit_complete_checks.json','w'),indent=2)
