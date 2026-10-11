"""Exact rank/eigenvalue obstruction for every strict-partition crossing pair."""
from pathlib import Path
from itertools import permutations
import json
import sympy as s
from exact_fixtures import E,R,I2,I16,X,Y,Z,local,tensor
ROOT=Path(__file__).parent
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16))
records=[]
for i,j in permutations(range(4),2):
 name='Y' if (i,j)==(2,3) else 'X';P=Y if name=='Y' else X
 a=(3*I2+4*s.I*P)/5;b=X
 assert (a.H*a-I2).applyfunc(s.simplify)==s.zeros(2)
 us=[I2]*4;us[i]=a;us[j]=b;W=tensor(us)
 F=(W+sum(((local(k,Z)-I16)*W*E[k] for k in range(4)),s.zeros(16)))*D0
 alpha=R[i]*local(i,a)*R[i];beta=R[j]*local(j,b)*R[j]
 C=(beta.H*F*alpha.H).applyfunc(s.simplify)
 assert (C.H*C-I16).applyfunc(s.simplify)==s.zeros(16)
 D=(C-I16).applyfunc(s.simplify);assert D.rank()==4
 assert (D.H*D-D*D.H).applyfunc(s.simplify)==s.zeros(16)
 obstruction=(4*D**2-s.trace(D)*D).applyfunc(s.simplify)
 assert obstruction!=s.zeros(16)
 row,col=next((r,c) for r in range(16) for c in range(16) if obstruction[r,c]!=0)
 norm=s.simplify(s.trace(obstruction.H*obstruction));assert norm>0
 records.append({'left_query':i+1,'right_query':j+1,'left_unitary':f'(3I+4i{name})/5','right_unitary':'X',
  'rank_C_minus_I':4,'trace_C_minus_I':str(s.trace(D)),'normality_verified':True,
  'rank_one_multiplicity_polynomial_defect_HS_squared':str(norm),
  'nonzero_entry':[row,col,str(obstruction[row,col])]})
 print(i+1,j+1,'rank4, multiplicity polynomial nonzero, HS2',norm,flush=True)
(ROOT/'auxiliary_strict_m4_cocycle_obstruction_checks.json').write_text(json.dumps({'status':'PASS','all_ordered_crossing_pairs':12,'witnesses':records,'consequence':'Every full M4 auxiliary extension of the quartet with a fixed global strict orientation against each original query is pure past or pure future. A proper partition would put a rank4 normal C-I in I4 tensor M4, forcing4(C-I)^2=Tr(C-I)(C-I), contradicted here.','scope':'Does not classify M4 auxiliaries with nontrivial comparisons, branched auxiliaries, or routed hosts.'},indent=2)+'\n')
print('PASS: strict-comparison full M4 auxiliaries are boundary-only',flush=True)
