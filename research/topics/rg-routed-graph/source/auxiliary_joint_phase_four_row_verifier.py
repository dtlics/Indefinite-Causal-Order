"""Standalone four-row exact dual certificate: no rank enumeration required."""
import itertools,json
import sympy as s
from exact_fixtures import I16,E,local,Z,WORDS
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16));T=[]
for o in WORDS:
 V=I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16));T.append(4*V*D0)
P4=lambda n: int((n[0]==0 and n[3]==0) or(n[0]==1 and n[2]==0))
P5=lambda n: int(n[2]==0 or(n[0]==0 and n[1]==1 and n[2]==1))
C=[s.diag(*[(1-o[1])*P4(n) for n in WORDS])*T[r] for r,o in enumerate(WORDS)]
D=[s.diag(*[(1-o[3])*P5(n) for n in WORDS])*T[r] for r,o in enumerate(WORDS)]
opts=[[(1,a,1,a,1) for a in range(2)]]+[[(0,a,0,b,1),(1,a,1,b,-1)] for a,b in itertools.product(range(2),repeat=2)]
# key0=I, key1=u00* u00, key2=u00* u01,
# key3=u01* u00, key4=u01* u01 at each party.
chosen=[([0,1,0,1],2,2,-1),([0,1,0,2],2,0,-1),([0,2,0,1],2,6,1),([0,2,0,3],0,6,1)]
result=[];total={};value=s.Integer(0)
for key,pp,qq,weight in chosen:
 row={};rhs=s.Integer(0)
 for term in itertools.product(*[opts[key[k]] for k in range(4)]):
  r=sum(term[k][0]<<(3-k) for k in range(4));a=sum(term[k][1]<<(3-k) for k in range(4));b=sum(term[k][3]<<(3-k) for k in range(4));sg=s.prod(t[4] for t in term)
  rhs+=sg*(C[r][a,pp]*D[r][b,qq]+D[r][a,pp]*C[r][b,qq])
  for variable,coef in [((r,b,qq),sg*T[r][a,pp]),((r,a,pp),sg*T[r][b,qq])]:row[variable]=row.get(variable,0)+coef
 row={v:s.simplify(c) for v,c in row.items() if c!=0}
 for variable,coef in row.items():total[variable]=total.get(variable,0)+weight*coef
 value+=weight*rhs
 result.append({'word_key':key,'boundary_entry':[pp,qq],'weight':weight,'lhs_terms':[{'unknown_e_index':list(v),'coefficient':str(c)} for v,c in sorted(row.items())],'rhs':str(rhs)})
 print(result[-1],flush=True)
assert all(c==0 for c in total.values()) and value==16
out={'status':'PASS','exact_contradiction':'0=16 after clearing coefficient denominators','rows':result,'weighted_lhs_identically_zero':True,'weighted_rhs':str(value),'no_modular_or_rank_assumption':True}
json.dump(out,open('auxiliary_joint_phase_four_row_verifier_checks.json','w'),indent=2);print('EXACT FOUR-ROW CONTRADICTION 0=16',flush=True)
