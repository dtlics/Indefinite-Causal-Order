import sympy as s,json
from exact_fixtures import E,R,I2,I16,X,local,tensor
minus=s.Matrix([1,-1]);Q=tensor([I2,I2,minus*minus.H/2,s.diag(0,1)])
assert Q*Q==Q and Q.rank()==4
out={'cut_rank':4,'support_overlaps':[],'moving_input_carrier':[]}
for i,e in enumerate(E):
 diff=e*Q-Q*e
 out['support_overlaps'].append({'query':i+1,'trace_Ei_Q':str(s.trace(e*Q)),'Ei_Q_rank':(e*Q).rank(),'commutator_HS_squared':str(s.trace(diff.H*diff))})
for i in [0,1]:
 a=R[i]*local(i,X)*R[i];Qt=a.H*Q*a;diff=Qt-Q
 entry=next((r,c,diff[r,c]) for r in range(16) for c in range(16) if diff[r,c]!=0)
 out['moving_input_carrier'].append({'query':i+1,'context':'X at this query, all other original queries I','defect_HS_squared':str(s.trace(diff.H*diff)),'nonzero_entry':[entry[0],entry[1],str(entry[2])]})
print(json.dumps(out,indent=2));json.dump(out,open('auxiliary_cut_dynamic_carrier_checks.json','w'),indent=2)
