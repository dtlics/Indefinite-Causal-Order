import sympy as s,json
from exact_fixtures import I16,I2,E,X,Y,Z,local,tensor,WORDS
P0=s.diag(1,0);P1=s.diag(0,1)
beta=lambda A:tensor([P0,I2,I2,A])+tensor([P1,I2,A,I2])
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16));Vs=[I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16)) for o in WORDS]
alpha=[]
for A in [X,Y,Z]:
 b=beta(A);alpha.append(s.Matrix.vstack(*[b[r,:]*Vs[r]*D0 for r in range(16)]))
out={'single_aux_origin_tests':[]}
for name,a in zip('XYZ',alpha):out['single_aux_origin_tests'].append({'Pauli':name,'Hermitian':a==a.H,'square_identity':a*a==I16,'unitarity_defect_HS_squared':str(s.trace((a.H*a-I16).H*(a.H*a-I16)))})
out['Pauli_product_XY_equals_iZ']=alpha[0]*alpha[1]==s.I*alpha[2]
print(json.dumps(out,indent=2));json.dump(out,open('auxiliary_routed_input_qubit_probe_checks.json','w'),indent=2)
