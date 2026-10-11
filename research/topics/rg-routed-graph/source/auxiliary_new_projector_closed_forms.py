import sympy as s,json
from exact_fixtures import I16,I2,E,local,Z,tensor,WORDS
P0=s.diag(1,0);P1=s.diag(0,1)
P4=tensor([P0,I2,I2,P0])+tensor([P1,I2,P0,I2])
P5=tensor([I2,I2,P0,I2])+tensor([P0,P1,P1,I2])
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16));Vs=[I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16)) for o in WORDS]
ds=json.load(open('auxiliary_tangent_extra_directions.json'))['directions'];out=[]
for k,scale,sign,P,party in [(0,4,1,P4,1),(6,1,-1,P5,3)]:
 assert P*P==P and P.H==P
 d=ds[k];Bs=[s.zeros(16) for _ in range(16)]
 for idx,v in d['integer_coefficients'].items():
  o,t=divmod(int(idx),256);n,p=divmod(t,16);Bs[o][n,p]=s.Rational(sign*v,d['denominator']*scale)
 for o,ob in enumerate(WORDS):assert Bs[o]==((1-ob[party])*P*Vs[o]*D0)
 Q=local(party,P0)*P
 assert Q*Q==Q and Q.H==Q
 out.append({'direction':k,'coefficient_blocks_exactly_matched':16,'laboratory_input_projector_rank':P.rank(),'origin_projector_rank':Q.rank(),'own_output_zero_party':party+1})
print(json.dumps({'status':'PASS','closed_forms':out},indent=2));json.dump({'status':'PASS','closed_forms':out},open('auxiliary_new_projector_closed_forms_checks.json','w'),indent=2)
