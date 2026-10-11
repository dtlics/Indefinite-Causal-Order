import json,sympy as s,itertools
from exact_fixtures import I16,I2,E,local,Z,X,Y,WORDS,tensor
p=1000003;ds=json.load(open('auxiliary_tangent_extra_directions.json'))['directions'];pp=json.load(open('auxiliary_tangent_constructive_span_echelons.json'))
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16));Vo=[I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16)) for o in WORDS]
out=[];Ps=[I2,X,Y,Z];names='IXYZ'
for k,scale,sign in [(0,4,1),(6,1,-1)]:
 d=ds[k];den=d['denominator']*scale;v={int(i):sign*x%p for i,x in d['integer_coefficients'].items()};piv={int(i):{int(j):x for j,x in row.items()} for i,row in pp['0_real'].items()}
 rr=dict(v)
 while rr:
  col=min(rr);z=rr[col]
  if col not in piv:break
  for i,x in piv[col].items():
   vv=(rr.get(i,0)-z*x)%p
   if vv:rr[i]=vv
   elif i in rr:del rr[i]
 Bs=[s.zeros(16) for o in range(16)]
 for idx,vv in d['integer_coefficients'].items():
  o,t=divmod(int(idx),256);n,q=divmod(t,16);Bs[o][n,q]=s.Rational(sign*vv,den)
 Qs=[(Vo[o]*D0).H*Bs[o] for o in range(16)]
 assert all(Q.H==Q and Q*Q==Q for Q in Qs)
 unique=[];assign=[]
 for Q in Qs:
  if Q not in unique:unique.append(Q)
  assign.append(unique.index(Q))
 spect=[]
 for z,Q in enumerate(unique):
  coeff=[]
  for aa in itertools.product(range(4),repeat=4):
   P=tensor([Ps[a] for a in aa]);c=s.trace(P*Q)/16
   if c:coeff.append([''.join(names[a] for a in aa),str(c)])
  spect.append({'rank':Q.rank(),'Pauli_expansion':coeff})
 rec={'direction':k,'scale':f'{sign}/{scale}','outside_expanded_566_span_mod_prime':bool(rr),'modular_membership_residual_count':len(rr),'conditional_process_projector_count':len(unique),'output_to_projector_index':assign,'projectors':spect}
 print(json.dumps(rec,indent=2),flush=True);out.append(rec)
json.dump(out,open('auxiliary_new_projector_structure_checks.json','w'),indent=2)
