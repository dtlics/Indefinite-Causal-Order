import json,sympy as s,itertools
from exact_fixtures import I16,I2,E,local,Z,X,Y,WORDS,tensor
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16));Vo=[I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16)) for o in WORDS];ds=json.load(open('auxiliary_tangent_extra_directions.json'))['directions'];Paulis=[(''.join('IXYZ'[i] for i in a),tensor([[I2,X,Y,Z][i] for i in a])) for a in itertools.product(range(4),repeat=4)]
out=[]
for k,scale,sign in [(0,4,1),(6,1,-1)]:
 d=ds[k];Bs=[s.zeros(16) for o in range(16)]
 for idx,v in d['integer_coefficients'].items():
  o,t=divmod(int(idx),256);n,p=divmod(t,16);Bs[o][n,p]=s.Rational(sign*v,d['denominator']*scale)
 frames={}
 for name,qq in [('raw_input',[Vo[o]*Bs[o]*D0 for o in range(16)]),('laboratory_input',[Bs[o]*D0*Vo[o] for o in range(16)])]:
  unique=[];mapping=[]
  for Q in qq:
   if Q not in unique:unique.append(Q)
   mapping.append(unique.index(Q))
  expansion=[]
  for Q in unique:
   co=[[name,str(s.trace(P*Q)/16)] for name,P in Paulis if s.trace(P*Q)!=0];expansion.append(co)
  frames[name]={'unique':len(unique),'mapping':mapping,'term_counts':list(map(len,expansion)),'Pauli_expansions':expansion}
 print(k,{name:{k:v for k,v in x.items() if k!='Pauli_expansions'} for name,x in frames.items()},flush=True);out.append({'direction':k,'frames':frames})
json.dump(out,open('auxiliary_new_projector_frames_checks.json','w'),indent=2)
