import sympy as s,itertools,json
from fractions import Fraction
from exact_fixtures import I2,X,Y,Z,tensor,WORDS
j=json.load(open('auxiliary_tangent_extra_directions.json'));old=json.load(open('auxiliary_tangent_extra_integrability_checks.json'));remaining=[x['direction'] for x in old['directions'] if x['bitflip_witness'] is None]
Us=[I2,(3*I2+4*s.I*X)/5,(3*I2+4*s.I*Y)/5,(3*I2+4*s.I*Z)/5,(I2+2*s.I*X+2*s.I*Y+4*s.I*Z)/5]
contexts=[]
for i in range(4):
 for u in range(1,5):a=[0]*4;a[i]=u;contexts.append(a)
contexts += [[u]*4 for u in range(1,5)]+[[1,2,3,4],[4,3,2,1],[2,1,4,3],[3,4,1,2]]
out=[]
for k in remaining:
 d=j['directions'][k];co={int(i):s.Rational(x,d['denominator']) for i,x in d['integer_coefficients'].items()};base=s.Rational(old['directions'][k]['identity_HS_squared']);witness=None
 for a in contexts:
  W=tensor([Us[u] for u in a]);C=s.zeros(16)
  for idx,v in co.items():
   r,t=divmod(idx,256);n,p=divmod(t,16);C[r,p]+=v*W[r^d['mask'],n]
  C=C.applyfunc(s.expand);norm=s.expand(s.trace(C.H*C))
  if norm!=base:witness={'context':a,'HS_squared':str(norm),'difference':str(norm-base)};break
 print(k,'witness',witness,flush=True);out.append({'direction':k,'identity_HS_squared':str(base),'witness':witness})
json.dump({'rotation_unitaries':['I','(3I+4iX)/5','(3I+4iY)/5','(3I+4iZ)/5','(I+2iX+2iY+4iZ)/5'],'results':out,'scope':'Exact finite counterexamples for listed individual representatives only.'},open('auxiliary_tangent_integrability_rotation_checks.json','w'),indent=2)
