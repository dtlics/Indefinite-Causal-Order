"""Exact complete projector test for two additional tangent representatives."""
import itertools,json,numpy as np,sympy as s
from exact_fixtures import I16,E,local,Z,WORDS
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16));T=[]
for o in WORDS:
 v=I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16));T.append(np.array(4*v*D0,dtype=np.int64))
T=np.array(T);ds=json.load(open('auxiliary_tangent_extra_directions.json'))['directions'];out=[]
opts=[[(1,a,1,a,1) for a in range(2)]]+[[(0,a,0,b,1),(1,a,1,b,-1)] for a,b in itertools.product(range(2),repeat=2)]
for k,scale,sign in [(0,4,1),(6,1,-1)]:
 d=ds[k];den=d['denominator']*scale;C=np.zeros((16,16,16),dtype=np.int64)
 for idx,v in d['integer_coefficients'].items():
  r,t=divmod(int(idx),256);a,b=divmod(t,16);C[r,a,b]=sign*v
 bad=[]
 for choice in itertools.product(range(5),repeat=4):
  M=np.zeros((16,16),dtype=np.int64)
  for term in itertools.product(*[opts[choice[i]] for i in range(4)]):
   r=sum(term[i][0]<<(3-i) for i in range(4));a=sum(term[i][1]<<(3-i) for i in range(4));b=sum(term[i][3]<<(3-i) for i in range(4));sg=int(np.prod([x[4] for x in term]))
   M+=sg*(4*np.outer(C[r,a,:],C[r,b,:])-den*np.outer(T[r,a,:],C[r,b,:]))
  if np.any(M):bad.append({'word_key':choice,'max_abs':int(np.max(np.abs(M)))})
 origin=s.Matrix([[s.Rational(C[r,r,q],den) for q in range(16)] for r in range(16)])
 assert origin*origin==origin and origin.H==origin
 rec={'direction':k,'rescaling':f'{sign}/{scale}','origin_projector_rank':origin.rank(),'reduced_word_keys_checked':625,'nonzero_defect_keys':len(bad),'first_bad':bad[:4]};print(json.dumps(rec),flush=True);out.append(rec)
json.dump({'tests':out,'meaning':'A zero defect, together with the already exact complete Hermiticity check, proves a complete C⊕C auxiliary phase extension, not just infinitesimal integrability.'},open('auxiliary_tangent_projector_extensions_checks.json','w'),indent=2)
