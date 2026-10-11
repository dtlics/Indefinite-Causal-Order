"""Recompute the retained exact coefficient minor and the structural phase carriers."""
import json,itertools
import sympy as s
from exact_fixtures import E,I16,I2,X,Y,Z,tensor,WORDS,local,R
j=json.load(open('phase_mask_tangent_space_checks.json'))
chars={'0':s.Matrix([1,0]),'1':s.Matrix([0,1]),'+':s.Matrix([1,1]),'-':s.Matrix([1,-1])}
W=s.Matrix.hstack(*[tensor([chars[c] for c in w]) for w in j['labels']]);V=[I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16)) for o in WORDS];B=[v*W for v in V]
assert W.H*W==s.diag(*[(W[:,p].H*W[:,p])[0] for p in range(16)])
Ps=[I2,X,Y,Z];cache={}; rows=[]
for rr in j['retained_rows']:
 aa=tuple(rr['pauli_word'])
 if aa not in cache:
  A=tensor([Ps[a] for a in aa]);cache[aa]=[64*(-1)**sum(o[i] for i in range(4) if aa[i])*(B[k].H*A*B[k]) for k,o in enumerate(WORDS)]
 part=s.re if rr['part']=='real' else s.im
 cc=[part(m[rr['p'],rr['q']]) for m in cache[aa]]
 assert all(c.q==1 for c in cc)
 assert list(map(int,cc))==rr['coeff']
 row=[0]*256
 for o,c in enumerate(cc):row[16*o+rr['p']]=int(c);row[16*o+rr['q']]=-int(c)
 rows.append(row)
prime=j['prime'];pivots={}
for row in rows:
 rr={i:c%prime for i,c in enumerate(row) if c%prime}
 while rr:
  col=min(rr);v=rr[col]
  if col not in pivots:
   inv=pow(v,-1,prime);pivots[col]={i:(c*inv)%prime for i,c in rr.items()};break
  for i,c in pivots[col].items():
   z=(rr.get(i,0)-v*c)%prime
   if z:rr[i]=z
   elif i in rr:del rr[i]
assert len(pivots)==221
# Four source-cylinder carriers; zero-based query indices.
groups=[(1,[2,10]),(1,[3,13]),(2,[4,5]),(3,[6,7])]
carriers=[]
for i,cols in groups:
 C=sum((W[:,p]*W[:,p].H/(W[:,p].H*W[:,p])[0] for p in cols),s.zeros(16));carriers.append(C)
 assert C*C==C and C.H==C and C.rank()==2
 assert all(C*local(i,a)==local(i,a)*C for a in [X,Y,Z])
 assert all(E[k]*C==s.zeros(16) for k in range(4) if k!=i)
 # Controlled own-output R_i commutes with output-bit projector.
 assert R[i]*local(i,s.diag(0,1))==local(i,s.diag(0,1))*R[i]
 # These structural identities imply the parameter-level serial formula
 # proved in phase_mask_rigidity.md. The independent audit additionally
 # checks that formula with generic symbolic query entries.
assert all(a*b==s.zeros(16) for k,a in enumerate(carriers) for b in carriers[k+1:])
# Explicit 35 independent masks: sixteen input, fifteen nonconstant output, four controls.
gens=[]
for p in range(16):gens.append(s.Matrix([int(pp==p) for o in range(16) for pp in range(16)]))
for o in range(1,16):gens.append(s.Matrix([int(oo==o) for oo in range(16) for p in range(16)]))
for i,cols in groups:gens.append(s.Matrix([int(p in cols)*o[i] for o in WORDS for p in range(16)]))
G=s.Matrix.hstack(*gens)
assert G.rank()==35 and s.Matrix(rows)*G==s.zeros(221,35)
out={'status':'PASS','exact_recomputed_witness_rows':len(rows),'rank_mod_prime':len(pivots),'prime':prime,'explicit_generator_rank':35,'phase_space_dimension':35,'serial_controls':[{'query':i+1,'source_columns_zero_based':cols,'source_labels':[j['labels'][p] for p in cols]} for i,cols in groups]}
print(json.dumps(out,indent=2));json.dump(out,open('phase_mask_exact_verifier_checks.json','w'),indent=2)
