"""Try the two ordinary ordered joint extensions of the new phase slots.
An exact failure of original-query linearity rejects that ordered construction.
"""
import sympy as s,itertools,json
from exact_fixtures import I16,I2,X,Y,Z,E,local,tensor,WORDS
P0=s.diag(1,0);P1=s.diag(0,1);P4=tensor([P0,I2,I2,P0])+tensor([P1,I2,P0,I2]);P5=tensor([I2,I2,P0,I2])+tensor([P0,P1,P1,I2])
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16));Vo=[I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16)) for o in WORDS]
cache={};gates=[I2,X,Y,Z]+[(3*I2+4*s.I*A)/5 for A in [X,Y,Z]]
def vals(ids):
 ids=tuple(ids)
 if ids in cache:return cache[ids]
 W=tensor([gates[k] for k in ids]);F=s.Matrix.vstack(*[W[o,:]*Vo[o]*D0 for o in range(16)]);C=s.Matrix.vstack(*[(1-ow[1])*W[o,:]*P4*Vo[o]*D0 for o,ow in enumerate(WORDS)]);D=s.Matrix.vstack(*[(1-ow[3])*W[o,:]*P5*Vo[o]*D0 for o,ow in enumerate(WORDS)])
 v=[(C*F.H*D).applyfunc(s.expand),(D*F.H*C).applyfunc(s.expand)];cache[ids]=v;return v
out=[]
for order in [0,1]:
 found=None;count=0
 for i in range(4):
  if found:break
  for others in itertools.product(range(4),repeat=3):
   if found:break
   a=list(others);a.insert(i,0);EI=vals(a)[order]
   for k in [1,2,3]:
    a[i]=k;EP=vals(a)[order];a[i]=k+3;ER=vals(a)[order];a[i]=0
    diff=(ER-s.Rational(3,5)*EI-s.Rational(4,5)*s.I*EP).applyfunc(s.expand);count+=1
    if diff!=s.zeros(16):
     rr,cc=next((rr,cc) for rr in range(16) for cc in range(16) if diff[rr,cc]!=0)
     found={'varied_query':i+1,'spectator_context':others,'axis':'IXYZ'[k],'defect_HS_squared':str(s.expand(s.trace(diff.H*diff))),'nonzero_entry':[rr,cc,str(diff[rr,cc])]};break
 out.append({'order':'C4 Fdag C5' if order==0 else 'C5 Fdag C4','tests':count,'linearity_failure':found});print(out[-1],flush=True)
json.dump({'results':out,'scope':'Only these ordinary ordered joint phase constructions; no exclusion of controlled-order or other joint extensions.'},open('auxiliary_phase_ordered_joint_test_checks.json','w'),indent=2)
