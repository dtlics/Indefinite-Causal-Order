"""Exact linear tangent constraints for output/source masks of quartet in safe OPB."""
import sys, json, itertools, time
import sympy as s
from exact_fixtures import E, I16, I2, X,Y,Z,tensor,WORDS
chars={'0':s.Matrix([1,0]),'1':s.Matrix([0,1]),'+':s.Matrix([1,1]),'-':s.Matrix([1,-1])}
labels=['001-','10+0','0001','11-+','0100','0110','11+0','11+1','0000','001+','0101','0111','10+1','10-+','10--','11--']
W=s.Matrix.hstack(*[tensor([chars[c] for c in w]) for w in labels])
Ps=[I2,X,Y,Z]; V=[I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16)) for o in WORDS]
B=[v*W for v in V]
# All matrices have entries in Z[i]/powers of 2. Multiply by 64 to integral coefficients.
mod=1000003
pivots={}; retained=[]; scanned=0
for k,aa in enumerate(itertools.product(range(4),repeat=4)):
 A=tensor([Ps[a] for a in aa]); mats=[]
 for oi,o in enumerate(WORDS):
  sign=(-1)**sum(o[i] for i in range(4) if aa[i])
  mats.append(64*sign*(B[oi].H*A*B[oi]))
 for p in range(16):
  for q in range(p+1,16):
   for part in [s.re,s.im]:
    coeff=[int(part(m[p,q])) for m in mats]
    if not any(coeff):continue
    row={oi*16+p:c%mod for oi,c in enumerate(coeff) if c%mod}
    row.update({oi*16+q:(-c)%mod for oi,c in enumerate(coeff) if c%mod})
    original=dict(row)
    while row:
     col=min(row); z=row[col]
     if col not in pivots:
      inv=pow(z,-1,mod); row={j:(v*inv)%mod for j,v in row.items()}
      pivots[col]=row;retained.append((aa,p,q,'real' if part==s.re else 'imag',coeff));break
     for j,v in pivots[col].items():
      r=(row.get(j,0)-z*v)%mod
      if r:row[j]=r
      elif j in row:del row[j]
    scanned+=1
 print(k+1,len(pivots),flush=True)
 if len(pivots)>=225: # additive input/output functions guarantee <=225
  print('REACHED ADDITIVE UPPER BOUND',flush=True);break
out={'labels':labels,'prime':mod,'rank_lower_bound':len(pivots),'constraints_scanned':scanned,'retained_rows':[{'pauli_word':list(a),'p':p,'q':q,'part':part,'coeff':c} for a,p,q,part,c in retained]}
open('phase_mask_tangent_space_checks.json','w').write(json.dumps(out,indent=2))
