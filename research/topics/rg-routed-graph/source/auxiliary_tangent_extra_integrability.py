"""Exact fixed-spectrum obstruction for the chosen rational tangent representatives.
This does not rule out their translates by the boundary/cut tangent span.
"""
import json
from fractions import Fraction
j=json.load(open('auxiliary_tangent_extra_directions.json'));out=[]
for k,d in enumerate(j['directions']):
 coeff={int(i):x for i,x in d['integer_coefficients'].items()};mask=d['mask'];den=d['denominator'];norms=[]
 for flip in range(16):
  val=sum(coeff.get((r*16+(r^mask^flip))*16+p,0)**2 for r in range(16) for p in range(16));norms.append(Fraction(val,den*den))
 witness=next((i for i in range(1,16) if norms[i]!=norms[0]),None)
 out.append({'direction':k,'mask':mask,'kind':d['kind'],'free_index':d['free_index'],'identity_HS_squared':str(norms[0]),'bitflip_witness':witness,'witness_HS_squared':str(norms[witness]) if witness is not None else None,'witness_difference':str(norms[witness]-norms[0]) if witness is not None else None})
print(json.dumps(out,indent=2));json.dump({'status':'COMPLETE','directions':out,'representatives_excluded_by_constant_spectrum':sum(x['bitflip_witness'] is not None for x in out),'scope':'Only the explicitly chosen representatives, not arbitrary linear combinations or additions of the 557-dimensional boundary/cut span.'},open('auxiliary_tangent_extra_integrability_checks.json','w'),indent=2)
