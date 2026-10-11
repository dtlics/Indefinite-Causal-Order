import sympy as s,json
j=json.load(open('auxiliary_tangent_extra_directions.json'));old=json.load(open('auxiliary_tangent_extra_integrability_checks.json'));remaining=[x['direction'] for x in old['directions'] if x['bitflip_witness'] is None];out=[]
for k in remaining:
 d=j['directions'][k];C=s.zeros(16)
 for idx,v in d['integer_coefficients'].items():
  r,t=divmod(int(idx),256);n,p=divmod(t,16)
  if n==(r^d['mask']):C[r,p]=s.Rational(v,d['denominator'])*(s.I if d['kind']=='imag' else 1)
 assert C==C.H
 eig=C.eigenvals();print(k,'rank',C.rank(),'eigen',eig,flush=True)
 out.append({'direction':k,'rank':C.rank(),'eigenvalues':{str(x):int(y) for x,y in eig.items()}})
json.dump(out,open('auxiliary_tangent_extra_spectra_checks.json','w'),indent=2)
