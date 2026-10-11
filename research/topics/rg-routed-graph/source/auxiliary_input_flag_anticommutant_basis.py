import json,math
from fractions import Fraction
import sympy as s
p=1000003
def rat(v):
 if v==0:return Fraction(0)
 r0,r1=p,v;t0,t1=0,1;B=700
 while abs(r1)>B:
  q=r0//r1;r0,r1=r1,r0-q*r1;t0,t1=t1,t0-q*t1
 if not t1 or abs(t1)>B:raise ValueError(v)
 a=Fraction(r1,t1);assert (a.numerator*pow(a.denominator,-1,p))%p==v;return a
out=[];origins=[]
for m in [0,4]:
 for kind in ['real','imag']:
  pp={int(k):{int(j):v for j,v in row.items()} for k,row in json.load(open(f'auxiliary_input_flag_anticommutant_echelon_{m}_{kind}.json')).items()};free=[j for j in range(4096) if j not in pp]
  for j in free:
   v=[0]*4096;v[j]=1
   for k in sorted(pp,reverse=True):v[k]=-sum(a*v[l] for l,a in pp[k].items() if l!=k)%p
   rr={k:rat(a) for k,a in enumerate(v) if a};den=math.lcm(*[a.denominator for a in rr.values()]);nums={str(k):int(a*den) for k,a in rr.items()}
   A=s.zeros(16)
   for k,a in rr.items():
    r,t=divmod(k,256);n,q=divmod(t,16)
    if n==(r^m):A[r,q]=s.Rational(a.numerator,a.denominator)*(s.I if kind=='imag' else 1)
   assert A==A.H
   origins.append(A);out.append({'mask':m,'kind':kind,'free_index':j,'denominator':den,'integer_coefficients':nums})
Gram=sum((A.H*A for A in origins),s.zeros(16));ker=Gram.nullspace();image=s.Matrix.hstack(*[A.reshape(256,1) for A in origins])
res={'lifted_directions':len(out),'origin_image_dimension':image.rank(),'common_origin_kernel_dimension':len(ker),'common_origin_kernel_basis':[[str(x) for x in v] for v in ker],'generic_trials':[]}
for b in [2,3,5]:
 A=sum((((k*b)%11-5)*a for k,a in enumerate(origins)),s.zeros(16));res['generic_trials'].append({'seed':b,'rank':A.rank()})
print(json.dumps(res,indent=2));json.dump({'summary':res,'directions':out},open('auxiliary_input_flag_anticommutant_basis_checks.json','w'),indent=2)
