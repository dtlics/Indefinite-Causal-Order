"""Lift the 26 missing modular null directions to small rational vectors."""
import json,math
from fractions import Fraction
p=1000003;cut=json.load(open('auxiliary_tangent_cut_span_echelons.json'));out=[]
def add(v,piv):
 row={i:x%p for i,x in enumerate(v) if x%p}
 while row:
  j=min(row);a=row[j]
  if j not in piv:
   inv=pow(a,-1,p);piv[j]={k:x*inv%p for k,x in row.items()};return True
  for k,x in piv[j].items():
   z=(row.get(k,0)-a*x)%p
   if z:row[k]=z
   elif k in row:del row[k]
 return False
def reconstruct(v):
 if v==0:return Fraction(0)
 r0,r1=p,v;t0,t1=0,1;B=700
 while abs(r1)>B:
  q=r0//r1;r0,r1=r1,r0-q*r1;t0,t1=t1,t0-q*t1
 if not t1 or abs(t1)>B or math.gcd(r1,t1)!=1:raise ValueError(v)
 a=Fraction(r1,t1)
 assert (a.numerator*pow(a.denominator,-1,p))%p==v
 return a
for m in [0,1,2,4]:
 for kind in ['real','imag']:
  piv={int(k):{int(j):v for j,v in row.items()} for k,row in json.load(open(f'auxiliary_tangent_echelon_{m}_{kind}.json')).items()}
  free=[j for j in range(4096) if j not in piv];sub={}
  for row in cut[f'{m}_{kind}'].values():add([row.get(str(j),0) for j in free],sub)
  extras=[]
  for k,j in enumerate(free):
   e=[0]*len(free);e[k]=1
   if add(e,sub):extras.append(j)
  print(m,kind,'free',len(free),'extra',len(extras),flush=True)
  for j in extras:
   v=[0]*4096;v[j]=1
   for k in sorted(piv,reverse=True):v[k]=-sum(a*v[l] for l,a in piv[k].items() if l!=k)%p
   rs={str(k):str(reconstruct(a)) for k,a in enumerate(v) if a}
   denom=math.lcm(*[Fraction(x).denominator for x in rs.values()]);nums={k:int(Fraction(a)*denom) for k,a in rs.items()}
   out.append({'mask':m,'kind':kind,'free_index':j,'denominator':denom,'integer_coefficients':nums,'nonzero_count':len(nums),'max_abs_numerator':max(map(abs,nums.values()))})
json.dump({'prime':p,'extra_dimension':len(out),'directions':out},open('auxiliary_tangent_extra_directions.json','w'),indent=2)
print('total',len(out),'maxden',max(x['denominator'] for x in out),'maxnum',max(x['max_abs_numerator'] for x in out),flush=True)
