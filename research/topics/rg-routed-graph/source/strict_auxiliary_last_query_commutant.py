"""Add exact Gaussian-rational contexts to the four last-query cocycle commutants."""
from pathlib import Path
from itertools import product
import json,time,numpy as np,sympy as s
from exact_fixtures import E,I2,I16,X,Y,Z,tensor
from phase_endpoint_exact import row_tensor,WORDS
ROOT=Path(__file__).parent;P=1000033;assert s.isprime(P);ii=int(s.sqrt_mod(-1,P));assert ii*ii%P==P-1
T=row_tensor(4,1);J=X*Z
def F(us):
 W=tensor(us)
 return (W+sum((tensor([Z*us[j]*Z-us[j] if j==i else us[j] for j in range(4)])*E[i] for i in range(4)),s.zeros(16))).applyfunc(s.expand)
def modnum(x):
 a,b=s.expand(x).as_real_imag();a=s.Rational(a);b=s.Rational(b)
 return (int(a.p)*pow(int(a.q),-1,P)+ii*int(b.p)*pow(int(b.q),-1,P))%P
values={}
for choice in product(range(4),repeat=4):
 A=np.zeros((16,16),dtype=np.int64)
 for r,rw in enumerate(WORDS):
  nw=[];sg=1
  for i,o in enumerate(rw):
   gate=choice[i];nw.append(o^(gate in [1,3]));sg*=(-1 if(gate==2 and o==1)or(gate==3 and o==0)else 1)
  n=sum(a<<(3-k) for k,a in enumerate(nw));A[r]=sg*T[r,n]
 values[choice]=A
qs=[(1,2,2,4),(2,1,4,2),(2,4,1,2),(4,2,2,1),(3,4,0,0),(3,0,4,0),(3,0,0,4)]
gates=[(a*I2+s.I*b*X+c*J+s.I*d*Z)/5 for a,b,c,d in qs]
choices=[(0,1,2,3),(1,2,3,0),(4,5,6,0),(0,0,0,0),(2,3,1,0)]
out=[]
for last in range(4):
 left=[i for i in range(4) if i!=last];piv={};recs=[];start=time.time()
 def add(C,context):
  for a,b in product(range(16),repeat=2):
   row={}
   for k in range(16):
    col=16*k+b;row[col]=(row.get(col,0)+int(C[a,k]))%P
    col=16*a+k;row[col]=(row.get(col,0)-int(C[k,b]))%P
   row={k:v for k,v in row.items() if v}
   while row:
    col=min(row);z=row[col]
    if col not in piv:
     inv=pow(z,-1,P);piv[col]={j:v*inv%P for j,v in row.items()};recs.append({'context':context,'entry':[a,b]});break
    for j,v in piv[col].items():
     zz=(row.get(j,0)-z*v)%P
     if zz:row[j]=zz
     elif j in row:del row[j]
   if len(piv)==255:break
 for choice in product(range(4),repeat=4):
  if sum(c!=0 for c in choice)<2:continue
  ll=tuple(c if i in left else 0 for i,c in enumerate(choice));rr=tuple(c if i not in left else 0 for i,c in enumerate(choice));C=values[rr].T@values[choice]@values[ll].T;add(C,{'type':'real_Pauli','indices':list(choice)})
  if len(piv)==255:break
 ranks=[len(piv)]
 for choice in choices:
  if len(piv)==255:break
  us=[gates[k] for k in choice];FL=F([u if i in left else I2 for i,u in enumerate(us)]);FR=F([I2 if i in left else u for i,u in enumerate(us)]);C=FR.H*F(us)*FL.H;CM=np.array([[modnum(x) for x in row] for row in C.tolist()],dtype=np.int64);add(CM,{'type':'quaternion','indices':list(choice)});ranks.append(len(piv));print('last',last+1,'rank',len(piv),'seconds',time.time()-start,flush=True)
 out.append({'last_query':last+1,'before_queries':[i+1 for i in left],'rank_progression':ranks,'commutator_rank_lower_bound':len(piv),'commutant_dimension_upper_bound':256-len(piv),'rank_rows':recs})
(ROOT/'strict_auxiliary_last_query_commutant_checks.json').write_text(json.dumps({'status':'EXACT_GAUSSIAN_RANK_LOWER_CERTIFICATES','prime':P,'image_of_i':ii,'quaternions':qs,'results':out,'scope':'All selected rows are exact Gaussian-rational necessary commutator equations. Rank255 closes the full commutant at scalars; lesser rank is only an upper bound on its dimension.'},indent=2)+'\n')
