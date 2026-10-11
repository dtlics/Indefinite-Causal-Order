"""Exact necessary input-operator tangent space and controlled one-qubit probes."""
import json,itertools,sympy as s,numpy as np
from exact_fixtures import I16,I2,X,Y,Z,E,local,tensor,WORDS
p=1000003;D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16));Ts=[]
for o in WORDS:
 V=I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16));Ts.append(np.array(4*V*D0,dtype=np.int64))
Ts=np.array(Ts);rows_by_kind={};out={}
for kind in ['real','imag']:
 pp={int(i):{int(j):v for j,v in row.items()} for i,row in json.load(open(f'auxiliary_tangent_echelon_0_{kind}.json')).items()}
 # Transform retained echelon constraints modulo p into 16x16 input A coordinates.
 coords=[(a,b) for a in range(16) for b in range(a if kind=='real' else a+1,16)];idx={ab:k for k,ab in enumerate(coords)};piv={};rows=[]
 for old in pp.values():
  row={}
  for vv,c in old.items():
   r,t=divmod(vv,256);n,q=divmod(t,16)
   for m in range(16):
    x=int(Ts[r,m,q])*c
    if not x or(kind=='imag' and m==n):continue
    pair=(min(n,m),max(n,m));j=idx[pair];sg=-1 if(kind=='imag' and n>m)else 1;row[j]=(row.get(j,0)+sg*x)%p
  row={j:x for j,x in row.items() if x};rows.append(row.copy())
  while row:
   col=min(row);a=row[col]
   if col not in piv:
    inv=pow(a,-1,p);piv[col]={j:x*inv%p for j,x in row.items()};break
   for j,x in piv[col].items():
    z=(row.get(j,0)-a*x)%p
    if z:row[j]=z
    elif j in row:del row[j]
 rows_by_kind[kind]=(coords,rows);out[kind]={'input_Hermitian_coordinates':len(coords),'constraint_rank_lower_bound':len(piv),'dimension_upper_bound':len(coords)-len(piv)}
print(out,flush=True)
probes=[];P0=s.diag(1,0);P1=s.diag(0,1)
for control,target in itertools.permutations(range(4),2):
 flags=[]
 for name,A in [('X',X),('Y',Y),('Z',Z)]:
  H=tensor([P1 if i==control else A if i==target else I2 for i in range(4)]);kind='imag' if name=='Y' else 'real';B=H/s.I if kind=='imag' else H
  coords,rows=rows_by_kind[kind];v=[int(B[a,b])%p for a,b in coords];bad=sum(bool(sum(c*v[j] for j,c in row.items())%p) for row in rows);flags.append({'Pauli':name,'satisfies_complete_tangent_equations':bad==0,'violated_rows':bad})
 probes.append({'control':control+1,'target':target+1,'conditional_native_M2_candidate_all_Paulis_pass':all(x['satisfies_complete_tangent_equations'] for x in flags),'checks':flags})
print(json.dumps(probes,indent=2));json.dump({'input_tangent_upper_bounds':out,'controlled_qubit_probes':probes,'scope':'Necessary complete tangent membership only; negative finite-field residuals reject these fixed integer candidates exactly, positive membership is not a unitary native extension.'},open('auxiliary_lab_input_operator_space_checks.json','w'),indent=2)
