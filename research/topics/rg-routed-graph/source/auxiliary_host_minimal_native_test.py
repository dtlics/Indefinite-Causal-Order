"""Evaluate all exact mixed forms on the minimal active carriers E_i."""
from pathlib import Path
from itertools import product
import json,numpy as np,sympy as s
from exact_fixtures import E,I2,R,X,Y,Z,local
ROOT=Path(__file__).parent;meta=json.loads((ROOT/'auxiliary_host_compatibility_form_checks.json').read_text());data=np.load(ROOT/'auxiliary_host_compatibility_tangent_basis.npz');forms=json.loads((ROOT/'auxiliary_host_all_curvature_exact_checks.json').read_text())
maps={};pivcols={}
for i in range(4):
    for m,k in product([0,1<<(3-i)],['real','imag']):
        key=f'{m}_{k}'
        if key in maps:continue
        M=s.Matrix(data[key].tolist());_,pp=s.polys.matrices.DomainMatrix.from_Matrix(M).convert_to(s.QQ).rref();pivcols[key]=pp;maps[key]=M[:,list(pp)].T.inv()
units=[s.Matrix(2,2,lambda r,c:int(r==a and c==b)) for a,b in product(range(2),repeat=2)]
lookup={(d['mask'],d['kind'],d['typed_basis_index']):j for j,d in enumerate(forms['coordinate_labels'])}
Bs=[]
for rec in forms['forms']:
    B=s.zeros(72)
    for item in rec['bilinear_entries']:
        a,b=item['coordinates'];B[a,b]=B[b,a]=item['value']
    Bs.append(B)
out=[]
for i in range(4):
    bit=1<<(3-i);reps=[R[i]*local(i,u)*R[i] for u in units]
    for name,P in [('X',X),('Y',Y),('Z',Z)]:
        H=local(i,P)*E[i];kind='imag' if name=='Y' else 'real';H=H/s.I if kind=='imag' else H;mats=[H*A for A in reps];v=s.zeros(72,1)
        for mask in [0,bit]:
            key=f'{mask}_{kind}';vals=[]
            for index in pivcols[key]:
                r,t=divmod(index,256);n,q=divmod(t,16);t=(n&~bit)|(r&bit);vals.append(mats[2*int(bool((r^mask)&bit))+int(bool(n&bit))][t,q])
            coords=maps[key]*s.Matrix(vals)
            for j,x in enumerate(coords):
                if (mask,kind,j) in lookup:v[lookup[mask,kind,j]]=x
        bad=[j for j,B in enumerate(Bs) if B*v!=s.zeros(72,1)]
        out.append({'query':i+1,'Pauli':name,'common_radical':not bad,'nonannihilating_forms':bad,'nonboundary_coordinates':{str(j):str(x) for j,x in enumerate(v) if x}})
        print(out[-1],flush=True)
(ROOT/'auxiliary_host_minimal_native_test_checks.json').write_text(json.dumps({'status':'EXACT_MINIMAL_NATIVE_COORDINATES','results':out,'scope':'Genuine native directions at Q_i=E_i against all exact discovered forms; no topology sufficiency.'},indent=2)+'\n')
