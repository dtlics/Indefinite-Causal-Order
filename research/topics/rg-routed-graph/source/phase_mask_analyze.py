import sympy as s,json
j=json.load(open('phase_mask_tangent_space_checks.json')); rows=[]
for rr in j['retained_rows']:
 row=[0]*256;p=rr['p'];q=rr['q']
 for o,c in enumerate(rr['coeff']):row[16*o+p]=c;row[16*o+q]=-c
 rows.append(row)
A=s.polys.matrices.DomainMatrix.from_Matrix(s.Matrix(rows)).convert_to(s.QQ)
ns=A.nullspace().to_Matrix();ns=[v/s.gcd_list(list(v)) for v in [ns.row(k).T for k in range(ns.rows)]]
print('nullity',len(ns),flush=True)
# remove additive gauges: m(o,p)-m(o,0)-m(0,p)+m(0,0)
res=[]
for v in ns:
 r=s.Matrix(16,16,v); rr=s.Matrix(16,16,lambda o,p:r[o,p]-r[o,0]-r[0,p]+r[0,0]);res.append(rr.reshape(256,1))
R=s.Matrix.hstack(*res);cols=R.columnspace();print('quotient dim',len(cols),flush=True)
for k,col in enumerate(cols):
 M=s.Matrix(16,16,col);print('BASIS',k);print(M);print()
json.dump({'nullity':len(ns),'basis':[[str(x) for x in v] for v in ns],'quotient_basis':[[str(x) for x in v] for v in cols]},open('phase_mask_tangent_basis.json','w'),indent=2)
