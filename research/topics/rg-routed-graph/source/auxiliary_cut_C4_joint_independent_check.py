"""Independent rational witnesses against both globally forced active orders."""
from pathlib import Path
import json
import sympy as s
from exact_fixtures import E,I2,I16,X,Z,WORDS,tensor,local
ROOT=Path(__file__).parent
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16))
P0=s.diag(1,0);P1=s.diag(0,1)
P4=tensor([P0,I2,I2,P0])+tensor([P1,I2,P0,I2])
minus=s.Matrix([1,-1]);Q34=s.kronecker_product(minus*minus.T/2,P1)
Q=tensor([I2,I2,Q34])
a=tensor([P1,P0,Q34])
assert Q*Q==Q and Q.rank()==4 and Q*a==a and a*Q==a and a.rank()==1
J=X*Z;R=(3*I2+4*J)/5
assert J.H*J==I2 and R.H*R==I2


def F(us):
    # Independent normalized orthogonal-cylinder formula, not the scout's
    # row-coefficient tensor multiplication.
    out=tensor(us)
    for i in range(4):
        factors=us.copy();factors[i]=Z*us[i]*Z-us[i]
        out+=tensor(factors)*E[i]
    return out


def C4(us):
    W=tensor(us);rows=[]
    for r,o in enumerate(WORDS):
        V=I16-2*sum((E[i] for i in range(4) if o[i]),s.zeros(16))
        rows.append(W[r,:]*P4*V*D0 if o[1]==0 else s.zeros(1,16))
    return s.Matrix.vstack(*rows)


def ordered(us,order):
    f=F(us);c=C4(us)
    assert f.H*f==I16 and c.H*c==f.H*c
    fl=F(us[:2]+[I2,I2]);fr=F([I2,I2]+us[2:])
    active=fr*a*fl
    assert active==tensor([I2,I2]+us[2:])*a*fl
    return c*f.H*active if order==0 else active*f.H*c


records=[]
for order,varied,baseline,entry,value in [
    (0,0,[I2,I2,I2,I2],(1,0),-s.Rational(24,125)),
    (1,3,[I2,X,I2,I2],(8,12),s.Rational(24,125))]:
    vals=[]
    for u in [I2,J,R]:
        us=baseline.copy();us[varied]=u;vals.append(ordered(us,order))
    defect=vals[2]-(3*vals[0]+4*vals[1])/5
    assert defect[entry]==value
    assert defect!=s.zeros(16)
    records.append({'order':'C4 Fdag Gactive' if order==0 else 'Gactive Fdag C4',
        'active_a':'|10><10|12 tensor |minus,1><minus,1|34',
        'varied_original_query':varied+1,
        'fixed_X_queries':[i+1 for i,u in enumerate(baseline) if u==X],
        'rotation':'(3 I+4 XZ)/5','entry':list(entry),'exact_defect':str(value),
        'nonzero_entries':sum(x!=0 for x in defect),
        'defect_matrix':[[str(x) for x in row] for row in defect.tolist()]})
    print(records[-1]['order'],'entry',entry,'defect',value,'PASS',flush=True)
(ROOT/'auxiliary_cut_C4_joint_independent_checks.json').write_text(json.dumps({
    'status':'PASS','witnesses':records,
    'conclusion':'Both active orders forced by a hypothetical complete full-cut/C4 pair fail original-query complex linearity.',
    'scope':'No simultaneous complete extension with both exact fixed marginal tensors. This does not follow from the rank-two tangent obstruction alone.'},indent=2)+'\n')
