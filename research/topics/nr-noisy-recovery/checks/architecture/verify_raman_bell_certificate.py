"""Exact ordinary two-node Bell-yield lower bound, not an upper bound.

All matrices and initial amplitudes are reconstructed from small rational
data.  Four positive-definite Gram majorants and Vidal's pure-state LOCC
conversion theorem supply the claimed attainable Bell yield.  The latter
theorem and ideal local-control/optical-port assumptions are analytic.
"""
from fractions import Fraction as F
from pathlib import Path
import json

if not __debug__:
    raise RuntimeError('Assertions are required; do not use -O.')

def z(a=0,b=0):return (F(a),F(b))
ZERO=z();ONE=z(1)
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def neg(a):return (-a[0],-a[1])
def sub(a,b):return add(a,neg(b))
def mul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def conj(a):return (a[0],-a[1])
def scale(a,x):return (a[0]*x,a[1]*x)
def inv(a):
    d=a[0]**2+a[1]**2
    assert d>0
    return (a[0]/d,-a[1]/d)
def sumz(values):
    out=ZERO
    for value in values:out=add(out,value)
    return out
def zeros(n,m):return [[ZERO for j in range(m)] for i in range(n)]
def eye(n):return [[ONE if i==j else ZERO for j in range(n)] for i in range(n)]
def adj(a):return [[conj(a[j][i]) for j in range(len(a))] for i in range(len(a[0]))]
def mm(a,b):
    assert len(a[0])==len(b)
    return [[sumz(mul(x,y) for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def matrix_inv(a):
    n=len(a);work=[row[:]+idrow[:] for row,idrow in zip(a,eye(n))]
    for j in range(n):
        pivot=next(i for i in range(j,n) if work[i][j]!=ZERO)
        work[j],work[pivot]=work[pivot],work[j]
        value=inv(work[j][j]);work[j]=[mul(x,value) for x in work[j]]
        for i in range(n):
            if i!=j:
                value=work[i][j]
                work[i]=[sub(x,mul(value,y)) for x,y in zip(work[i],work[j])]
    assert [row[:n] for row in work]==eye(n)
    out=[row[n:] for row in work]
    assert mm(a,out)==mm(out,a)==eye(n)
    return out

def cayley(numerators,denominator):
    h=[[z(F(pair[0],denominator),F(pair[1],denominator)) for pair in row] for row in numerators]
    assert h==adj(h)
    left=eye(4);right=eye(4)
    for i in range(4):
        for j in range(4):
            ih=mul(z(0,1),h[i][j])
            left[i][j]=add(left[i][j],ih)
            right[i][j]=sub(right[i][j],ih)
    unitary=mm(left,matrix_inv(right))
    assert mm(unitary,adj(unitary))==mm(adj(unitary),unitary)==eye(4)
    return unitary

def apply2(vector,gate,i,j):
    out=[ZERO]*64
    mask=(1<<(5-i))|(1<<(5-j))
    for col,value in enumerate(vector):
        if value==ZERO:continue
        local_col=2*((col>>(5-i))&1)+((col>>(5-j))&1)
        base=col&~mask
        for local_row in range(4):
            target=base|((local_row//2)<<(5-i))|((local_row%2)<<(5-j))
            out[target]=add(out[target],mul(gate[local_row][local_col],value))
    return out

def pd_ldl(matrix):
    assert matrix==adj(matrix)
    n=len(matrix);lower=eye(n);diagonal=[]
    for j in range(n):
        value=sub(matrix[j][j],sumz(scale(mul(lower[j][k],conj(lower[j][k])),diagonal[k]) for k in range(j)))
        assert value[1]==0 and value[0]>0
        diagonal.append(value[0])
        for i in range(j+1,n):
            residual=sub(matrix[i][j],sumz(scale(mul(lower[i][k],conj(lower[j][k])),diagonal[k]) for k in range(j)))
            lower[i][j]=scale(residual,1/diagonal[j])
    d=zeros(n,n)
    for j,value in enumerate(diagonal):d[j][j]=z(value)
    assert mm(mm(lower,d),adj(lower))==matrix
    return diagonal

def verify(path):
    data=json.loads(Path(path).read_text(encoding='utf-8'))
    assert data['schema']=='ordinary-local-ancilla-lower-bound-v1'
    beta=F(data['beta']);t=1-beta
    assert 0<beta<1
    denominator=data['parameter_denominator']
    amplitudes=[]
    for numerator in data['initial_tangent_numerators']:
        u=F(numerator,denominator)
        c=(1-u*u)/(1+u*u);s=2*u/(1+u*u)
        assert c*c+s*s==1
        amplitudes.append((c,s))
    assert len(amplitudes)==3
    source=[ZERO]*64
    for p in range(2):
        for a in range(2):
            for b in range(2):
                source[48*p+12*a+3*b]=z(amplitudes[0][p]*amplitudes[1][a]*amplitudes[2][b])
    assert sum(mul(conj(x),x)[0] for x in source)==1
    node=[[z(1),ZERO,ZERO,ZERO],[ZERO,z(t),z(beta),ZERO],
          [ZERO,z(beta),z(t),ZERO],[ZERO,ZERO,ZERO,z(1)]]
    contraction=mm(adj(node),node)
    singlet=[ZERO,ONE,z(-1),ZERO]
    assert [[sub(eye(4)[i][j],contraction[i][j]) for j in range(4)] for i in range(4)]==[
        [scale(mul(singlet[i],conj(singlet[j])),2*beta*t) for j in range(4)] for i in range(4)]
    mid=cayley(data['mid_cayley_H_numerators'],denominator)
    read=cayley(data['read_cayley_H_numerators'],denominator)
    state=apply2(source,node,0,2)
    state=apply2(state,mid,0,1)
    state=apply2(state,node,0,4)
    state=apply2(state,read,0,1)
    lower=F(0);norm=F(0);records=[];pivots=0
    for outcome,bound_text in enumerate(data['largest_Schmidt_weight_upper_bounds']):
        m=[state[16*outcome+4*i:16*outcome+4*i+4] for i in range(4)]
        gram=mm(m,adj(m));trace=sum(gram[i][i][0] for i in range(4))
        assert all(gram[i][i][1]==0 for i in range(4))
        bound=F(bound_text)
        majorant=[[sub(z(bound if i==j else 0),gram[i][j]) for j in range(4)] for i in range(4)]
        pivots+=len(pd_ldl(majorant))
        probability=min(trace,2*(trace-bound))
        assert probability>0
        lower+=probability;norm+=trace
        records.append({'outcome':outcome,'norm':float(trace),'lambda_max_upper':float(bound),
                        'Bell_yield_lower':float(probability)})
    switch=beta*beta*(1+t*t)
    assert 0<lower<=norm<=1 and lower>switch
    assert lower>F(5473,10000) and lower-switch>F(13,1000)
    return {'status':'passed','beta':str(beta),'unitary_matrices':2,'exact_LDL_pivots':pivots,
            'ordinary_Bell_probability_lower':float(lower),'switch_Bell_probability':float(switch),
            'simple_certified_ordinary_lower':'5473/10000',
            'strict_gap_lower':float(lower-switch),'survival_probability':float(norm),
            'all_photon_loss_probability':float(1-norm),'records':records,
            'scope':'Exact attainable ordinary ideal-flat-Lambda lower bound with two local matter ancillas, one flying two-degree photon, declared coherent controls, all helper outcomes and ideal LOCC concentration. Not a native-cost advantage or an ordinary upper bound.'}

if __name__=='__main__':
    print(json.dumps(verify(Path(__file__).with_name('raman_bell_certificate.json')),indent=2))
