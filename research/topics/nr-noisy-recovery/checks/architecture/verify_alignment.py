"""Exact primal/dual replay for alignment.md, using only the standard library.

Port order is (outF,inF,outE,inE). No solver or saved positivity flag is used.
Prints JSON and writes no files; the runner owns current validation evidence.
"""
from fractions import Fraction as F
from itertools import product
from math import comb
import json

if not __debug__:
    raise RuntimeError('Assertions must be enabled')


def zero(n,m=None): return [[F(0) for _ in range(n if m is None else m)] for _ in range(n)]
def eye(n): return [[F(i==j) for j in range(n)] for i in range(n)]
def scale(c,A): return [[c*x for x in row] for row in A]
def add(A,B): return [[x+y for x,y in zip(a,b)] for a,b in zip(A,B)]
def sub(A,B): return add(A,scale(-1,B))
def tr(A): return sum(A[i][i] for i in range(len(A)))
def outer(a,b=None):
    if b is None: b=a
    return [[F(x*y) for y in b] for x in a]
def matmul(A,B):
    return [[sum(x*y for x,y in zip(a,b)) for b in zip(*B)] for a in A]
def kron(A,B):
    return [[a*B[k][l] for a in ar for l in range(len(B[0]))]
            for ar in A for k in range(len(B))]
def iszero(A): return all(x==0 for row in A for x in row)
def index(bits,dims):
    n=0
    for b,d in zip(bits,dims): n=n*d+b
    return n
def ptrace(A,dims,axis):
    dd=dims[:axis]+dims[axis+1:]
    states=list(product(*[range(d) for d in dd]))
    return [[sum(A[index(a[:axis]+(k,)+a[axis:],dims)][index(b[:axis]+(k,)+b[axis:],dims)]
                 for k in range(dims[axis])) for b in states] for a in states]
def psd(A):
    B=[row[:] for row in A]
    n=len(B); pivots=[]
    assert all(B[i][j]==B[j][i] for i in range(n) for j in range(n))
    for k in range(n):
        d=B[k][k]
        assert d>=0,('negative pivot',k,d)
        if not d:
            assert all(B[k][j]==0 for j in range(k,n)),('zero pivot/nonzero row',k)
        else:
            pivots.append(str(d))
            for i in range(k+1,n):
                for j in range(i,n):
                    B[i][j]-=B[i][k]*B[k][j]/d
                    B[j][i]=B[i][j]
    return pivots
def inverse(A):
    n=len(A); B=[row[:]+e[:] for row,e in zip(A,eye(n))]
    for k in range(n):
        assert B[k][k]
        d=B[k][k];B[k]=[x/d for x in B[k]]
        for i in range(n):
            if i!=k:
                d=B[i][k];B[i]=[x-d*y for x,y in zip(B[i],B[k])]
    return [row[n:] for row in B]
def reverse_qubits(A,n):
    p=[int(format(i,'0'+str(n)+'b')[::-1],2) for i in range(2**n)]
    return [[A[p[i]][p[j]] for j in range(2**n)] for i in range(2**n)]


# Gaussian integers are integer pairs throughout construction of Bell vectors.
def ga(a,b):return (a[0]+b[0],a[1]+b[1])
def gn(a):return (-a[0],-a[1])
def gm(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def gc(a):return(a[0],-a[1])
def gvouter(v,den):
    A=[]
    for a in v:
        row=[]
        for b in v:
            z=gm(a,gc(b));assert z[1]==0
            row.append(F(z[0],den))
        A.append(row)
    return A
def gkron(a,b):return[gm(x,y) for x in a for y in b]


def supplementary_checks(K, R):
    # The native square roots are defined by these exact spectral projectors.
    A=scale(16,R); E=eye(8); projectors=[]
    for eigen, other, divisor in [(3,(4,6),3),(4,(3,6),-2),(6,(3,4),6)]:
        factors=[sub(A,scale(x,E)) for x in other]
        P=scale(F(1,divisor),matmul(*factors))
        assert iszero(sub(matmul(P,P),P))
        assert iszero(sub(matmul(A,P),scale(eigen,P)))
        projectors.append(P)
    assert [tr(P) for P in projectors]==[4,2,2]
    assert iszero(sub(sum_matrices(projectors),E))
    for i,P in enumerate(projectors):
        for j,Q in enumerate(projectors):
            if i!=j:assert iszero(matmul(P,Q))
    # Therefore sqrt(R)=(sqrt(3)P3+2P4+sqrt(6)P6)/4 is positive,
    # squares exactly to R, and the displayed V is an isometry by its prefix.
    bell=scale(F(1,2),outer([1,0,0,1]))
    P=sub(eye(4),bell); swap=zero(16)
    for i in range(4):
        for j in range(4):swap[4*i+j][4*j+i]=F(1)
    independentK=scale(F(1,2),matmul(kron(P,P),sub(eye(16),swap)))
    assert iszero(sub(K,independentK))
    n=[1,0,0,-1]
    m=[F(4,5),F(3,5),F(3,5),F(-4,5)]
    rhoi=outer([1,0,0,1])
    rn=scale(F(1,4),add(rhoi,outer(n)))
    rm=scale(F(1,4),add(rhoi,outer(m)))
    assert tr(rn)==tr(rm)==1
    assert tr(matmul(K,kron(rn,rm)))==F(9,200)
    assert tr(matmul(K,kron(rn,rn)))==0
    # Output/input regrouping proves the parallel harmonic-mean constraint.
    states=list(product(range(2),repeat=4)); perm=[0,2,1,3]
    indices=[index(tuple(s[i] for i in perm),[2]*4) for s in states]
    regroup=[[K[indices[i]][indices[j]] for j in range(16)] for i in range(16)]
    sing=scale(F(1,2),outer([0,1,-1,0])); trip=sub(eye(4),sing)
    TS=kron(trip,sing); ST=kron(sing,trip)
    assert iszero(sub(matmul(matmul(regroup,TS),regroup),scale(F(1,2),regroup)))
    assert iszero(sub(matmul(matmul(regroup,ST),regroup),scale(F(1,2),regroup)))
    assert iszero(sub(matmul(add(TS,ST),regroup),regroup))
    pairs=0
    for a in range(1,13):
        for b in range(1,13):
            k=a+b; empirical=F(0)
            for aa in range(a+1):
                for bb in range(b+1):
                    if aa+bb:
                        empirical+=F(comb(a,aa)*comb(b,bb),2**k)*F(aa*bb,aa+bb)
            closed=F(a*b,k*(k-1))*(F(k,2)-1+F(1,2**k))
            assert empirical==closed
            assert sum(comb(a,r)*comb(b,r) for r in range(min(a,b)+1))==comb(k,a)
            derivative=F(sum(r*comb(a,r)*comb(b,r) for r in range(min(a,b)+1)),comb(k,a))
            assert derivative==F(a*b,k)
            pairs+=1
    for k in range(2,66,2):
        c=F(k,4*(k-1))*(F(k,2)-1+F(1,2**k))
        assert 1-8*c/k==(1-F(1,2**(k-1)))/(k-1)>0
    # Rational-angle full-output/visibility identities; all round outcomes count.
    nu=F(97,100); sint=F(3,5); cost=F(4,5); z=cost**2
    ps=(1-nu)/2+nu*sint**2/4; dps=nu*sint*cost/2
    assert dps**2/(ps*(1-ps))==4*nu**2*z*(1-z)/(4-nu**2*(1+z)**2)
    numerator=nu**2*(1-z)*(55+9*z)-9*(4-nu**2*(1+z)**2)
    assert numerator==4*(nu**2*(16-7*z)-9)
    zdot=-2*sint*cost
    weights=[z/3,(1-z)/2,(3+z)/6]
    derivatives=[zdot/3,-zdot/2,zdot/6]
    assert sum(d*d/p for d,p in zip(derivatives,weights))/4==(1+z)/(3+z)
    return {'native_R_spectrum':'3/16 (rank4), 1/4 (rank2), 3/8 (rank2)',
            'pointwise_rational_axis_cosine':'4/5','pointwise_Bell_null_probability':'9/200',
            'parallel_recoupling':'two equal singlet-triplet weights',
            'multicopy_integer_pairs_checked':pairs,
            'balanced_mean_two_limit':'1 from below',
            'visibility_crossover':'nu^2 > 9/(16-7 cos(theta)^2)'}


def main():
    I=[(1,0),(0,0),(0,0),(1,0)]
    X=[(0,0),(1,0),(1,0),(0,0)]
    Y=[(0,0),(0,-1),(0,1),(0,0)]
    Z=[(1,0),(0,0),(0,0),(-1,0)]
    sig=[I,X,Y,Z]
    K=zero(16)
    for i in range(1,4):
        for j in range(i+1,4):
            v=[ga(a,gn(b)) for a,b in zip(gkron(sig[i],sig[j]),gkron(sig[j],sig[i]))]
            K=add(K,gvouter(v,8))
    P00=gvouter(gkron(I,I),4)
    trip=scale(F(1,2),add(add(gvouter(X,1),gvouter(Y,1)),gvouter(Z,1)))
    bell0=gvouter(I,2)
    P0t=kron(bell0,trip);Pt0=kron(trip,bell0)
    scalar=[(0,0)]*16
    for sigi in [X,Y,Z]:scalar=[ga(a,b) for a,b in zip(scalar,gkron(sigi,sigi))]
    J0=gvouter(scalar,12)
    J2=sub(sub(kron(trip,trip),J0),K)
    sectors=[P00,P0t,Pt0,J0,K,J2]
    assert [tr(P) for P in sectors]==[1,3,3,1,3,5]
    assert iszero(sub(sum_matrices(sectors),eye(16)))
    for i,A in enumerate(sectors):
        assert iszero(sub(matmul(A,A),A))
        for j,B in enumerate(sectors):
            if i!=j:assert iszero(matmul(A,B))
    C0=add(add(P00,scale(F(1,3),add(P0t,Pt0))),add(scale(F(1,3),J0),scale(F(2,15),J2)))
    C90=add(add(P00,scale(F(1,3),add(P0t,Pt0))),add(scale(F(1,6),K),scale(F(1,10),J2)))
    assert tr(C0)==tr(C90)==4
    assert iszero(matmul(C0,K))
    assert tr(matmul(K,C90))==F(1,2)
    # Exact feasible causal normalization and null effect T=alpha K.
    R=zero(8)
    for i,d in enumerate([4,5,3,4,4,3,5,4]):R[i][i]=F(d,16)
    for i,j,s in [(0,6,1),(1,7,1),(1,4,-1),(3,6,-1)]:R[i][j]=R[j][i]=F(s,16)
    rho=scale(F(1,2),eye(2));alpha=F(9,32)
    assert iszero(sub(ptrace(R,[2,2,2],0),kron(eye(2),rho)))
    rp=psd(R)
    slack=sub(kron(eye(2),R),scale(alpha,K));sp=psd(slack)
    Rinv=inverse(R)
    # Hence the physical final effect using R^{-1/2} is itself a projector.
    assert iszero(sub(matmul(matmul(K,kron(eye(2),Rinv)),K),scale(1/alpha,K)))
    # Exact matching dual: H is a sum of three rational rank-one PSD terms.
    a=[0]*16;b=[0]*16;c=[0]*16
    for i,v in [(0,1),(3,-1),(6,-4),(9,4),(12,1),(15,-1)]:a[i]=v
    for i,v in [(1,1),(4,-2),(7,2),(13,-3)]:b[i]=v
    for i,v in [(2,3),(8,-2),(11,2),(14,-1)]:c[i]=v
    H=scale(F(1,96),add(outer(a),add(scale(2,outer(b)),scale(2,outer(c)))))
    Zd=scale(F(3,32),[[F(x) for x in row] for row in [[1,0,0,-1],[0,2,0,0],[0,0,2,0],[-1,0,0,1]]])
    assert tr(matmul(H,K))==1
    assert iszero(sub(ptrace(H,[2,2,2,2],0),kron(eye(2),Zd)))
    assert iszero(sub(ptrace(Zd,[2,2],0),scale(alpha,eye(2))))
    assert tr(matmul(H,slack))==0
    # Explicit conversion to forward port order used by the parent's note:
    # (inE,outE,inF,outF). It is full reversal of the four qubits.
    Rp=reverse_qubits(R,3);Kp=reverse_qubits(K,4)
    Hp=reverse_qubits(H,4);Zp=reverse_qubits(Zd,2)
    assert [Rp[i][i] for i in range(8)]==[F(x,16) for x in [4,4,3,5,5,3,4,4]]
    assert iszero(sub(ptrace(Rp,[2,2,2],2),kron(rho,eye(2))))
    assert iszero(sub(ptrace(Hp,[2]*4,3),kron(Zp,eye(2))))
    assert iszero(sub(ptrace(Zp,[2,2],1),scale(alpha,eye(2))))
    assert tr(matmul(Hp,Kp))==1
    assert iszero(sub(reverse_qubits(slack,4),sub(kron(Rp,eye(2)),scale(alpha,Kp))))
    extra=supplementary_checks(K,R)
    result=dict(status='passed',scope='Exact finite primal/dual, native realization and pointwise/cost identities for NR-R18; general statistical and physical arguments remain analytic',
                port_order=['outF','inF','outE','inE'],optimal_null_tester_alpha=str(alpha),
                converted_port_order=['inE','outE','inF','outF'],wire_conversion='Reverse all four qubits; reverse three qubits of R and two qubits of Z',
                optimal_null_event_probability='(9/64) sin(theta)^2',
                all_ordinary_two_query_local_fi_limit='9/16',
                bell_parallel_event_probability='sin(theta)^2/8',bell_parallel_local_fi_limit='1/2',
                switch_event_probability='sin(theta)^2/4',switch_local_fi_limit='1',
                spin_sector_dimensions=[1,3,3,1,3,5],haar_choi_trace=4,
                primal_normalization_matrix_16R=[[str(16*x) for x in row] for row in R],
                primal_psd_pivots=rp,slack_psd_nonzero_pivots=sp,
                dual_gram_vectors=[a,b,c],dual_gram_weights=['1/96','2/96','2/96'],
                passed=['Bell sector projectors and exact orthogonal completeness','C0 kernel and C90 null weight','causal normalization prefix','R positive definite','causal tester slack PSD','native projective effect identity','dual PSD Gram form','dual objective normalization','both causal dual prefix equalities','complementary slackness','explicit wire-order reversal and converted prefix identities'])
    result['supplementary']=extra
    print(json.dumps({k:v for k,v in result.items() if k not in ['primal_normalization_matrix_16R','dual_gram_vectors']},indent=2))


def sum_matrices(mats):
    out=zero(len(mats[0]))
    for M in mats:out=add(out,M)
    return out


if __name__=='__main__':main()
