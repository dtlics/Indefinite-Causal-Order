"""Exact checks of cache CPTP effects and invariant states with quantum references."""
import json
import sympy as S
from itertools import product
from independent_exact_checks import create,polar_one,eq,zero,lift_action

def permute(d,k,a,b):
    states=list(product(range(d),repeat=k));ix={x:i for i,x in enumerate(states)};P=S.zeros(d**k)
    for col,x in enumerate(states):
        z=list(x);z[a],z[b]=z[b],z[a];P[ix[tuple(z)],col]=1
    return P

def exact_invariant_state(d,k):
    N=d**k;Z=2;I=S.eye(N)
    A=S.Matrix([[1,2],[0,1]]);B=S.Matrix([[0,1],[-1,2]]);C=S.Matrix([[2,-1],[1,0]])
    X=S.kronecker_product(I,A)+S.kronecker_product(permute(d,k,0,1),B)+S.kronecker_product(permute(d,k,1,2),C)
    rho=X*X.T;rho/=S.trace(rho)
    rest=d**(k-1)*Z; sigmas=[d*rho[j*rest:(j+1)*rest,j*rest:(j+1)*rest] for j in range(d)]
    for sig in sigmas:assert S.trace(sig)==1
    for j in range(d):
        for r in range(d):
            if j==r:continue
            entries=[]
            for labels in product(range(d),repeat=k-1):entries.extend([int(j not in labels and r not in labels)]*Z)
            P=S.diag(*entries)
            zero(P*sigmas[j]-sigmas[j]*P)
            eq(P*sigmas[j]*P,P*sigmas[r]*P)
            bad=S.trace((S.eye(rest)-P)*sigmas[j])
            assert bad <= (k-1)*(S.Rational(2,d+1)+S.Rational(1,d-1))
    # Every transposition intertwines U^tensor k for arbitrary U. Confirm a complex U instance too.
    U=S.eye(d);U[1,1]=S.I;U[0,0]=S.Rational(3,5);U[0,1]=-S.Rational(4,5)*S.I;U[1,0]=S.Rational(4,5);U[1,1]=S.Rational(3,5)*S.I
    eq(U.conjugate().T*U,S.eye(d));Uk=S.eye(1)
    for _ in range(k):Uk=S.kronecker_product(Uk,U)
    Uk=S.kronecker_product(Uk,S.eye(Z));eq(Uk*rho*Uk.conjugate().T,rho)
    return dict(test='invariant quantum-reference conditional block and occupation identities',d=d,k=k,reference=Z,status='PASS')

def cache_effects():
    d=2;F0=create(d,0,True);_,F1,_=polar_one(d,True)
    P=F0*F0.T;Q=S.eye(P.rows)-P;effectR=S.zeros(P.rows);effectB=S.zeros(P.rows)
    for j in range(d):
        proj=S.zeros(d);proj[j,j]=1;R=F0*proj*F0.T;effectR+=R.T*R
        ket=S.zeros(d,1);ket[j]=1
        for a in range(d):
            bra=S.zeros(1,d);bra[a]=1
            B=F1*S.kronecker_product(ket/S.sqrt(d),S.eye(d*d))*S.kronecker_product(bra,S.eye(d*d))*Q
            effectB+=B.T*B
    eq(effectR,P);eq(effectB,Q);eq(effectR+effectB,S.eye(P.rows))
    return dict(test='cache Kraus completeness with retrieval and birth',d=2,r=1,status='PASS')

if __name__=='__main__':
    out=[cache_effects()]+[exact_invariant_state(d,k) for d,k in [(2,3),(2,4),(3,3)]]
    print(json.dumps(dict(status='PASS',arithmetic='exact SymPy',cases=out),indent=2))
