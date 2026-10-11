"""Independent small-sector audit of normalized bosonic and fresh-label maps.
Exact SymPy algebra; no candidate checker is imported. d=3 is a local
operator test, not a claim that the n-qubit task allows dimension3.
"""
from itertools import combinations_with_replacement,product,permutations
from collections import Counter
import sympy as S
import json

def zero(A):
    assert all(S.simplify(x)==0 for x in A), 'nonzero matrix'

def eq(A,B): zero(A-B)

def modes(d,r): return list(combinations_with_replacement(range(d*d),r))

def create(d,r,left=False):
    ins,outs=modes(d,r),modes(d,r+1); ix={v:i for i,v in enumerate(outs)}
    E=S.zeros(d*len(outs),d*len(ins))
    for q,R in product(range(d),ins):
        col=q*len(ins)+ins.index(R)
        for z in range(d):
            x,y=(q,z) if left else (z,q); m=x*d+y
            Rn=tuple(sorted(R+(m,)))
            E[z*len(outs)+ix[Rn],col]=S.sqrt(S.Rational(R.count(m)+1,d))
    return E

def symmetry(d,r):
    ins=modes(d,r); alltuples=list(product(range(d*d),repeat=r)); ix={v:i for i,v in enumerate(alltuples)}
    V=S.zeros(len(alltuples),len(ins))
    for c,R in enumerate(ins):
        ps=set(permutations(R)); amp=1/S.sqrt(len(ps))
        for p in ps: V[ix[p],c]=amp
    eq(V.T*V,S.eye(len(ins)));return V

def gram_swaps(d,r,left=False):
    states=list(product(range(d),*([range(d*d)]*r)));ix={v:i for i,v in enumerate(states)}
    J=S.zeros(len(states))
    for col,state in enumerate(states):
        for a in range(r):
            q=state[0]; m=state[a+1]; x,y=divmod(m,d); new=list(state)
            new[0]=x if left else y; new[a+1]=q*d+y if left else x*d+q
            J[ix[tuple(new)],col]+=1
    V=S.kronecker_product(S.eye(d),symmetry(d,r))
    return V.T*(S.eye(len(states))+J/d)*V

def label_projector(d,r,k):
    return S.diag(*[int(all(m//d<k for m in R)) for R in modes(d,r)])

def number(d,r,label):
    return S.diag(*[sum(m//d==label for m in R) for R in modes(d,r)])

def polar_one(d,left=False):
    E=create(d,1,left);Gm=E.T*E;J=d*(Gm-S.eye(d**3));eq(J*J,S.eye(d**3))
    K=(S.eye(d**3)+J)/(2*S.sqrt(1+S.Rational(1,d)))+(S.eye(d**3)-J)/(2*S.sqrt(1-S.Rational(1,d)))
    G=E*K;eq(G.T*G,S.eye(d**3));return E,G,K

def one_particle_action(d,U):return S.kronecker_product(U,S.eye(d))

def lift_action(d,r,U):
    V=symmetry(d,r); action=S.eye(1)
    for _ in range(r): action=S.kronecker_product(action,one_particle_action(d,U))
    return V.T*action*V

def main():
    out=[]
    for d,r in [(2,0),(2,1),(2,2),(3,1)]:
        for left in [False,True]:
            E=create(d,r,left);eq(E.T*E,gram_swaps(d,r,left))
        out.append(dict(test='creation Gram and occupation normalization',d=d,r=r,status='PASS'))
    for d in [2,3]:
        E,G,K=polar_one(d)
        for label in range(d):
            N=S.kronecker_product(S.eye(d),number(d,1,label));zero(K*N-N*K)
        for k in range(d+1):
            Pin=S.kronecker_product(S.eye(d),label_projector(d,1,k));Pout=S.kronecker_product(S.eye(d),label_projector(d,2,k))
            eq(Pin*E.T*(S.eye(E.rows)-Pout)*E*Pin,S.Rational(d-k,d)*Pin)
            zero(Pout*G*(S.eye(G.cols)-Pin))
        out.append(dict(test='polar isometry, right-label occupation preservation, fresh norm identity',d=d,r=1,status='PASS'))
    # Non-real change of label basis: exact left equivariance, including polar factor.
    d=2; E,F,K=polar_one(d,True)
    for U in [S.Matrix([[S.Rational(3,5),S.Rational(-4,5)],[S.Rational(4,5),S.Rational(3,5)]]),S.diag(1,S.I),S.Matrix([[0,1],[1,0]])]:
        old=lift_action(d,1,U);new=lift_action(d,2,U)
        eq(S.kronecker_product(S.eye(d),new)*F,F*S.kronecker_product(U,old))
        P=F*F.T;A=S.kronecker_product(S.eye(d),new);zero(A*P-P*A)
    out.append(dict(test='complex and rational label equivariance and image projector',d=2,r=1,status='PASS'))
    # Orthogonal birth directions identify each bosonic sector with ordered image registers.
    for d,r in [(2,1),(3,1),(3,2)]:
        Rs=modes(d,r);Rnext=modes(d,r+1);Rix={R:i for i,R in enumerate(Rs)};Nix={R:i for i,R in enumerate(Rnext)}
        ys=list(product(range(d),repeat=r)); ysnew=list(product(range(d),repeat=r+1))
        V=S.zeros(len(Rs),d**r);Vn=S.zeros(len(Rnext),d**(r+1))
        for c,Y in enumerate(ys):V[Rix[tuple(a*d+Y[a] for a in range(r))],c]=1
        for c,Y in enumerate(ysnew):Vn[Nix[tuple(a*d+Y[a] for a in range(r+1))],c]=1
        eq(V.T*V,S.eye(d**r));eq(Vn.T*Vn,S.eye(d**(r+1)))
        E=create(d,r);Pout=S.zeros(len(Rnext),E.rows)
        for j in range(len(Rnext)):Pout[j,r*len(Rnext)+j]=1
        actual=Vn.T*Pout*E*S.kronecker_product(S.eye(d),V)
        ideal=S.zeros(d**(r+1),d**(r+1));iy={Y:i for i,Y in enumerate(ysnew)}
        for q,Y in product(range(d),ys):ideal[iy[Y+(q,)],q*d**r+ys.index(Y)]=1/S.sqrt(d)
        eq(actual,ideal)
        out.append(dict(test='fresh orthogonal birth factorization with inert old images',d=d,r=r,status='PASS'))
    print(json.dumps(dict(status='PASS',arithmetic='exact SymPy',cases=out),indent=2))
if __name__=='__main__':main()
