"""Exact invariant objectives for globally noisy anticommuting gate products.

The six-wire convention is (P,AI,AO,BI,BO,F), signature (-,+,-,+,-,+).
For each diagram B, Tr(B Omega_Haar)=Tr(B Omega_canonical), because B
commutes with the mixed-tensor action. The canonical matrices are X,Y,Z
tensor I_(D/2). All contractions below use Gaussian integers and Fractions.
No Haar quadrature, floating eigensolver, or Weingarten values enter f_i.
"""
from __future__ import annotations
if not __debug__:
    raise RuntimeError('Exact objective checks require Python without -O.')

import argparse
from fractions import Fraction
import itertools
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
SIGNATURE=(-1,1,-1,1,-1,1)
ZERO=(0,0)
ONE=(1,0)


def _gadd(a,b): return (a[0]+b[0],a[1]+b[1])
def _gmul(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def _conj(a): return (a[0],-a[1])
def _transpose(a): return (a[0],a[2],a[1],a[3])
def _mconj(a): return tuple(_conj(x) for x in a)
def _mmul(a,b):
    return tuple(_gadd(_gmul(a[2*i],b[j]),_gmul(a[2*i+1],b[2+j]))
                 for i in range(2) for j in range(2))


II=(ONE,ZERO,ZERO,ONE)
XX=(ZERO,ONE,ONE,ZERO)
YY=(ZERO,(0,-1),(0,1),ZERO)
ZZ=(ONE,ZERO,ZERO,(-1,0))


def _fraction(value):
    # Decimal gamma=.1 must mean 1/10 rather than its binary expansion.
    return value if isinstance(value,Fraction) else Fraction(str(value))


def _edges(unitary_first,unitary_second,second_label,kind):
    """(u,v,M) denotes the matrix entry M[index_u,index_v]."""
    n=6
    edges=[]
    if kind=='fidelity':
        edges.extend(((n+5,n+0,ZZ),(5,0,_mconj(ZZ))))
    else:
        edges.extend(((0,n+0,II),(5,n+5,II)))
    for incoming,outgoing,unitary,mat in ((1,2,unitary_first,XX),
        (3,4,unitary_second,YY if second_label=='B' else XX)):
        if unitary:
            # J_M^T has M* on the ket/bottom indices and M on bra/top.
            edges.extend(((n+outgoing,n+incoming,_mconj(mat)),
                          (outgoing,incoming,mat)))
        else:
            edges.extend(((incoming,n+incoming,II),(outgoing,n+outgoing,II)))
    return edges


def _diagram_contraction(partner,D,edges):
    """Trace contraction of a pairing with a product of Pauli/delta edges."""
    if len(partner)!=12 or any(partner[partner[i]]!=i or partner[i]==i for i in range(12)):
        raise ValueError('Expected a fixed-point-free partner array on twelve vertices')
    all_edges=[(i,j,II) for i,j in enumerate(partner) if i<j]+list(edges)
    adjacency=[[] for _ in range(12)]
    for k,(u,v,mat) in enumerate(all_edges):
        adjacency[u].append(k);adjacency[v].append(k)
    assert all(len(a)==2 for a in adjacency)
    visited=set()
    answer=ONE
    m=D//2
    for start in range(12):
        if all(k in visited for k in adjacency[start]):continue
        current=start
        product=II
        while True:
            edge=next(k for k in adjacency[current] if k not in visited)
            visited.add(edge)
            u,v,mat=all_edges[edge]
            if current==u:
                product=_mmul(product,mat);current=v
            else:
                product=_mmul(product,_transpose(mat));current=u
            if current==start:break
        trace=_gadd(product[0],product[3])
        answer=_gmul(answer,(m*trace[0],m*trace[1]))
    assert len(visited)==12
    assert answer[1]==0,answer
    return answer[0]


def _check(algebra,D,second_label,kind):
    if not isinstance(D,int) or D<2 or D%2:raise ValueError('D must be a positive even integer >=2')
    if tuple(algebra.signature)!=SIGNATURE:raise ValueError('Task requires signature (-,+,-,+,-,+)')
    if second_label not in ('A','B'):raise ValueError("second_label must be 'A' (EE) or 'B' (EF)")
    if kind not in ('fidelity','probability'):raise ValueError("kind must be 'fidelity' or 'probability'")


def objective_vector(algebra,D,gamma,second_label='B',kind='fidelity'):
    """Return exact f_i=Tr(B_i Omega), in algebra basis order.

    gamma is full D-dimensional replacement noise, not hidden-logical noise.
    second_label='A' means two memoryless uses of the SAME first oracle.
    """
    _check(algebra,D,second_label,kind)
    gamma=_fraction(gamma)
    if not 0<=gamma<=1:raise ValueError('Noise gamma must be in [0,1]')
    result=[Fraction(0) for _ in algebra.pairs]
    for first,second in itertools.product((False,True),repeat=2):
        factor=(1-gamma if first else gamma/D)*(1-gamma if second else gamma/D)
        factor/=D**(2 if kind=='fidelity' else 1)
        edges=_edges(first,second,second_label,kind)
        for i,partner in enumerate(algebra.pairs):
            result[i]+=factor*_diagram_contraction(partner,D,edges)
    return result


def operator_coefficients(algebra,D,gamma,second_label='B',kind='fidelity'):
    """Return exact w with Omega=sum_i w_i B_i, for faithful D>=6.

    Partial transpose is Hilbert-Schmidt isometric. Thus the Gram matrix is
    G_ij=D**cycles(pi_i^-1 pi_j). The right-hand side is f_star, not f.
    """
    if D<algebra.n:raise ValueError('Unique exact coefficients require D>=number of wires')
    f=objective_vector(algebra,D,gamma,second_label,kind)
    from brauer_weingarten import gram_inverse_vector
    return gram_inverse_vector(algebra.permutations,D,[f[int(i)] for i in algebra.star])


class _ValidationAlgebra:
    """Independent permutation/PT construction; not used by production API."""
    signature=SIGNATURE
    n=6
    def __init__(self):
        self.permutations=list(itertools.permutations(range(6)))
        lookup={p:i for i,p in enumerate(self.permutations)}
        self.pairs=[];self.star=[]
        for p in self.permutations:
            partners=[-1]*12
            def flip(v):
                wire=v%6
                return (v+6)%12 if SIGNATURE[wire]<0 else v
            for j in range(6):
                u,v=flip(p[j]),flip(6+j)
                partners[u]=v;partners[v]=u
            self.pairs.append(tuple(partners))
            inverse=tuple(p.index(j) for j in range(6))
            self.star.append(lookup[inverse])


def _entry(mat,row,col,D):
    """Physical D-by-D entry of mat tensor I_(D/2), no diagram graph."""
    m=D//2
    return mat[2*(row//m)+(col//m)] if row%m==col%m else ZERO


def _physical_canonical_entry(row,col,D,gamma,second_label,kind):
    """Physical six-wire canonical objective matrix entry, exact and sparse."""
    pr,ai,ao,bi,bo,fr=row
    pc,aj,ap,bj,bp,fc=col
    if kind=='fidelity':
        target=_gmul(_entry(ZZ,fr,pr,D),_conj(_entry(ZZ,fc,pc,D)))
        denom=D*D
    else:
        target=ONE if pr==pc and fr==fc else ZERO
        denom=D
    if target==ZERO:return Fraction(0)
    # Transposed input-slot Choi matrices.
    a=_gmul(_entry(XX,ap,aj,D),_conj(_entry(XX,ao,ai,D)))
    second=YY if second_label=='B' else XX
    b=_gmul(_entry(second,bp,bj,D),_conj(_entry(second,bo,bi,D)))
    assert target[1]==a[1]==b[1]==0
    ja=(1-gamma)*a[0]+(gamma/D if ai==aj and ao==ap else 0)
    jb=(1-gamma)*b[0]+(gamma/D if bi==bj and bo==bp else 0)
    return target[0]*ja*jb/denom


def _physical_trace(p,D,gamma,second_label,kind):
    """Enumerate the D**6 nonzeros of a physical PT permutation matrix."""
    answer=Fraction(0)
    for inputs in itertools.product(range(D),repeat=6):
        top=[0]*6
        for j in range(6):top[p[j]]=inputs[j]
        bottom=list(inputs)
        for wire,sign in enumerate(SIGNATURE):
            if sign<0:top[wire],bottom[wire]=bottom[wire],top[wire]
        # Tr(B Omega) uses Omega[bottom,top].
        answer+=_physical_canonical_entry(bottom,top,D,gamma,second_label,kind)
    return answer


def validate():
    a=_ValidationAlgebra()
    gamma=Fraction(1,10)
    tests=[]
    # Include all identity/single-swap and varied cup diagrams, with fixed seed
    # independent of graph contraction. D2 checks the full720 basis.
    selected4=sorted(set([0,1,2,5,6,23,24,57,119,120,245,359,518,600,719]))
    for D in (2,4):
        indices=range(720) if D==2 else selected4
        for label in ('A','B'):
            for kind in ('fidelity','probability'):
                values=objective_vector(a,D,gamma,label,kind)
                for i in indices:
                    direct=_physical_trace(a.permutations[i],D,gamma,label,kind)
                    assert direct==values[i],(D,label,kind,i,direct,values[i])
                tests.append({'D':D,'second_label':label,'kind':kind,'physical_diagrams_checked':len(indices)})
    out={'status':'passed','exact_sparse_physical_matrix_checks':tests,
         'arithmetic':'Gaussian integers and exact Fraction contractions only',
         'scope':'independent physical matrix-entry check of all D2 diagrams and selected D4 diagrams; no numerical library'}
    (HERE/'brauer_objective_validation.json').write_text(json.dumps(out,indent=2))
    return out


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--validate',action='store_true');args=parser.parse_args()
    if args.validate:print(json.dumps(validate(),indent=2))
    else:parser.error('Use --validate for independent physical checks')
