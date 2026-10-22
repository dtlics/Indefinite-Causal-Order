"""Exact diagram/Pauli structural checks for the ideal fidelity remainder.

All identities hold formally for A=X tensor I_m, B=Y tensor I_m,
W=BA, D=2m. Gaussian-integer 2x2 products and symbolic loop powers of D
replace finite-D numerical matrices. Representation dimensions are audited
separately by verify_dimensions.py.
"""
from pathlib import Path
from itertools import permutations,combinations,product
from fractions import Fraction as F
import json
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'algebra'))
from brauer_exact_replay import ExactBrauerAlgebra as Algebra
from brauer_objective import II,XX,YY,_mmul,_transpose,_gadd,_gmul,ONE

if not __debug__:
    raise RuntimeError('Exact structural proof checks require Python without -O.')

# Plus wires0,1,2 are AI,BI,F; minus wires3,4,5 are P,AO,BO.
GATE_EDGES=[(0,4,XX),(1,5,YY),(2,3,_mmul(YY,XX))]


def network(cups):
    edges=GATE_EDGES+[(i,j,II) for i,j in cups]
    adjacent=[[] for _ in range(6)]
    for e,(i,j,mat) in enumerate(edges):adjacent[i].append(e);adjacent[j].append(e)
    visited=set();coefficient=ONE;loops=0;open_matrices=[]
    # Every open path begins on its free plus wire. Closed components
    # likewise begin on a plus wire, so no hidden matrix transpose occurs.
    starts=[i for i in range(3) if len(adjacent[i])==1]+list(range(3))
    for start in starts:
        if all(e in visited for e in adjacent[start]):continue
        current=start;matrix=II;closed=False
        while True:
            candidates=[e for e in adjacent[current] if e not in visited]
            if not candidates:break
            e=candidates[0];visited.add(e);u,v,mat=edges[e]
            if current==u:matrix=_mmul(matrix,mat);current=v
            else:matrix=_mmul(matrix,_transpose(mat));current=u
            if current==start:closed=True;break
        if closed:
            trace=_gadd(matrix[0],matrix[3]);loops+=1
            assert trace[0]%2==trace[1]%2==0
            coefficient=_gmul(coefficient,(trace[0]//2,trace[1]//2))
        else:open_matrices.append(matrix)
    assert len(visited)==len(edges)
    return coefficient,loops,open_matrices


def cycles(p):
    seen=set();out=0
    for i in range(len(p)):
        if i in seen:continue
        out+=1;j=i
        while j not in seen:seen.add(j);j=p[j]
    return out


def main():
    perms=list(permutations(range(3)));id3=(0,1,2);rev=(2,0,1)
    invariant=[]
    for p in perms:
        c,loops,opened=network([(i,3+p[i]) for i in range(3)])
        assert not opened
        expected=1 if p==id3 else (-1 if p==rev else 0)
        assert c==(expected,0)
        assert loops==1 or expected==0
        # Gram times(e_EF-e_FE) is exactly D(D^2-1) times that vector.
        inv=tuple(p.index(i) for i in range(3));poly=[0]*4
        poly[cycles(tuple(inv[i] for i in id3))]+=1
        poly[cycles(tuple(inv[i] for i in rev))]-=1
        assert poly==[0,-expected,0,expected]
        invariant.append({'matching':p,'overlap_with_normalized_g':expected})

    two=[]
    for plus_used in combinations(range(3),2):
        for minus_used in combinations(range(3,6),2):
            for pairing in permutations(minus_used):
                cups=list(zip(plus_used,pairing));c,loops,opened=network(cups)
                assert len(opened)==1
                if c!=(0,0):
                    # All remaining open matrices are scalar I, so every
                    # adjoint/traceless matrix has zero contraction.
                    mat=opened[0]
                    assert mat[1]==mat[2]==(0,0) and mat[0]==mat[3]
                    assert loops==0 and mat[0] in ((1,0),(-1,0),(0,1),(0,-1))
                two.append({'cups':cups,'zero':c==(0,0),
                    'remaining_open_matrix_scalar_when_nonzero':True})
    assert len(two)==18

    one=[]
    for i,j in product(range(3),range(3,6)):
        c,loops,opened=network([(i,j)])
        assert len(opened)==2
        zero=c==(0,0)
        if not zero:
            assert loops==0
            for mat in opened:
                # Every path is a product of unitary Paulis. Check it
                # exactly rather than infer its norm from a numerical SVD.
                adj=tuple((z[0],-z[1]) for z in _transpose(mat))
                assert _mmul(adj,mat)==II
        one.append({'cup':(i,j),'zero':zero,
            'raw_unnormalized_contraction_squared_norm':'0' if zero else 'D^2',
            'normalized_objective_g_Pi_projection_squared_norm':'0' if zero else '1/D'})
    assert sum(not x['zero'] for x in one)==6

    # Exact projector-overlap/TL identities, with no representation cache.
    algebra=Algebra((1,1,1,-1,-1,-1));indices={}
    for i,j in product(range(3),range(3,6)):
        p=list(range(6));p[i],p[j]=p[j],p[i]
        indices[i,j]=algebra.index_by_permutation[tuple(p)]
    shared=disjoint=0
    for e,f in combinations(indices,2):
        ef,ell=algebra.multiply(indices[e],indices[f])
        if e[0]==f[0] or e[1]==f[1]:
            efe,more=algebra.multiply(ef,indices[e])
            assert efe==indices[e] and ell+more==0
            shared+=1
        else:
            fe,other=algebra.multiply(indices[f],indices[e])
            assert (ef,ell)==(fe,other) and algebra.cups[ef]==2
            disjoint+=1
    assert shared==18 and disjoint==18
    assert all(sum(e!=f and(e[0]==f[0] or e[1]==f[1]) for f in indices)==4 for e in indices)

    # The displayed finite-n constants use only upper bounds at n8,D256.
    D=256;intercept=F(4617,10000*D)+F(3,200)*F(65536,65535)**2+F(1,512)
    assert intercept==F(2749735788563,146597076480000)
    ordinary=F(81,100)+intercept/F(9,10)
    assert ordinary==F(109619004542483,131937368832000) and ordinary<F(831,1000)
    out={'status':'passed','arithmetic':'stdlib Gaussian integers and formal D loop powers',
        'singlet_matching_checks':invariant,'adjoint_two_cup_checks':two,
        'one_cup_checks':one,'shared_cup_TL_identities':shared,
        'disjoint_cup_two_cup_range_identities':disjoint,'rook_degree':4,
        'normalization':'g=raw_tensor/D; ||g||^2=D; one-cup totalweight<=12/D',
        'finite_local_depolarization_intercept_upper':str(intercept),
        'finite_local_depolarization_ordinary_fidelity_upper':str(ordinary),
        'scope':'structural contraction identities; complete representation/dimension proof reviewed separately'}
    (HERE/'local_noise_independent_structural_audit.json').write_text(json.dumps(out,indent=2))
    print(json.dumps({k:v for k,v in out.items() if k not in ('singlet_matching_checks','adjoint_two_cup_checks','one_cup_checks')},indent=2))


if __name__=='__main__':main()
