"""Finite exact guards for two-layer all-good projector filtering.

This does not model feedback on other outcomes, reset/cooling channels,
microscopic clock records, an arbitrary ground state algorithm or hardware.
The all-dimension principal-angle decomposition and norm proof are analytic.
"""
from fractions import Fraction as F
import json


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def eye(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def add(a, b, weight=F(1)):
    return [[x+weight*y for x,y in zip(r,s)] for r,s in zip(a,b)]


def mul(a, b):
    n=len(a)
    return [[sum(a[i][l]*b[l][j] for l in range(n)) for j in range(n)] for i in range(n)]


def transpose(a):
    return list(map(list,zip(*a)))


def scale(a, w):
    return [[w*x for x in r] for r in a]


def power(a, n):
    result=eye(len(a))
    for _ in range(n):
        result=mul(result,a)
    return result


def verify():
    sectors=word_checks=norm_checks=trace_checks=ground_reject_checks=0
    for c,s in ((F(0),F(1)),(F(3,5),F(4,5)),(F(5,13),F(12,13)),
                (F(8,17),F(15,17)),(F(1),F(0))):
        require(c*c+s*s==1,'rational principal angle')
        p=[[F(1),F(0),F(0)],[F(0),F(1),F(0)],[F(0),F(0),F(0)]]
        q=[[F(1),F(0),F(0)],[F(0),c*c,c*s],[F(0),c*s,s*s]]
        require(mul(p,p)==p and mul(q,q)==q,'orthogonal projectors')
        ap=add(eye(3),p,-1)
        aq=add(eye(3),q,-1)
        native=scale(add(mul(p,q),mul(q,p)),F(1,2))
        sum_effect=[[F(0) for _ in range(3)] for _ in range(3)]
        ordinary_effect=[[F(0) for _ in range(3)] for _ in range(3)]
        for pj in (p,ap):
            for qj in (q,aq):
                ordinary=mul(pj,qj)
                if pj is p and qj is q:
                    require(ordinary[0][0]==1,'ordinary accepted ground amplitude')
                else:
                    require(all(ordinary[j][0]==ordinary[0][j]==0 for j in range(3)),
                            'ordinary failed branch ground annihilation')
                    ground_reject_checks+=1
                ordinary_effect=add(ordinary_effect,mul(transpose(ordinary),ordinary))
                for sign in (-1,1):
                    branch=scale(add(mul(pj,qj),mul(qj,pj),sign),F(1,2))
                    if pj is p and qj is q and sign==1:
                        require(branch[0][0]==1,'native accepted ground amplitude')
                    else:
                        require(all(branch[j][0]==branch[0][j]==0 for j in range(3)),
                                'native failed branch ground annihilation')
                        ground_reject_checks+=1
                    sum_effect=add(sum_effect,mul(transpose(branch),branch))
        require(sum_effect==ordinary_effect==eye(3),'complete accepted/reject instruments')
        require(native[0][0]==1 and all(native[0][j]==native[j][0]==0 for j in (1,2)),
                'common ground block')
        a=[r[1:] for r in mul(p,q)[1:]]
        C=[r[1:] for r in native[1:]]
        lp,lm=c*(1+c)/2,c*(c-1)/2
        require(sum(C[i][i] for i in range(2))==lp+lm,'native eigenvalue sum')
        require(C[0][0]*C[1][1]-C[0][1]*C[1][0]==lp*lm,'native eigenvalue product')
        require(lp>=abs(lm),'native norm eigenvalue')
        require(mul(mul([r[1:] for r in p[1:]], [r[1:] for r in q[1:]]),
                    [r[1:] for r in p[1:]])==[[c*c,F(0)],[F(0),F(0)]],
                'ordinary three-call sandwich')
        for k in range(1,21):
            require(power(a,k)==scale(a,c**(2*k-2)),'ordinary word power')
            word_checks+=1
            if k>=2:
                require(c**(2*k-1)<=lp**k,'ordinary repeated-word worst contraction')
                require(c**(4*k-2)<=lp**(2*k)+lm**(2*k),
                        'ordinary isotropic bad mass')
                norm_checks+=1
                trace_checks+=1
        sectors+=1
    return {'status':'passed','principal_angle_sectors':sectors,'complete_instruments':2*sectors,
            'word_power_checks':word_checks,'repeated_norm_checks':norm_checks,
            'isotropic_trace_checks':trace_checks,
            'individual_reject_ground_annihilation_checks':ground_reject_checks,
            'scope':'Finite rational projector/filter guards. Analytic Halmos decomposition and norms; no full-feedback, many-body success-rate optimum, bath clock or hardware claim.'}


if __name__=='__main__':
    print(json.dumps(verify(),sort_keys=True))
