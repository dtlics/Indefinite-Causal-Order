#!/usr/bin/env python3
"""Independent exact audit of a universal rational-kernel GYNI certificate.

Uses only the Python standard library and integer/rational arithmetic. No author
code, floating-point discovery arrays, solver, or word-reduction code is used.
The infinite dihedral group is represented faithfully by affine maps of Z.
Six semantic indices are handled explicitly, without reshape/permutation tricks.
"""
import argparse
from collections import defaultdict
from decimal import Decimal, localcontext
from fractions import Fraction as F
import gzip, hashlib, json, math, time
from pathlib import Path

ONE=(1,0)
def mul(a,b): return a[0]*b[0], a[0]*b[1]+a[1]
def inv(a): return a[0], -a[0]*a[1]
def val(w):
    z=ONE
    for b in w: z=mul(z,(-1,2*b))
    return z

def verify(summary_path, factors_path, dump_path=None):
    started=time.time()
    claim=json.loads(Path(summary_path).read_text())
    with gzip.open(factors_path,'rt') as stream: data=json.load(stream)
    assert data['kind']=='rational_kernel_slack_Gram_factors'
    r=F(data['r']); p,q=r.numerator,r.denominator
    L,bits=data['level'],data['bits']
    assert type(L) is int and L>=4
    assert type(bits) is int and bits>=3
    assert 0<=r<1
    words=[()]+[tuple((b+j)%2 for j in range(k)) for k in range(1,L+1) for b in (0,1)]
    elements=[val(w) for w in words]
    n=len(words); N=n*n; lookup={v:i for i,v in enumerate(elements)}
    assert len(lookup)==n
    overlap={(i,j):mul(inv(elements[j]),elements[i]) for i in range(n) for j in range(n)}
    assert all((overlap[i,j]==ONE)==(i==j) for i in range(n) for j in range(n))
    U=mul(val((0,)),val((1,)))
    # Q=q^2 q_r and T=Q^2: group algebra convolution independent of word strings.
    Q={ONE:q*q+p*p,U:p*q,inv(U):p*q}
    T=defaultdict(int)
    for a,c in Q.items():
        for b,d in Q.items(): T[mul(a,b)]+=c*d
    T=dict(T)
    alpha=T[ONE]; beta=T[U]; gamma=T[mul(U,U)]
    assert alpha==q**4+4*p*p*q*q+p**4
    assert beta==2*p*q*(q*q+p*p) and gamma==p*p*q*q
    # Explicit centrality and endpoint lower bound (1-r)^2.
    for refl in [val((0,)),val((1,))]:
        assert {mul(refl,g):c for g,c in Q.items()}=={mul(g,refl):c for g,c in Q.items()}
    endpoint_q={str(s):F(q*q+p*p+2*p*q*s,q*q) for s in [-1,1]}
    assert min(endpoint_q.values())==(1-r)**2>0
    groups=defaultdict(list)
    for setting in range(2):
        for i in range(n):
            for j in range(n): groups[overlap[i,j]].append((setting,i,j))
    assert set(T)<=set(groups)
    m={w:len(g) for w,g in groups.items()}
    M=math.lcm(*m.values())
    # Weighted least-squares projection group means onto the line spanned by T.
    weighted={w:T.get(w,0)*(M//m[w]) for w in groups}
    A=sum(T.get(w,0)*weighted[w] for w in groups)
    B=M*A
    assert A>0
    factors=data['factors']
    assert len(factors)==4
    for mat in factors:
        assert len(mat)==N and all(len(row)==N for row in mat)
        assert all(type(z) is int for row in mat for z in row)
    fden=2**(2*bits); kden=64*q**8; D=math.lcm(fden,kden)
    targets=[]; H0=[]
    for x in range(2):
        for y in range(2):
            a=[0]*n; b=[0]*n
            for g,c in Q.items():
                a[lookup[g]]+=c
                a[lookup[mul(g,val((x,)))]]+=(-1)**y*c
                b[lookup[g]]+=c
                b[lookup[mul(g,val((y,)))]]+=(-1)**x*c
            k=[aa*bb for aa in a for bb in b]
            tar=[[k[i]*k[j]*(D//kden) for j in range(N)] for i in range(N)]
            mat=factors[2*x+y]
            h=[[tar[i][j]+sum(aa*bb for aa,bb in zip(mat[i],mat[j]))*(D//fden) for j in range(N)] for i in range(N)]
            targets.append(tar); H0.append(h)
    def get(H,x,y,u,v,up,vp): return H[2*x+y][u*n+v][up*n+vp]
    def blank(): return [[[0]*N for _ in range(N)] for _ in range(4)]
    def project_side(H,side):
        P=blank()
        # fixed=(other setting, other word, other primed word).
        for fixed in range(2):
            for a in range(n):
                for ap in range(n):
                    def entry(setting,b,bp):
                        return get(H,fixed,setting,a,b,ap,bp) if side=='B' else get(H,setting,fixed,b,a,bp,ap)
                    sums={w:sum(entry(setting,b,bp) for setting,b,bp in g) for w,g in groups.items()}
                    dot=sum(weighted[w]*sums[w] for w in groups)
                    for w,g in groups.items():
                        correction=(M//m[w])*(A*sums[w]-T.get(w,0)*dot)
                        for setting,b,bp in g:
                            z=B*entry(setting,b,bp)-correction
                            if side=='B': P[2*fixed+setting][a*n+b][ap*n+bp]=z
                            else: P[2*setting+fixed][b*n+a][bp*n+ap]=z
        return P
    P=project_side(project_side(H0,'B'),'A')
    # The opposite order gives exactly the same integer tensor.
    assert P==project_side(project_side(H0,'A'),'B')
    E=[[[B*B*H0[k][i][j]-P[k][i][j] for j in range(N)] for i in range(N)] for k in range(4)]
    norms=[]
    for e in E:
        assert all(e[i][j]==e[j][i] for i in range(N) for j in range(N))
        f2=sum(z*z for row in e for z in row)
        f=math.isqrt(f2)+(math.isqrt(f2)**2<f2)
        row=max(sum(abs(z) for z in rr) for rr in e)
        norms.append({'squared_Frobenius':str(f2),'ceiling_Frobenius':str(f),'absolute_row_bound':str(row)})
    error=max(min(int(z['ceiling_Frobenius']),int(z['absolute_row_bound'])) for z in norms)
    # Independent explicit positive repair. Jnum=mu I+sum positive rank-one terms.
    mu=alpha-2*beta-2*gamma
    assert mu>0 and beta>=0 and gamma>=0
    J=[[mu if i==j else 0 for j in range(n)] for i in range(n)]
    J[lookup[ONE]][lookup[ONE]]+=n*mu
    for coef,g in [(beta,U),(gamma,mul(U,U))]:
        vec=[0]*n; vec[lookup[ONE]]+=1; vec[lookup[g]]+=1
        for i in range(n):
            for j in range(n): J[i][j]+=2*n*coef*vec[i]*vec[j]
    Jden=2*n*q**4
    eps=F(mu,Jden)
    ja=defaultdict(int)
    for i in range(n):
        for j in range(n): ja[overlap[i,j]]+=J[i][j]
    assert all(ja[w]==2*n*T.get(w,0) for w in groups)
    JJ=[[J[i//n][j//n]*J[i%n][j%n] for j in range(N)] for i in range(N)]
    H=[[[mu*mu*P[k][i][j]+error*JJ[i][j] for j in range(N)] for i in range(N)] for k in range(4)]
    Hden=mu*mu*D*B*B
    for k in range(4):
        assert all(H[k][i][j]==H[k][j][i] for i in range(N) for j in range(N))
        assert error**2>=int(norms[k]['squared_Frobenius']) or error>=int(norms[k]['absolute_row_bound'])
        # Exact CP dominance decomposition, with LL^T and norm-bounded remainder.
        assert all(H[k][i][j]-mu*mu*B*B*targets[k][i][j]
                   ==mu*mu*B*B*(H0[k][i][j]-targets[k][i][j])+error*JJ[i][j]-mu*mu*E[k][i][j]
                   for i in range(N) for j in range(N))
    count=0
    for fixed in range(2):
        for a in range(n):
            for ap in range(n):
                sb={w:sum(get(H,fixed,y,a,v,ap,vp) for y,v,vp in g) for w,g in groups.items()}
                sa={w:sum(get(H,x,fixed,u,a,up,ap) for x,u,up in g) for w,g in groups.items()}
                for w in groups:
                    assert alpha*sb[w]==T.get(w,0)*sb[ONE]
                    assert alpha*sa[w]==T.get(w,0)*sa[ONE]
                    count+=2
    # Fully independent joint expansion checks TP, not merely its trace.
    total=defaultdict(int)
    for x in range(2):
        for y in range(2):
            for u in range(n):
                for v in range(n):
                    for up in range(n):
                        for vp in range(n): total[overlap[u,up],overlap[v,vp]]+=get(H,x,y,u,v,up,vp)
    trace=sum(H[k][i][i] for k in range(4) for i in range(N))
    assert total[ONE,ONE]==trace
    assert all(alpha*alpha*c==trace*T.get(a,0)*T.get(b,0) for (a,b),c in total.items())
    bound=F(trace*q**8,Hden*alpha*alpha)
    p_trace=sum(P[k][i][i] for k in range(4) for i in range(N))
    base=F(p_trace*q**8,D*B*B*alpha*alpha)
    repair=bound-base
    assert repair==4*F(error,D*B*B)/(eps*eps)
    assert bound==F(claim['upper_rational'])
    assert repair==F(claim['repair_cost_rational'])
    for key,value in [('r',str(r)),('word_length',L),('word_count',n),('Gram_dimension',N),('NS_proportional_coefficient_checks',count)]: assert claim[key]==value
    assert bound>0
    with localcontext() as ctx:
        ctx.prec=80
        dec=str(Decimal(bound.numerator)/Decimal(bound.denominator))
        rep=str(Decimal(repair.numerator)/Decimal(repair.denominator))
    out={'status':'PASS_INDEPENDENT_EXACT_RATIONAL_KERNEL_AUDIT','r':str(r),'word_length':L,'root_bits':bits,'word_count':n,'Gram_dimension':N,'upper_rational':str(bound),'upper_decimal':dec,'repair_cost_rational':str(repair),'repair_cost_decimal':rep,'base_scale_rational':str(base),'flagwise_NS_equalities_checked':count,'TP_coefficient_pairs_checked':len(total),'overlap_groups':len(groups),'group_sizes':sorted(m.values()),'projection_orders_equal':True,'local_q2_identity_coefficient':str(F(alpha,q**4)),'local_repair_minimum_eigenvalue_lower_bound':str(eps),'rational_denominator_uniform_lower_bound':str((1-r)**2),'endpoint_q_values':{k:str(v) for k,v in endpoint_q.items()},'projection_denominator_per_side':str(B),'input_common_denominator':str(D),'PSD_error_integer_bound':str(error),'final_common_denominator':str(Hden),'norm_bounds':norms,'factor_sha256':hashlib.sha256(Path(factors_path).read_bytes()).hexdigest(),'summary_sha256':hashlib.sha256(Path(summary_path).read_bytes()).hexdigest(),'uses_author_code':False,'uses_floating_arithmetic_for_proof':False,'uses_SDP_solver':False,'seconds':time.time()-started}
    if dump_path:
        with gzip.open(dump_path,'wt') as f: json.dump({'words':words,'r':str(r),'denominator':str(Hden),'matrices':H},f)
    return out

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('summary');p.add_argument('factors');p.add_argument('--out');p.add_argument('--dump');a=p.parse_args()
    result=verify(a.summary,a.factors,a.dump)
    output=json.dumps(result,indent=2)+'\n'
    if a.out: Path(a.out).write_text(output)
    print(output,end='')
