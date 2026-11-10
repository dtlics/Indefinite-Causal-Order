"""Exact finite-order certificates, standard-library arithmetic only."""
from fractions import Fraction as F
import itertools,json,math
from pathlib import Path
# Standalone copy avoids a numpy/scipy dependency in the exact verifier.
def cross_exp(pi,sig,kind):
    m=len(pi);p=list(range(2*m));mark={}
    def root(i):
        while p[i]!=i:i=p[i]
        return i
    def union(a,b):
        a,b=root(a),root(b)
        if a!=b:p[b]=a
    for s in (pi,sig):
        for j in range(1,m):union(m+s[j],s[j-1])
    fixed=[(m+pi[0],0),(m+sig[0],int(kind=='id')),(pi[-1],int(kind=='dep')),(sig[-1],1)]
    # id: inputs 0,1 outputs 0,1. dep: inputs 0,0 outputs 1,1.
    for i,c in fixed:
        r=root(i)
        if r in mark and mark[r]!=c:return None
        mark[r]=c
    return len({root(i) for i in range(2*m)})-len(mark)-m+int(kind=='dep')

def matrices(m,d):
    ps=list(itertools.permutations(range(m)));idx={p:i for i,p in enumerate(ps)}
    aa=[cross_exp(ps[0],s,'id') for s in ps]
    bb=[cross_exp(ps[0],s,'dep') for s in ps]
    av=[F(0) if x is None else F(d)**x for x in aa]
    bv=[F(0) if x is None else F(d)**x for x in bb]
    A=[];B=[]
    for p in ps:
        inv=[0]*m
        for j,a in enumerate(p):inv[a]=j
        ids=[idx[tuple(inv[a] for a in s)] for s in ps]
        A.append([av[j] for j in ids]); B.append([bv[j] for j in ids])
    return ps,A,B

def psd(M):
    M=[row[:] for row in M];n=len(M);positive=zero=0
    assert all(M[i][j]==M[j][i] for i in range(n) for j in range(n))
    for k in range(n):
        p=M[k][k]
        if p<0:return False,positive,zero
        if not p:
            if any(M[k][j] for j in range(k+1,n)):return False,positive,zero
            zero+=1;continue
        positive+=1
        for i in range(k+1,n):
            for j in range(i,n):
                M[i][j]-=M[i][k]*M[k][j]/p
                M[j][i]=M[i][j]
    return True,positive,zero

def quad(M,z):return sum(z[i]*M[i][j]*z[j] for i in range(len(z)) for j in range(len(z)))
def sign(p):return (-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
def accept(m,d,words,weights):
    z=[F(w) for w in weights];a=b=F(0)
    for i,pi in enumerate(words):
        for j,sig in enumerate(words):
            e=cross_exp(pi,sig,'id');f=cross_exp(pi,sig,'dep')
            if e is not None:a+=z[i]*z[j]*F(d)**e
            if f is not None:b+=z[i]*z[j]*F(d)**f
    prob=a+b;Fe=(a+b/F(d*d))/prob
    return {'a':str(a),'b':str(b),'p':str(prob),'F':str(Fe),'EB':Fe<=F(1,d)}

def main():
    out={}
    for m in (2,3,4):
        d=4;ps,A,B=matrices(m,d);n=len(ps)
        # Entire control-target Choi output separable, not just a single flag.
        ppt=[[B[i][j]-d*A[i][j] for j in range(n)] for i in range(n)]
        cp=[[A[i][j]+B[i][j]/(d*d) for j in range(n)] for i in range(n)]
        st=psd(ppt);sc=psd(cp);assert st[0] and sc[0]
        out[f'd4_m{m}_EB']={'B_minus_dA_LDL':st,'A_plus_B_over_d2_LDL':sc}
        if m==4:
            upper=F(5,21)
            C=[[upper*(A[i][j]+B[i][j])-A[i][j]-B[i][j]/16 for j in range(n)] for i in range(n)]
            st=psd(C);assert st[0]
            out['d4_m4_F_upper']={'value':str(upper),'LDL':st}
    ps=list(itertools.permutations(range(5)))
    r=accept(5,4,ps,[F(sign(p),120) for p in ps]);assert r['p']=='3/512' and r['F']=='5/16'
    out['d4_five_all_alternating']=r
    cyc=[tuple(range(j,5))+tuple(range(j)) for j in range(5)]
    perm=(4,0,3,1,2)
    cos=[tuple(perm[x] for x in s) for s in cyc]
    r=accept(5,4,cyc+cos,[F(1,10)]*5+[F(-1,10)]*5)
    assert r['p']=='141/1280' and r['F']=='25/94'
    out['d4_five_ten_orders']={'words':cyc+cos,'weights':['1/10']*5+['-1/10']*5,**r}
    for m,d in [(4,2),(6,4)]:
        cyc=[tuple(range(j,m))+tuple(range(j)) for j in range(m)]
        out[f'cyclic_d{d}_m{m}']=accept(m,d,cyc,[F(1,m)]*m)
    Path(__file__).with_name('exact_certificate_results.json').write_text(json.dumps(out,indent=2))
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
