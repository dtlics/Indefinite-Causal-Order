"""Standard-library exact replay of the NR19 mean-two query certificate.

Analytic model inclusion, covariance, and physical trace bounds remain
in the accompanying proof. No conic solver, array package, pickle, or
floating-point arithmetic is used in this replay.
"""
from fractions import Fraction as F
from itertools import product
from math import isqrt
from pathlib import Path
import json
import sys

if not __debug__:
    raise RuntimeError('Run the exact query-certificate replay without -O.')


def require(condition,message):
    if not condition:raise AssertionError(message)


def digits(index,d,k):
    out=[0]*k
    for j in range(k-1,-1,-1):out[j],index=index%d,index//d
    return tuple(out)


def number(ds,d):
    out=0
    for a in ds:out=d*out+a
    return out


def rank_mod(a,p=1000003):
    if not a:return 0
    a=[[int(v)%p for v in row] for row in a];r=0;n=len(a[0])
    for c in range(n):
        pivot=next((j for j in range(r,len(a)) if a[j][c]),None)
        if pivot is None:continue
        a[r],a[pivot]=a[pivot],a[r]
        scale=pow(a[r][c],-1,p)
        a[r]=[(v*scale)%p for v in a[r]]
        for j in range(r+1,len(a)):
            scale=a[j][c]
            if scale:a[j]=[(x-scale*y)%p for x,y in zip(a[j],a[r])]
        r+=1
        if r==len(a):break
    return r


def positive_definite(a):
    n=len(a);l=[[F(0)]*n for _ in range(n)];dd=[]
    for i in range(n):
        require(all(a[i][j]==a[j][i] for j in range(n)),'Dual matrix not symmetric')
        pivot=F(a[i][i])-sum(l[i][k]**2*dd[k] for k in range(i))
        if pivot<=0:return False
        dd.append(pivot);l[i][i]=F(1)
        for j in range(i+1,n):
            l[j][i]=(F(a[j][i])-sum(l[j][k]*l[i][k]*dd[k] for k in range(i)))/pivot
    return True


def sqrt_upper(q,den=10**12):
    require(q>=0,'Negative residual norm square')
    v=(q.numerator*den*den+q.denominator-1)//q.denominator
    a=isqrt(v)
    if a*a<v:a+=1
    bound=F(a,den);require(bound*bound>=q,'Square-root rounding failed')
    return bound


def expected_reps(name):
    if name[0]=='R':
        j0,j1=map(int,name[1:]);middle=[(1-j1,-1),(j1,1),(1-j0,-1),(j0,1)]
        return [[(co,1)]+middle+[(ci,-1)] for co,ci in product(range(2),repeat=2)]
    if name[0]=='S':
        j0,j1,ci=map(int,name[1:]);return [[(j1,1),(1-j0,-1),(j0,1),(ci,-1)]]
    if name[0]=='C':
        j0,j1,ci=map(int,name[1:]);return [[(1-j1,-1),(j1,1),(1-j0,-1),(j0,1),(ci,-1)]]
    if name[0]=='T':
        j0,ci=map(int,name[1:]);return [[(j0,1),(ci,-1)]]
    if name.startswith('Abort'):
        j0,ci=map(int,name[5:]);return [[(1-j0,-1),(j0,1),(ci,-1)]]
    if name[0]=='Z':return [[(int(name[1]),-1)]]
    raise AssertionError('Unknown family '+name)


def parts(desc,k):
    bi,bj=desc['blocks'];edges=tuple(tuple(e) for e in desc['edges'])
    out=[(bi,bj,edges)]
    if desc['transpose']:
        out.append((bj,bi,tuple(((a+k)%(2*k),(b+k)%(2*k)) for a,b in edges)))
    return out


def check_diagram(desc,reps,k):
    bi,bj=desc['blocks'];edges=[tuple(e) for e in desc['edges']]
    require(0<=bi<len(reps) and 0<=bj<len(reps),'Diagram block outside representation')
    require(sorted(v for e in edges for v in e)==list(range(2*k)),'Invalid pairing')
    def representation(node):
        if node<k:return reps[bi][node]
        g,s=reps[bj][node-k];return g,-s
    for a,b in edges:
        ga,sa=representation(a);gb,sb=representation(b)
        require(ga==gb and sa==-sb,'Pairing is not invariant')
    if not desc['transpose']:
        original=sorted(tuple(sorted(e)) for e in edges)
        trans=sorted(tuple(sorted(((a+k)%(2*k),(b+k)%(2*k)))) for a,b in edges)
        require(bi==bj and original==trans,'Unsymmetrized basis matrix')


def component_count(edges,k):
    parent=list(range(2*k))
    def find(a):
        while parent[a]!=a:parent[a]=parent[parent[a]];a=parent[a]
        return a
    for a,b in edges:parent[find(a)]=find(b)
    return len({find(a) for a in range(2*k)})


def gram_entry(a,b,k,d):
    return sum(d**component_count(pa+pb,k)
               for ai,aj,pa in parts(a,k) for bi,bj,pb in parts(b,k)
               if ai==bi and aj==bj)


def entries(desc,k,d):
    n=d**k
    for bi,bj,edges in parts(desc,k):
        for values in product(range(d),repeat=k):
            a=[0]*(2*k)
            for (i,j),v in zip(edges,values):a[i]=a[j]=v
            yield bi*n+number(a[:k],d),bj*n+number(a[k:],d)


def entry(desc,k,d,r,c):
    n=d**k;bi,r=divmod(r,n);bj,c=divmod(c,n)
    a=digits(r,d,k)+digits(c,d,k)
    return sum(int(bi==pi and bj==pj and all(a[i]==a[j] for i,j in edges))
               for pi,pj,edges in parts(desc,k))


def dimension(weight):
    d=len(weight);out=F(1)
    for i in range(d):
        for j in range(i+1,d):out*=F(weight[i]-weight[j]+j-i,j-i)
    require(out.denominator==1,'Nonintegral Weyl dimension')
    return out.numerator


def check_highest(family,d):
    reps,k=family['reps'],family['k'];n=d**k;N=len(reps)*n
    lookup={};total=0;seen=set();symmetric_dimension=0
    for block,h in enumerate(family['highest']):
        w=tuple(h['weight']);require(len(w)==2*d,'Wrong highest-weight length')
        require(all(type(a) is int for a in w),'Noninteger highest weight')
        require(w not in seen,'Duplicate highest weight');seen.add(w)
        require(all(w[g*d+i]>=w[g*d+i+1] for g in range(2) for i in range(d-1)),'Nondominant weight')
        require(all(len({i for i,v in column})==len(column) for column in h['vectors']),
                'Repeated coordinate in a highest vector')
        vectors=[{int(i):int(v) for i,v in column} for column in h['vectors']]
        m=len(vectors);require(m>0,'Empty multiplicity block')
        vg=[[sum(v.get(i,0)*u.get(i,0) for i in v) for u in vectors] for v in vectors]
        require(rank_mod(vg)==m,'Dependent highest-weight vectors')
        for column,v in enumerate(vectors):
            require(all(0<=i<N and a for i,a in v.items()),'Invalid highest-vector coefficient')
            for index,a in v.items():
                b,j=divmod(index,n);ds=digits(j,d,k);actual=[0]*(2*d)
                for value,(g,s) in zip(ds,reps[b]):actual[g*d+value]+=s
                require(tuple(actual)==w,'Highest vector has wrong weight')
                old=lookup.setdefault(index,(block,[]));require(old[0]==block,'Conflicting highest sectors')
                old[1].append((column,a))
            for g in range(2):
                for i in range(d-1):
                    result={}
                    for index,value in v.items():
                        b,j=divmod(index,n);ds=digits(j,d,k)
                        for port,(pg,s) in enumerate(reps[b]):
                            if pg!=g:continue
                            before,after=(i+1,i) if s==1 else (i,i+1)
                            if ds[port]!=before:continue
                            target=list(ds);target[port]=after;idx=b*n+number(target,d)
                            result[idx]=result.get(idx,0)+s*value
                    require(not any(result.values()),'Highest vector is not annihilated by a raising generator')
        total+=m*dimension(w[:d])*dimension(w[d:]);symmetric_dimension+=m*(m+1)//2
    require(total==N,'Highest-weight decomposition is incomplete')
    require(symmetric_dimension==len(family['basis']),'Invariant symmetric basis not complete')
    return lookup


def family_coefficients(family,d,rank,mu,lam):
    h=[-1]*rank+[1]*(d-rank);name=family['name'];k=family['k'];n=d**k
    lookup=check_highest(family,d);out=[];dual=[]
    for hh in family['highest']:
        z=hh['dual_psd_integer'];require(len(z)==len(hh['vectors']),'Dual block dimension mismatch')
        require(all(len(row)==len(z) for row in z),'Nonsquare dual block')
        require(positive_definite(z),'Rounded rational dual is not positive definite');dual.append(z)
    def zvalue(index):
        block,index=divmod(index,n);co,ci=divmod(block,2);a,q,qi,p,pi,b=digits(index,d,6)
        return h[a]*h[q] if co==ci and a==b and q==qi and p==pi else 0
    def probability_value(index):
        ds=digits(index,d,k)
        if name.startswith('Abort'):return (ds[2],1) if ds[0]==ds[1] else None
        if name[0]=='C':return (ds[4],h[ds[0]]) if ds[0]==ds[1] and ds[2]==ds[3] else None
        return None
    for desc in family['basis']:
        projected=[[[0]*len(hh['vectors']) for _ in hh['vectors']] for hh in family['highest']]
        numerator=0
        for r,c in entries(desc,k,d):
            a=lookup.get(r);b=lookup.get(c)
            if a is not None and b is not None and a[0]==b[0]:
                mat=projected[a[0]]
                for i,x in a[1]:
                    for j,y in b[1]:mat[i][j]+=x*y
            if name[0]=='R':numerator+=zvalue(r)*zvalue(c)
            elif name.startswith('Abort') or name[0]=='C':
                a=probability_value(r);b=probability_value(c)
                if a is not None and b is not None and a[0]==b[0]:numerator+=a[1]*b[1]
            elif name[0]=='Z':numerator+=int(r==c)
        contraction=sum(projected[g][i][j]*dual[g][i][j]
                        for g in range(len(dual)) for i in range(len(dual[g])) for j in range(len(dual[g])))
        if name[0]=='R':objective=F(numerator,4*d*d)
        elif name.startswith('Abort'):objective=max(lam+mu,1-mu)*F(numerator,2*d)
        elif name[0]=='C':objective=(1-mu)*F(numerator,2*d)
        elif name[0]=='Z':objective=(lam+2*mu)*F(numerator,2*d)
        else:objective=F(0)
        out.append((objective,contraction))
    return out


def equation_coefficients(address,families,d):
    kind=address[0];out={}
    require(all(type(v) is int for v in address[1:]),'Noninteger causal address')
    def add_family(name,fn,sign=1):
        family=families[name]
        for i,basis in enumerate(family['basis']):
            value=sign*fn(basis,family['k'])
            if value:out[family['offset']+i]=out.get(family['offset']+i,0)+value
    if kind=='terminal':
        require(len(address)==6,'Wrong terminal-address length')
        _,j0,j1,ci,r,c=address
        require(j0 in [0,1] and j1 in [0,1] and ci in [0,1]
                and 0<=r<d**5 and 0<=c<d**5,'Terminal causal address out of range')
        rs=digits(r,d,5);cs=digits(c,d,5)
        def f(b,k):
            n=d**k
            return sum(entry(b,k,d,(co*2+ci)*n+number((a,)+rs,d),
                             (co*2+ci)*n+number((a,)+cs,d)) for co in range(2) for a in range(d))
        add_family(f'R{j0}{j1}',f)
        add_family(f'C{j0}{j1}{ci}',lambda b,k:entry(b,k,d,r,c))
        if rs[0]==cs[0]:add_family(f'S{j0}{j1}{ci}',lambda b,k:entry(b,k,d,number(rs[1:],d),number(cs[1:],d)),-1)
        rhs=0
    elif kind=='middle':
        require(len(address)==5,'Wrong middle-address length')
        _,j0,ci,r,c=address
        require(j0 in [0,1] and ci in [0,1] and 0<=r<d**3 and 0<=c<d**3,
                'Middle causal address out of range')
        rs=digits(r,d,3);cs=digits(c,d,3)
        add_family(f'Abort{j0}{ci}',lambda b,k:entry(b,k,d,r,c))
        for j1 in range(2):
            add_family(f'S{j0}{j1}{ci}',lambda b,k:sum(entry(b,k,d,number((a,)+rs,d),number((a,)+cs,d)) for a in range(d)))
        if rs[0]==cs[0]:add_family(f'T{j0}{ci}',lambda b,k:entry(b,k,d,number(rs[1:],d),number(cs[1:],d)),-1)
        rhs=0
    elif kind=='initial':
        require(len(address)==4,'Wrong initial-address length')
        _,ci,r,c=address
        require(ci in [0,1] and 0<=r<d and 0<=c<d,'Initial causal address out of range')
        for j0 in range(2):add_family(f'T{j0}{ci}',lambda b,k:sum(entry(b,k,d,a*d+r,a*d+c) for a in range(d)))
        add_family(f'Z{ci}',lambda b,k:entry(b,k,d,r,c));rhs=int(r==c)
    else:raise AssertionError('Unknown causal equation')
    return {i:v for i,v in out.items() if v},rhs


def verify(data):
    require(data['schema']=='NR19-mean-query-certificate-v1','Unknown certificate schema')
    d,rank=data['data_dimension'],data['reflection_rank'];mu=F(data['mu']);den=int(data['dual_grid_denominator'])
    require((d,rank)==(3,1),'This certificate is the qutrit rank-one instance')
    require(mu>=0 and den>0,'Invalid Lagrange/grid parameter')
    s=d-2*rank;lam=max(F(s*s,d*d),F(d*d-s*s,d*d*(d*d-1)))
    expected={f'{letter}{j0}{j1}' for letter in ['R'] for j0,j1 in product(range(2),repeat=2)}
    expected.update(f'{letter}{j0}{j1}{ci}' for letter in ['S','C'] for j0,j1,ci in product(range(2),repeat=3))
    expected.update(f'{letter}{j0}{ci}' for letter in ['T','Abort'] for j0,ci in product(range(2),repeat=2))
    expected.update(['Z0','Z1'])
    families={};offset=0;residual=[];gram=[];counts={'basis_matrices':0,'highest_blocks':0}
    for f in data['families']:
        name=f['name'];require(name not in families,'Duplicate family')
        reps=expected_reps(name);require(f['reps']==[[list(a) for a in b] for b in reps],'Wrong port representations')
        f['reps']=reps;f['k']=len(reps[0]);f['offset']=offset
        for desc in f['basis']:check_diagram(desc,reps,f['k'])
        g=[[gram_entry(a,b,f['k'],d) for b in f['basis']] for a in f['basis']]
        require(rank_mod(g)==len(g),'Invariant basis is linearly dependent')
        coeff=family_coefficients(f,d,rank,mu,lam)
        residual.extend(-c-F(z,den) for c,z in coeff)
        gram.append(g);offset+=len(f['basis']);families[name]=f
        counts['basis_matrices']+=len(g);counts['highest_blocks']+=len(f['highest'])
    require(set(families)==expected,'Missing or unexpected causal family')
    dual_objective=F(0)
    for eq in data['equalities']:
        coefficients,rhs=equation_coefficients(eq['address'],families,d)
        y=F(int(eq['dual_integer']),den);dual_objective+=rhs*y
        for i,value in coefficients.items():residual[i]+=value*y
    error=F(0);off=0
    for f,g in zip(data['families'],gram):
        n=len(g);rr=residual[off:off+n];representer=list(map(F,f['residual_representer']))
        require(len(representer)==n,'Wrong residual representer size')
        require(all(sum(F(a)*b for a,b in zip(row,representer))==r for row,r in zip(g,rr)),
                'Exact Gram residual equation failed')
        square=sum(a*b for a,b in zip(rr,representer));norm=sqrt_upper(square)
        name=f['name'];trace_bound=(2*d**3 if name[0]=='R' else d**3 if name[0]=='C'
                                   else d if name[0] in ['T','Z'] else d*d)
        error+=trace_bound*norm;off+=n
    upper=dual_objective+error;claimed=F(data['claimed_upper_bound'])
    require(upper<=claimed,'Claimed bound is smaller than exact certified bound')
    return {'status':'passed','result':'NR-R19','data_dimension':d,
            'ordinary_expected_query_budget':'2','mu':str(mu),'lambda_missing':str(lam),
            'rounded_dual_objective':str(dual_objective),'exact_residual_trace_error':str(error),
            'exact_certified_upper':str(upper),'reported_upper':str(claimed),
            **counts,'causal_rows_reconstructed':len(data['equalities']),
            'arithmetic':'Python standard-library integer and Fraction only',
            'scope':'Exact invariant-basis completeness, highest-weight kernels, causal dual and residual replay. Analytic prior/covariance/stopping inclusion and physical trace bounds are proof inputs; no native hardware advantage.'}


if __name__=='__main__':
    source=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('mean_query_certificate.json')
    print(json.dumps(verify(json.loads(source.read_text(encoding='utf-8'))),indent=2))
