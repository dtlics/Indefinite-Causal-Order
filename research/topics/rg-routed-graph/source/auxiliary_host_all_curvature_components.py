"""Refine rank-two component cover with the remaining exact curvature forms.

Real linear factorization gives exact binary branches. Complex factorizations
of a pair of real equations, when found, give exact real codimension-two branches.
"""
from pathlib import Path
import json,collections,time
import sympy as s
ROOT=Path(__file__).parent
source=json.loads((ROOT/'auxiliary_host_all_curvature_exact_checks.json').read_text());quot=json.loads((ROOT/'auxiliary_host_all_curvature_quotient_checks.json').read_text());piv=quot['pivot_coordinates'];idx={old:i for i,old in enumerate(piv)};n=37
Bs=[]
for rec in source['forms']:
    A=s.zeros(n)
    for entry in rec['bilinear_entries']:
        a,b=entry['coordinates']
        if a in idx and b in idx:A[idx[a],idx[b]]=A[idx[b],idx[a]]=entry['value']
    Bs.append(A)
initial=json.loads((ROOT/'auxiliary_host_rank_two_components_checks.json').read_text())['components']
def canon(A):
    rr,pp=A.rref();return tuple(tuple(rr[i,:]) for i in range(len(pp)))
def mat(key):return s.Matrix(key) if key else s.zeros(0,n)
def contained(a,b):
    if len(b)>len(a):return False
    return mat(a).col_join(mat(b)).rank()==len(a)
queue=[canon(s.Matrix([[s.Rational(x) for x in row] for row in rec['rows']])) for rec in initial];seen=set();finished=[];unresolved=[];start=time.time();count=0;branches=[]
while queue:
    key=queue.pop();
    if key in seen or any(contained(key,b) for b in finished):continue
    seen.add(key);M=mat(key);N=s.Matrix.hstack(*M.nullspace());d=N.cols
    forms=[]
    for B in Bs:
        A=N.T*B*N
        if A!=s.zeros(d):forms.append(A)
    if not forms:
        finished=[b for b in finished if not contained(b,key)]+[key];print('COMPONENT',len(key),'free',d,flush=True);continue
    mon=[(i,j) for i in range(d) for j in range(i,d)];CO=s.Matrix([[A[i,j]*(1 if i==j else 2) for i,j in mon] for A in forms]);rr,pp=CO.rref();vs=s.symbols('z0:'+str(d));polys=[sum(rr[k,c]*vs[i]*vs[j] for c,(i,j) in enumerate(mon) if rr[k,c]) for k in range(len(pp))]
    free=[i for i in range(n) if i not in M.rref()[1]];assert N.extract(free,list(range(d)))==s.eye(d)
    found=None;kind=None
    for q in polys:
        factor=s.factor_list(q)[1]
        if all(s.Poly(f,*vs).total_degree()==1 for f,m in factor):
            found=[[f] for f,m in factor];kind='real';break
    if found is None:
        for ia in range(len(polys)):
            for ib in range(ia+1,len(polys)):
                factor=s.factor_list(polys[ia]+s.I*polys[ib],extension=s.I)[1]
                if all(s.Poly(f,*vs).total_degree()==1 for f,m in factor):
                    found=[]
                    for f,m in factor:
                        re=s.expand(f).as_real_imag(deep=True)
                        # Variables are real but generic symbols need explicit replacements.
                        re=[s.expand(s.re(f)).subs({s.re(v):v for v in vs}).subs({s.im(v):0 for v in vs}),s.expand(s.im(f)).subs({s.re(v):v for v in vs}).subs({s.im(v):0 for v in vs})]
                        found.append([x for x in re if x!=0])
                    kind='complex';break
            if found is not None:break
    if found is None:
        unresolved.append({'key':key,'free':d,'polynomials':[str(q) for q in polys]});print('UNRESOLVED',len(key),'free',d,'quadrics',len(polys),flush=True);continue
    for group in found:
        rows=[]
        for f in group:
            coeff=[s.expand(f).coeff(v) for v in vs];assert s.expand(f-sum(x*v for x,v in zip(coeff,vs)))==0
            row=s.zeros(1,n)
            for j,x in zip(free,coeff):row[j]=x
            rows.append(row)
        nxt=canon(M.col_join(s.Matrix.vstack(*rows)))
        if nxt!=key:queue.append(nxt)
    count+=1;print('BRANCH',count,'type',kind,'codim',len(key),'free',d,'remaining',len(queue),'seconds',time.time()-start,flush=True)
out={'status':'COMPLETE_COMPONENT_COVER' if not unresolved else 'PARTIAL_COMPONENT_COVER','active_dimension':n,'finished':[{'codimension':len(key),'full_tangent_dimension':583-len(key),'rows':[[str(x) for x in row] for row in key]} for key in finished],'unresolved':[{'codimension':len(v['key']),'free':v['free'],'rows':[[str(x) for x in row] for row in v['key']],'remaining_polynomials':v['polynomials']} for v in unresolved],'scope':'Exact linear/complex-product branching cover of all common isotropic host spans, contingent on the audited full curvature forms; sufficiency for a host is not asserted.'}
(ROOT/'auxiliary_host_all_curvature_components_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('DONE',out['status'],'finished',len(finished),'unresolved',len(unresolved),'seconds',time.time()-start,flush=True)
