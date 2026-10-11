"""Lift the thirteen discovered mixed-word obstructions to exact rational duals."""
from pathlib import Path
from itertools import product
from fractions import Fraction as Q
import math,json,time
import numpy as np
import sympy as s
from phase_endpoint_exact import row_tensor,WORDS
ROOT=Path(__file__).parent;T=row_tensor(4,1)
meta=json.loads((ROOT/'auxiliary_host_compatibility_form_checks.json').read_text());data=np.load(ROOT/'auxiliary_host_compatibility_tangent_basis.npz')
old=json.loads((ROOT/'auxiliary_tangent_output_block_0_imag.json').read_text())['rows']
scout=json.loads((ROOT/'auxiliary_host_curvature_scout_checks.json').read_text())
opts=[[(1,a,1,a,1) for a in range(2)]]+[[(0,a,0,b,1),(1,a,1,b,-1)] for a,b in product(range(2),repeat=2)]
cache={}
def rawterms(key):
    key=tuple(key)
    if key not in cache:
        out=[]
        for term in product(*[opts[key[i]] for i in range(4)]):
            r=sum(term[i][0]<<(3-i) for i in range(4));a=sum(term[i][1]<<(3-i) for i in range(4));b=sum(term[i][3]<<(3-i) for i in range(4));sg=math.prod(t[4] for t in term);out.append((r,a,b,sg))
        cache[key]=out
    return cache[key]
def arow(rec):
    key,pp,qq=rec;row={}
    for r,a,b,sg in rawterms(key):
        i=(r*16+b)*16+qq;j=(r*16+a)*16+pp
        row[i]=row.get(i,0)+sg*int(T[r,a,pp]);row[j]=row.get(j,0)+sg*int(T[r,b,qq])
    return {i:Q(x) for i,x in row.items() if x}
def sub(row,other,z):
    for i,x in other.items():
        zz=row.get(i,0)-z*x
        if zz:row[i]=zz
        elif i in row:del row[i]
piv={};start=time.time()
for rid,rec in enumerate(old):
    row=arow(rec);comb={rid:Q(1)}
    while row:
        k=min(row);z=row[k]
        if k not in piv:
            piv[k]=({i:x/z for i,x in row.items()},{i:x/z for i,x in comb.items()});break
        pp,cc=piv[k];sub(row,pp,z);sub(comb,cc,z)
    else:raise AssertionError('selected rank row became dependent')
    if rid%500==0:print('Exact dual elimination',rid,'seconds',time.time()-start,flush=True)
assert len(piv)==3967
duals=[]
for ii,rec in enumerate(scout['forms']):
    last=[rec['word_key'],*rec['boundary_entry']];row=arow(last);comb={len(old):Q(1)}
    while row:
        k=min(row);z=row[k];assert k in piv
        pp,cc=piv[k];sub(row,pp,z);sub(comb,cc,z)
    den=math.lcm(*[x.denominator for x in comb.values()]);weights={i:int(x*den) for i,x in comb.items()};gg=math.gcd(*weights.values());weights={i:x//gg for i,x in weights.items()}
    if weights[len(old)]<0:weights={i:-x for i,x in weights.items()}
    locations=old+[last];check={};rows=[];terms=[]
    for rid,w in sorted(weights.items()):
        key,pp,qq=locations[rid]
        for i,x in arow(locations[rid]).items():check[i]=check.get(i,0)+w*x
        rows.append({'word_key':key,'boundary_entry':[pp,qq],'weight':w})
        terms.extend((o,a,b,pp,qq,w*sg) for o,a,b,sg in rawterms(key))
    assert all(x==0 for x in check.values())
    typed=[];fullzero=True
    for typedkey in data.files:
        mask=int(typedkey.split('_')[0]);kind=typedkey.split('_')[1];V=data[typedkey].reshape(-1,16,16,16);n=len(V);B=np.zeros((n,n),dtype=np.int64)
        bound=2*sum(abs(t[-1]) for t in terms)*int(np.max(np.abs(V)))**2;assert bound<2**63
        for o,a,b,pp,qq,sg in terms:
            x=V[:,o^mask,a,pp];y=V[:,o^mask,b,qq];B+=sg*(np.outer(x,y)+np.outer(y,x))
        active=np.flatnonzero(np.any(B,axis=0)).tolist()
        if active:
            fullzero=False;M=s.Matrix(B[np.ix_(active,active)].tolist());rank=M.rank()
            assert typedkey=='0_real' and rank==2
            xs=s.symbols('x0:172');poly=sum((B[i,i]*xs[i]**2+sum(2*B[i,j]*xs[i]*xs[j] for j in active if j>i) for i in active),s.Integer(0));fac=s.factor_list(poly)
            assert len(fac[1])==2 and all(mult==1 and s.Poly(f,*xs).total_degree()==1 for f,mult in fac[1])
            factors=[]
            for f,mult in fac[1]:factors.append({str(i):str(s.expand(f).coeff(xs[i])) for i in active if f.coeff(xs[i])})
            typed.append({'typed_block':typedkey,'rank':rank,'basis_indices':active,'matrix':B[np.ix_(active,active)].tolist(),'diagonal_polynomial_factor':str(fac[0]),'linear_factors':factors,'integer_bound':bound})
        else:typed.append({'typed_block':typedkey,'rank':0,'integer_bound':bound})
    assert not fullzero
    duals.append({'number':ii,'dual_rows':rows,'row_count':len(rows),'maximum_weight':max(map(abs,weights.values())),'annihilates_every_complex_mixed_coefficient':True,'forms':typed})
    print('Exact form',ii,'dual support',len(rows),'maxweight',max(map(abs,weights.values())),'seconds',time.time()-start,flush=True)
out={'status':'EXACT_THIRTEEN_NECESSARY_FORMS','forms':duals,'full_tangent_dimension':583,'scope':'Each of thirteen exact rank-two forms vanishes on the full auxiliary tangent span of every single host. No claim here of completeness of these forms or sufficiency for a host.'}
(ROOT/'auxiliary_host_curvature_exact_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(duals),'exact host-wide rank-two forms',time.time()-start,flush=True)
