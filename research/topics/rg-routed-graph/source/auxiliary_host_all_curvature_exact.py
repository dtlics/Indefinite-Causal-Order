"""Exact rational duals in every discovered mixed-word sector.

Boundary directions are in the radical by the explicit mixed tensors CH and HC;
the output records exact bilinear coefficients on a full 72-coordinate complement.
"""
from pathlib import Path
from itertools import product
from fractions import Fraction as Q
import math,json,time
import numpy as np
import sympy as s
from phase_endpoint_exact import row_tensor,WORDS
ROOT=Path(__file__).parent;T=row_tensor(4,1);P=1000003
meta=json.loads((ROOT/'auxiliary_host_compatibility_form_checks.json').read_text());src=np.load(ROOT/'auxiliary_host_compatibility_tangent_basis.npz')
vectors=[];labels=[];masks=[];kinds=[]
for key,labs in meta['basis_labels'].items():
    m=int(key.split('_')[0]);kind=key.split('_')[1]
    for idx,lab in enumerate(labs):
        if lab[0] in ['past','future']:continue
        vectors.append(src[key][idx].reshape(16,16,16));labels.append({'mask':m,'kind':kind,'typed_basis_index':idx,'label':lab});masks.append(m);kinds.append(int(kind=='imag'))
V=np.array(vectors,dtype=np.int64);masks=np.array(masks,dtype=np.int64);kinds=np.array(kinds,dtype=np.int64)
label_lookup={(d['mask'],d['kind'],d['typed_basis_index']):i for i,d in enumerate(labels)}
def sub(row,other,z):
    for i,x in other.items():
        zz=row.get(i,0)-z*x
        if zz:row[i]=zz
        elif i in row:del row[i]
all_forms=[];start=time.time();gram=np.zeros((72,72),dtype=np.int64);sectors=[]
for kappa,mode in product(range(16),['real','imag']):
    scout=json.loads((ROOT/f'auxiliary_host_all_curvature_{kappa}_{mode}_checks.json').read_text())
    if not scout['independent_residual_forms']:continue
    parity=1 if mode=='real' else -1
    ii=[];jj=[];ss=[]
    for pair in scout['pairs']:
        ids=[label_lookup[d['mask'],d['kind'],d['typed_basis_index']] for d in [pair['left'],pair['right']]]
        ii.append(ids[0]);jj.append(ids[1]);ss.append(-1 if kinds[ids[0]]==1 and kinds[ids[1]]==0 else 1)
    ii=np.array(ii);jj=np.array(jj);s1=np.array(ss);s2=parity*s1
    opts=[]
    for bit in [8,4,2,1]:
        if kappa&bit:opts.append([[(r,a,1-r,b,1)] for r,a,b in product(range(2),repeat=3)])
        else:opts.append([[(1,a,1,a,1) for a in range(2)]]+[[(0,a,0,b,1),(1,a,1,b,-1)] for a,b in product(range(2),repeat=2)])
    cache={}
    def rawterms(key):
        key=tuple(key)
        if key not in cache:
            terms=[]
            for term in product(*[opts[i][key[i]] for i in range(4)]):
                r=sum(term[i][0]<<(3-i) for i in range(4));a=sum(term[i][1]<<(3-i) for i in range(4));t=sum(term[i][2]<<(3-i) for i in range(4));b=sum(term[i][3]<<(3-i) for i in range(4));sg=math.prod(x[4] for x in term);terms.append((r,a,t,b,sg))
            cache[key]=terms
        return cache[key]
    def arow(rec):
        key,pp,qq=rec;row={}
        for r,a,t,b,sg in rawterms(key):
            i=(r*16+b)*16+qq;j=(t*16+a)*16+pp
            row[i]=row.get(i,0)+sg*int(T[r,a,pp]);row[j]=row.get(j,0)+sg*parity*int(T[t,b,qq])
        return {i:Q(x) for i,x in row.items() if x}
    old=json.loads((ROOT/f'auxiliary_tangent_output_block_{kappa}_{"imag" if mode=="real" else "real"}.json').read_text())['rows'];piv={}
    for rid,rec in enumerate(old):
        row=arow(rec);comb={rid:Q(1)}
        while row:
            k=min(row);z=row[k]
            if k not in piv:
                piv[k]=({i:x/z for i,x in row.items()},{i:x/z for i,x in comb.items()});break
            pp,cc=piv[k];sub(row,pp,z);sub(comb,cc,z)
        else:raise AssertionError('rank row dependent')
    sector_forms=[]
    for number,rec in enumerate(scout['forms']):
        last=[rec['word_key'],*rec['boundary_entry']];row=arow(last);comb={len(old):Q(1)}
        while row:
            k=min(row);z=row[k];assert k in piv
            pp,cc=piv[k];sub(row,pp,z);sub(comb,cc,z)
        den=math.lcm(*[x.denominator for x in comb.values()]);weights={i:int(x*den) for i,x in comb.items()};gg=math.gcd(*weights.values());weights={i:x//gg for i,x in weights.items()}
        if weights[len(old)]<0:weights={i:-x for i,x in weights.items()}
        locations=old+[last];check={};rows=[];terms={}
        for rid,w in sorted(weights.items()):
            key,pp,qq=locations[rid]
            for i,x in arow(locations[rid]).items():check[i]=check.get(i,0)+w*x
            rows.append({'word_key':key,'boundary_entry':[pp,qq],'weight':w})
            for r,a,t,b,sg in rawterms(key):
                ident=(r,a,t,b,pp,qq);terms[ident]=terms.get(ident,0)+w*sg
        assert all(x==0 for x in check.values())
        terms={key:w for key,w in terms.items() if w}
        bound=2*sum(abs(w) for w in terms.values())*int(np.max(np.abs(V)))**2;assert bound<2**63
        vv=np.zeros(len(ii),dtype=np.int64)
        for (r,a,t,b,pp,qq),w in terms.items():
            f=r^masks[ii];g=r^masks[jj]
            assert np.all(f^masks[jj]==t) and np.all(g^masks[ii]==t)
            vv+=w*(s1*V[ii,f,a,pp]*V[jj,f,b,qq]+s2*V[jj,g,a,pp]*V[ii,g,b,qq])
        assert np.array_equal(vv%P,np.array(rec['residual_coefficients'],dtype=np.int64)*weights[len(old)]%P)
        gcd=math.gcd(*[int(v) for v in vv if v]);assert gcd
        norm=vv//gcd;B=np.zeros((72,72),dtype=np.int64);B[ii,jj]=norm;B[jj,ii]=norm
        gram+=B.T@B
        nz=np.flatnonzero(norm);entries=[{'coordinates':[int(ii[k]),int(jj[k])],'value':int(norm[k])} for k in nz]
        fm={'sector':[kappa,mode],'number':number,'dual_rows':rows,'dual_row_count':len(rows),'maximum_dual_weight':max(map(abs,weights.values())),'bilinear_normalization_divisor':gcd,'bilinear_entries':entries,'annihilator_exact':True,'integer_bound':bound}
        all_forms.append(fm);sector_forms.append(norm.tolist())
    M=s.Matrix(sector_forms);rank=s.polys.matrices.DomainMatrix.from_Matrix(M).convert_to(s.QQ).rank();assert rank==len(sector_forms)
    sectors.append({'mask':kappa,'mode':mode,'exact_independent_forms':rank})
    print('EXACT',kappa,mode,'forms',rank,'seconds',time.time()-start,flush=True)
GG=s.Matrix(gram.tolist());radical=GG.nullspace();r=72-len(radical)
report={'status':'EXACT_ALL_DISCOVERED_FORMS','quotient_dimension':72,'coordinate_labels':labels,'number_of_independent_forms':len(all_forms),'sectors':sectors,'common_radical_codimension':r,'full_tangent_common_radical_dimension':583-r,'quotient_common_radical_basis':[[str(x) for x in col] for col in radical],'forms':all_forms,'scope':'All listed forms are exact necessary host-wide bilinear constraints. Completeness of the discovery enumeration is not needed or claimed as a theorem; no sufficiency for a host.'}
(ROOT/'auxiliary_host_all_curvature_exact_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS',len(all_forms),'forms','common active dimension',r,'seconds',time.time()-start,flush=True)
