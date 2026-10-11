"""Independent exact audits of supported-cut witnesses and phase-mask rigidity.

All new outputs retain this file's prefix. The logical audits are in the companion
Markdown file. Positive finite cut dimensions are explicitly only upper bounds.
"""
from pathlib import Path
from itertools import product, permutations
import json
import sympy as s
from exact_fixtures import E,I16,I2,X,Y,Z,WORDS,tensor,local,R
ROOT=Path(__file__).parent
P=[I2,X,Y,Z]; zero=s.zeros(16)
Vs=[I16-2*sum((o[i]*E[i] for i in range(4)),zero) for o in WORDS]
D0=s.Matrix.vstack(*[Vs[k][k,:] for k in range(16)])
assert D0*D0==I16

def modrank(rows,p):
    pivots={}
    for original in rows:
        row=[int(x)%p for x in original]
        for col in range(len(row)):
            if not row[col]: continue
            if col not in pivots:
                inv=pow(row[col],-1,p)
                pivots[col]=[(x*inv)%p for x in row]
                break
            v=row[col]; pivot=pivots[col]
            row=[(x-v*y)%p for x,y in zip(row,pivot)]
    return len(pivots)

def pauli_permutation(aa):
    """Return column and i-phase exponent of each nonzero row entry."""
    ans=[]
    for w in WORDS:
        col=[];phase=0
        for a,b in zip(aa,w):
            col.append(1-b if a in [1,2] else b)
            if a==2:phase+=1 if b else 3
            if a==3 and b:phase+=2
        idx=sum(x<<(3-i) for i,x in enumerate(col))
        ans.append((idx,phase%4))
    return ans

# Rebuild exact coefficient rows without the author's matrix-product cache:
# all transformed columns multiplied by 8 are integral, and Paulis are monomial.
data=json.loads((ROOT/'phase_mask_tangent_space_checks.json').read_text())
chars={'0':s.Matrix([1,0]),'1':s.Matrix([0,1]),'+':s.Matrix([1,1]),'-':s.Matrix([1,-1])}
W=s.Matrix.hstack(*[tensor([chars[c] for c in w]) for w in data['labels']])
B8=[]
for V in Vs:
    b=8*V*W
    assert all(x.is_Integer for x in b)
    B8.append([[int(b[r,p]) for r in range(16)] for p in range(16)])
rows=[]
for rec in data['retained_rows']:
    aa=rec['pauli_word']; perm=pauli_permutation(aa)
    coeff=[]
    for o,w in enumerate(WORDS):
        re=im=0
        for r,(c,phase) in enumerate(perm):
            z=B8[o][rec['p']][r]*B8[o][rec['q']][c]
            if phase==0:re+=z
            elif phase==1:im+=z
            elif phase==2:re-=z
            else:im-=z
        z=re if rec['part']=='real' else im
        coeff.append(z*(-1)**sum(w[i] for i,a in enumerate(aa) if a))
    assert coeff==rec['coeff']
    row=[0]*256
    for o,z in enumerate(coeff):
        row[16*o+rec['p']]=z
        row[16*o+rec['q']]=-z
    rows.append(row)
prime=data['prime']; assert s.isprime(prime)
assert len(rows)==221 and modrank(rows,prime)==221

groups=[(1,[2,10]),(1,[3,13]),(2,[4,5]),(3,[6,7])]
gens=[]
for p in range(16):gens.append([int(q==p) for o in range(16) for q in range(16)])
for o in range(1,16):gens.append([int(k==o) for k in range(16) for p in range(16)])
for i,cols in groups:gens.append([int(p in cols)*o[i] for o in WORDS for p in range(16)])
assert len(gens)==35 and modrank(gens,prime)==35
assert all(sum(x*y for x,y in zip(r,g))==0 for r in rows for g in gens)

carriers=[]
for i,cols in groups:
    C=sum((W[:,p]*W[:,p].H/(W[:,p].H*W[:,p])[0] for p in cols),zero)
    assert C.rank()==2 and C*C==C and C.H==C
    assert all(C*local(i,p)==local(i,p)*C for p in P)
    assert all(E[j]*C==zero for j in range(4) if j!=i)
    carriers.append(C)
assert all(a*b==zero for k,a in enumerate(carriers) for b in carriers[k+1:])

# Fill the placeholder in the author's verifier with a full symbolic coefficient
# identity, with no unitary equations assumed for the sixteen query entries.
us=[s.Matrix(2,2,s.symbols(f'v{i}_0:4')) for i in range(4)]
WW=tensor(us)
raw=s.Matrix.vstack(*[(WW[k,:]*Vs[k]) for k in range(16)])
for (i,cols),C in zip(groups,carriers):
    bar=tensor([I2 if j==i else us[j] for j in range(4)])
    expected=bar*R[i]*local(i,us[i])*C
    assert all(s.expand(z)==0 for z in raw*C-expected)
    O=local(i,s.diag(0,1))
    assert O*R[i]*C*R[i]==R[i]*C*R[i]*O
phase_report={'status':'PASS','independently_recomputed_integer_rows':221,
              'prime_verified':prime,'constraint_rank_mod_prime':221,
              'displayed_generator_rank_mod_prime':35,
              'all_retained_rows_annihilate_all_generators_exactly':True,
              'all_four_serial_carrier_identities_checked_with_generic_complex_query_entries':True,
              'continuous_complete_phase_space_dimension':35,
              'sufficiency_source':'Orthogonal carrier/image argument audited, including private ancillas'}
(ROOT/'continuous_product_supported_cut_audit_phase_checks.json').write_text(json.dumps(phase_report,indent=2)+'\n')
print('Phase audit PASS: 221 independent exact rows, 35 independent generators, four symbolic serial identities.',flush=True)

# Independent row-tensor construction of every Pauli tuple, avoiding the author's
# original F formula and constructing singles by specialization rather than R_i.
row_products=[V*D0 for V in Vs]
cache={}
for aa in product(range(4),repeat=4):
    perm=pauli_permutation(aa)
    cache[aa]=s.Matrix.vstack(*[(s.I**power)*row_products[o][c,:]
                              for o,(c,power) in enumerate(perm)])
assert cache[(0,0,0,0)]==I16
pairgrams={}
for i,j in permutations(range(4),2):
    gram=zero
    for a,b in product(range(1,4),repeat=2):
        aa=[0]*4;aa[i]=a;aa[j]=b
        ia=[0]*4;ia[i]=a
        ja=[0]*4;ja[j]=b
        # This is F_j times the author's C, so has the same Gram and kernel.
        M=cache[tuple(aa)]*cache[tuple(ia)].H-cache[tuple(ja)]
        gram=gram+M.H*M
    pairgrams[i,j]=gram
print('Supported-cut independent row-tensor pair Grams complete.',flush=True)
cut_report=[]
reference=json.loads((ROOT/'auxiliary_supported_cut_spaces_checks.json').read_text())
for bits in product(range(2),repeat=4):
    before=[i for i in range(4) if bits[i]]; after=[i for i in range(4) if not bits[i]]
    if not before or not after:continue
    gram=sum((pairgrams[i,j] for i in before for j in after),zero)
    ns=gram.nullspace();K=s.Matrix.hstack(*ns) if ns else s.zeros(16,0)
    pairdim=K.cols;tested=0
    for aa in product(range(4),repeat=4):
        if not K.cols:break
        if sum(a!=0 for a in aa)<3:continue
        left=tuple(a if i in before else 0 for i,a in enumerate(aa))
        right=tuple(a if i in after else 0 for i,a in enumerate(aa))
        defect_on_K=cache[aa]*(cache[left].H*K)-cache[right]*K
        nn=defect_on_K.nullspace()
        K=K*s.Matrix.hstack(*nn) if nn else s.zeros(16,0)
        tested+=1
    ref=next(r for r in reference if r['before_queries']==[i+1 for i in before])
    assert pairdim==ref['pair_cut_dimension'] and K.cols==ref['pauli_cut_dimension']
    if K.cols:
        old=s.Matrix.hstack(*[s.Matrix([s.sympify(x) for x in col]) for col in ref['basis']])
        assert old.row_join(K).rank()==K.cols
    out={'before_queries':[i+1 for i in before],'after_queries':[i+1 for i in after],
         'pair_context_upper_bound_dimension':pairdim,'all_Pauli_upper_bound_dimension':K.cols,
         'higher_contexts_tested':tested,
         'status':'EXCLUDED' if not K.cols else 'NONZERO UPPER BOUND ONLY'}
    cut_report.append(out)
    print(out,flush=True)
report={'status':'PASS','all_fourteen_cuts_match_reference_subspaces':True,
        'zero_upper_bound_cuts':sum(r['all_Pauli_upper_bound_dimension']==0 for r in cut_report),
        'nonzero_upper_bound_cuts':sum(r['all_Pauli_upper_bound_dimension']>0 for r in cut_report),
        'cuts':cut_report,
        'warning':'A surviving finite-context subspace is not an all-parameter cut space or a host construction.'}
(ROOT/'continuous_product_supported_cut_audit_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print('Supported-cut finite certificate audit PASS.',flush=True)
