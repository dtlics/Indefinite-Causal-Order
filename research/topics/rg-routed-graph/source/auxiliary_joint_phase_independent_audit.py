"""Independent four-row rational audit of the arbitrary joint-extension obstruction.

Rebuild T via its bit-difference formula, and form rows by FORWARD reduction
of raw unitary-block words. This does not use the author's affine elimination,
inverse-word enumeration, pivots, or the homogeneous rank calculation.
"""
from pathlib import Path
from itertools import product
import json
import numpy as np
import sympy as s
from exact_fixtures import E, WORDS
ROOT=Path(__file__).parent
T=np.zeros((16,16,16),dtype=np.int64)
C4=np.zeros_like(T);C5=np.zeros_like(T)
for r,ow in enumerate(WORDS):
    for a,aw in enumerate(WORDS):
        v=4*s.eye(16)[a,:]-sum((8*E[i][a,:] for i in range(4) if ow[i]!=aw[i]),s.zeros(1,16))
        assert all(x.is_Integer for x in v)
        T[r,a]=[int(x) for x in v]
        if ow[1]==0 and ((aw[0]==0 and aw[3]==0) or (aw[0]==1 and aw[2]==0)):
            C4[r,a]=T[r,a]
        if ow[3]==0 and (aw[2]==0 or (aw[0]==0 and aw[1]==1 and aw[2]==1)):
            C5[r,a]=T[r,a]


def forward_local(r,a,b):
    # Normal words: 0=I; 1+2a+b = u_0a^*u_0b.
    if r==0:return {1+2*a+b:1}
    d={1+2*a+b:-1}
    if a==b:d[0]=1
    return d


source=json.loads((ROOT/'auxiliary_joint_phase_exact_obstruction.json').read_text())
expected=[([0,1,0,1],2,2,-1,0),([0,1,0,2],2,0,-1,0),
          ([0,2,0,1],2,6,1,16),([0,2,0,3],0,6,1,0)]
assert [(r['word_key'],r['row'],r['column'],r['weight'],r['exact_rhs'])
        for r in source['rows']] == expected
total_plus=np.zeros(4096,dtype=np.int64)
total_minus=np.zeros(4096,dtype=np.int64)
total_rhs=0;records=[]
for rec in source['rows']:
    key=tuple(rec['word_key']);p=rec['row'];q=rec['column'];weight=rec['weight']
    plus=np.zeros(4096,dtype=np.int64);minus=plus.copy();rhs=0;rawcount=0
    for r,a,b in product(range(16),repeat=3):
        sign=1
        for i in range(4):
            sign*=forward_local(WORDS[r][i],WORDS[a][i],WORDS[b][i]).get(key[i],0)
            if not sign:break
        if not sign:continue
        rawcount+=1
        j=(r*16+b)*16+q;k=(r*16+a)*16+p
        x=sign*int(T[r,a,p]);y=sign*int(T[r,b,q])
        plus[j]+=x;plus[k]+=y
        minus[j]+=x;minus[k]-=y
        rhs+=sign*(int(C4[r,a,p])*int(C5[r,b,q])+int(C5[r,a,p])*int(C4[r,b,q]))
    assert rhs==rec['exact_rhs']
    total_plus+=weight*plus;total_minus+=weight*minus;total_rhs+=weight*rhs
    nonzero=[]
    for index in np.flatnonzero(plus):
        r,x=divmod(int(index),256);a,p0=divmod(x,16)
        nonzero.append({'mixed_coefficient_output_row':r,'laboratory_input':a,'boundary_column':p0,
                        'coefficient':int(plus[index])})
    records.append(dict(rec,forward_raw_terms=rawcount,real_unknown_sparse_row=nonzero))
assert not np.any(total_plus)
assert total_rhs==16
# Directly check the three-variable human-readable form of all four rows.
ABC=[]
for a,p in [(2,2),(3,0),(6,6)]:
    v=np.zeros(4096,dtype=np.int64)
    for r,sign in [(10,1),(11,-1),(14,-1),(15,1)]:v[(r*16+a)*16+p]=sign
    ABC.append(v)
A,B,C=ABC
for rec,target in zip(records,[8*A,4*(-A+B),4*(A+C),4*(B-C)]):
    v=np.zeros(4096,dtype=np.int64)
    for item in rec['real_unknown_sparse_row']:
        index=(item['mixed_coefficient_output_row']*16+item['laboratory_input'])*16+item['boundary_column']
        v[index]=item['coefficient']
    assert np.array_equal(v,target)
out={'status':'PASS','verified_dual_rows':len(records),
     'weighted_real_unknown_coefficient_sum_zero':True,
     'real_unknown_count':4096,'weighted_rhs':int(total_rhs),
     'weighted_imaginary_operator_nonzero_columns':int(np.count_nonzero(total_minus)),
     'exact_contradiction':'0=16 after taking real parts of four independently reduced normal-word equations',
     'needs_modular_rank_or_elimination':False,
     'three_real_combinations_form_verified':['8A=0','4(-A+B)=0','4(A+C)=16','4(B-C)=0'],
     'rows':records,
     'scope':'No complete simultaneous multilinear extension with these exact two phase-slot marginals. Private original ancillas are essential to the normal-word independence argument.'}
(ROOT/'auxiliary_joint_phase_independent_audit_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: four exact forward-reduced rows annihilate all4096 real unknowns and have RHS16.',flush=True)
for rec in records:
    print(rec['weight'],rec['word_key'],rec['row'],rec['column'],'rhs',rec['exact_rhs'],
          'sparse row',rec['real_unknown_sparse_row'],flush=True)
