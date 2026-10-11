"""Exact diagonal laboratory-input Hermiticity space and Boolean candidates."""
from pathlib import Path
from itertools import product
import json
import numpy as np
import sympy as s
from phase_endpoint_exact import row_tensor, WORDS
ROOT=Path(__file__).parent
T=row_tensor(4,1)


def terms(r,a,b):
    opts=[]
    for i in range(4):
        rr,aa,bb=WORDS[r][i],WORDS[a][i],WORDS[b][i]
        opts.append([(1+2*aa+bb,1)] if rr==0 else
                    ([(0,1)] if aa==bb else [])+[(1+2*aa+bb,-1)])
    for term in product(*opts):
        key=0;sg=1
        for digit,sign in term:key=5*key+digit;sg*=sign
        yield key,sg


normal=np.zeros((625,256,16),dtype=np.int64)
raw_terms=[]
for r,a,b in product(range(16),repeat=3):
    raw=np.outer(T[r,a],T[r,b]).reshape(256)
    if not np.any(raw):continue
    ts=list(terms(r,a,b));raw_terms.append((a,b,raw,ts))
    for key,sg in ts:
        normal[key,:,b]+=sg*raw
        normal[key,:,a]-=sg*raw
N=normal.reshape(625*256,16)
assert 625*256*(4096*16)**2 < 2**63
G=N.T@N
GS=s.Matrix(G.tolist())
ns=GS.nullspace();print('Exact Hermiticity dimension',len(ns),flush=True)
nsM=s.Matrix.hstack(*ns)
assert GS*nsM==s.zeros(16,len(ns))
allbits=((np.arange(65536,dtype=np.int64)[:,None]>>np.arange(16))&1)
good=allbits[np.all(allbits@G==0,axis=1)]
print('Boolean Hermitian flags',len(good),flush=True)
records=[]
for bits in good:
    defect=np.zeros((625,256),dtype=np.int64)
    for a,b,raw,ts in raw_terms:
        weight=int(bits[b])*(int(bits[a])-1)
        if not weight:continue
        for key,sg in ts:defect[key]+=weight*sg*raw
    valid=not np.any(defect)
    records.append({'support':[i for i,b in enumerate(bits) if b],
                    'rank':int(sum(bits)),'complete_projection':valid,
                    'nonzero_projection_word_keys':int(sum(np.any(defect,axis=1)))})
    print(records[-1],flush=True)
closure=all(GS*s.matrix_multiply_elementwise(v,w)==s.zeros(16,1) for v in ns for w in ns)
assert len(ns)==10 and len(good)==320 and all(r['complete_projection'] for r in records)
valid=[frozenset(r['support']) for r in records]
minimal=[a for a in valid if a and not any(b and b<a for b in valid)]
partitions=[]
def exact_covers(left,parts):
    if not left:partitions.append(parts);return
    x=min(left)
    for atom in minimal:
        if x in atom and atom<=left:exact_covers(left-atom,parts+[atom])
exact_covers(frozenset(range(16)),[])
assert len(minimal)==13 and len(partitions)==4 and all(len(a)==7 for a in partitions)
all_unions=set()
for atoms in partitions:
    for mask in range(1<<len(atoms)):
        all_unions.add(frozenset().union(*(atoms[i] for i in range(len(atoms)) if mask>>i&1)))
assert all_unions==set(valid)
relations=s.Matrix.hstack(*nsM.T.nullspace()).T.rref()[0]
assert relations.rows==6 and relations*nsM==s.zeros(6,10)
atoms_report=[]
for atom in minimal:
    bits=np.array([int(i in atom) for i in range(16)])
    L=T*bits[None,:,None]
    past=np.array([t@np.diag(bits) for t in T])
    atoms_report.append({'support':sorted(atom),'rank':len(atom),
                         'equals_fixed_past_F_P_coefficientwise':np.array_equal(L,past)})
report={'status':'PASS','Hermitian_flag_linear_dimension':len(ns),
        'Hermitian_flag_basis_columns':[[str(x) for x in v] for v in ns],
        'six_exact_linear_constraint_rows':[[str(x) for x in row] for row in relations.tolist()],
        'linear_space_closed_under_pointwise_products':closure,
        'Boolean_Hermitian_flag_count':len(good),'Boolean_flags':records,
        'complete_Boolean_flag_count':sum(r['complete_projection'] for r in records),
        'minimal_nonzero_complete_flags':atoms_report,
        'maximal_complete_diagonal_partitions':[[sorted(a) for a in atoms] for atoms in partitions],
        'all_complete_Boolean_flags_are_unions_of_one_of_these_partitions':True,
        'scope':'Exact diagonal laboratory-input masks only, not all complete auxiliary records.'}
(ROOT/'auxiliary_four_sector_input_flags_checks.json').write_text(json.dumps(report,indent=2)+'\n')
