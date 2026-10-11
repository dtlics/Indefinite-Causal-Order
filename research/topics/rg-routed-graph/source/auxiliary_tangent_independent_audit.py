"""Independent exact audit of the complete 583-dimensional auxiliary tangent space.

Rebuilds every retained rank row from raw word reductions, constructs the
boundary/cut generators from independent carriers, and checks extras by forward
raw-to-normal reduction. No saved echelon matrix is trusted as a rank proof.
"""
from pathlib import Path
from itertools import product
from collections import deque
import json, math, time
import numpy as np
import scipy.sparse as sp
import sympy as s
from exact_fixtures import E,I16,I2,X,Y,Z,R,WORDS,tensor,local
ROOT=Path(__file__).parent
PRIME=1000003
assert s.isprime(PRIME)

# Independent normalized coefficient construction: for x_i=|o_i><a_i|,
# delta_i(x_i)=((-1)^(o_i+a_i)-1)x_i.
T=np.zeros((16,16,16),dtype=np.int64)
for o,ow in enumerate(WORDS):
    for a,aw in enumerate(WORDS):
        row=4*s.eye(16)[a,:]
        for i in range(4):
            if ow[i]!=aw[i]:row-=8*E[i][a,:]
        assert all(x.is_Integer for x in row)
        T[o,a,:]=[int(x) for x in row]
assert np.max(np.abs(T))<=4
A=(T*pow(4,-1,PRIME))%PRIME

# Explicit local reduction dictionary, generated from U^dagger U=I.
# local normal keys: constant=0; diagonal-row-zero (a,b)=1+2a+b;
# opposite-output-row (r,a,b)=4r+2a+b in its separate XOR sector.
def reduce_local(r,a,t,b):
    if r!=t:return [(4*r+2*a+b,1)]
    if r==0:return [(1+2*a+b,1)]
    out=[(1+2*a+b,-1)]
    if a==b:out.append((0,1))
    return out

INVERSE={}
for delta in [0,1]:
    inv=[[] for _ in range(8 if delta else 5)]
    for r,a,t,b in product(range(2),repeat=4):
        if (r^t)!=delta:continue
        for key,sg in reduce_local(r,a,t,b):inv[key].append((r,a,t,b,sg))
    INVERSE[delta]=inv

def raw_terms(mask,choice):
    parts=[INVERSE[(mask>>(3-i))&1][choice[i]] for i in range(4)]
    for terms in product(*parts):
        r=a=t=b=0;sg=1
        for rr,aa,tt,bb,sign in terms:
            r=2*r+rr;a=2*a+aa;t=2*t+tt;b=2*b+bb;sg*=sign
        yield r,a,t,b,sg

def integer_row(mask,kind,record):
    choice,p,q=record;parity=-1 if kind=='real' else 1
    row={}
    for r,a,t,b,sg in raw_terms(mask,choice):
        k=(r*16+b)*16+q
        row[k]=row.get(k,0)+sg*int(T[r,a,p])
        k=(t*16+a)*16+p
        row[k]=row.get(k,0)+sg*parity*int(T[t,b,q])
    return {k:v for k,v in row.items() if v}

def insert(row,pivots):
    row={int(k):int(v)%PRIME for k,v in row.items() if int(v)%PRIME}
    while row:
        k=min(row);v=row[k]
        if k not in pivots:
            inv=pow(v,-1,PRIME)
            pivots[k]={j:(x*inv)%PRIME for j,x in row.items()}
            return True
        for j,x in pivots[k].items():
            y=(row.get(j,0)-v*x)%PRIME
            if y:row[j]=y
            elif j in row:del row[j]
    return False

start=time.time();constraints={};rank_records=[]
for mask in range(16):
    for kind in ['real','imag']:
        ref=json.loads((ROOT/f'auxiliary_tangent_output_block_{mask}_{kind}.json').read_text())
        assert ref['prime']==PRIME and ref['variables']==4096
        piv={}
        for rec in ref['rows']:
            assert insert(integer_row(mask,kind,rec),piv), (mask,kind,rec)
        assert len(piv)==ref['rank_lower_bound']
        constraints[mask,kind]=piv
        rank_records.append({'mask':mask,'kind':kind,'independent_rank':len(piv),'nullity_upper_bound':4096-len(piv)})
    print('Retained rank rows independently verified, XOR',mask,flush=True)
upper=sum(r['nullity_upper_bound'] for r in rank_records)
assert upper==583
(ROOT/'auxiliary_tangent_independent_audit_rank_checks.json').write_text(json.dumps({'status':'PASS','prime':PRIME,'total_nullity_upper_bound':upper,'blocks':rank_records},indent=2)+'\n')
print('All 32 rank certificates PASS; upper bound 583. Seconds',time.time()-start,flush=True)

# Independent physical-cylinder bases, already derived parameterwise in the cut audit.
cut_data=json.loads((ROOT/'continuous_product_supported_cut_audit_all_cylinders_checks.json').read_text())['cuts']
def carrier_basis(L):
    rec=next(x for x in cut_data if x['before_queries']==[i+1 for i in L])
    rr=[i for i in range(4) if i not in L]
    spectators=[s.Matrix([s.sympify(v) for v in col]) for col in rec['after_carrier_basis']]
    cols=[]
    for left in product(range(2),repeat=len(L)):
        for v in spectators:
            col=s.zeros(16,1)
            for right in product(range(2),repeat=len(rr)):
                w=[0]*4
                for i,b in zip(L,left):w[i]=b
                for i,b in zip(rr,right):w[i]=b
                n=sum(b<<(3-i) for i,b in enumerate(w))
                a=sum(b<<(len(rr)-1-i) for i,b in enumerate(right))
                col[n]=v[a]
            cols.append(col)
    return s.Matrix.hstack(*cols)
Bs=[carrier_basis([i]) for i in range(4)]+[carrier_basis([0,1])]
assert [b.cols for b in Bs]==[4,4,2,2,4]

def modmat(M):
    return np.array([[int(x.p)*pow(int(x.q),-1,PRIME)%PRIME for x in row] for row in M.tolist()],dtype=np.int64)
def hermitian_coordinates(n):
    for i in range(n):
        h=s.zeros(n);h[i,i]=1;yield h,'real'
    for i in range(n):
        for j in range(i+1,n):
            h=s.zeros(n);h[i,j]=h[j,i]=1;yield h,'real'
            h=s.zeros(n);h[i,j]=1;h[j,i]=-1;yield h,'imag'

generators={(m,k):{} for m in range(16) for k in ['real','imag']}
def add_vector(mask,kind,v):
    flat=np.asarray(v,dtype=np.int64).reshape(4096)%PRIME
    return insert({i:int(x) for i,x in enumerate(flat) if x},generators[mask,kind])

for H,kind in hermitian_coordinates(16):
    h=modmat(H)
    # Past: F H has only XOR zero.
    add_vector(0,kind,np.array([(A[o]@h)%PRIME for o in range(16)]))
    # Future: H F has one independent monomial coefficient at each future/output pair.
    for mask in range(16):
        vv=np.array([(int(h[r,r^mask])*A[r^mask])%PRIME for r in range(16)],dtype=np.int64)
        add_vector(mask,kind,vv)

units=[s.Matrix(2,2,lambda r,c:int(r==a and c==b)) for a,b in product(range(2),repeat=2)]
for i,B in enumerate(Bs[:4]):
    reps=[modmat(R[i]*local(i,u)*R[i]) for u in units]
    bit=1<<(3-i)
    for H,kind in hermitian_coordinates(B.cols):
        h=modmat(B*H*B.H);mats=[h@a%PRIME for a in reps]
        for mask in [0,bit]:
            vv=np.zeros((16,16,16),dtype=np.int64)
            for r,n in product(range(16),repeat=2):
                oi=((r^mask)>>(3-i))&1;ni=(n>>(3-i))&1
                t=(n&~bit)|(r&bit)
                vv[r,n,:]=mats[2*oi+ni][t,:]
            add_vector(mask,kind,vv)

left={}
for o,n in product(range(4),repeat=2):
    M=np.zeros((16,16),dtype=np.int64)
    for r in range(4):M[4*o+r,:]=A[4*o+r,4*n+r,:]
    left[o,n]=M
B=Bs[4]
for H,kind in hermitian_coordinates(B.cols):
    h=modmat(B*H*B.H);mats={key:h@M%PRIME for key,M in left.items()}
    for mask in [0,4,8,12]:
        vv=np.zeros((16,16,16),dtype=np.int64)
        for r,n in product(range(16),repeat=2):
            t=4*(r//4)+(n%4)
            vv[r,n,:]=mats[(r^mask)//4,n//4][t,:]
        add_vector(mask,kind,vv)

ref_cut=json.loads((ROOT/'auxiliary_tangent_cut_span_checks.json').read_text())['blocks']
cut_records=[]
for mask in range(16):
    rec={'mask':mask}
    for kind in ['real','imag']:
        piv=generators[mask,kind]
        rec[kind+'_dimension']=len(piv)
        assert len(piv)==ref_cut[mask][kind+'_dimension']
        # Check every independently reconstructed generator basis against every
        # recomputed retained coefficient row, using bounded exact integer products.
        cs=constraints[mask,kind];data=[];rs=[];cols=[]
        for rowno,row in enumerate(cs.values()):
            for j,v in row.items():data.append(v);rs.append(rowno);cols.append(j)
        mat=sp.csr_matrix((np.array(data,dtype=np.int64),(rs,cols)),shape=(len(cs),4096))
        dense=np.zeros((4096,len(piv)),dtype=np.int64)
        for k,row in enumerate(piv.values()):
            for j,v in row.items():dense[j,k]=v
        assert max(map(len,cs.values()))*(PRIME-1)**2<2**63
        assert not np.any((mat@dense)%PRIME), (mask,kind)
    cut_records.append(rec)
cut_total=sum(len(v) for v in generators.values())
assert cut_total==557
print('Independent boundary/cut generators: 557 dimensions; every retained row annihilates them.',flush=True)

# Forward reduction of every raw word for each rational extra block.
extras=json.loads((ROOT/'auxiliary_tangent_extra_directions.json').read_text())['directions']
assert len(extras)==26
extra_records=[]
for mask in [0,1,2,4]:
    sizes=[8 if (mask>>(3-i))&1 else 5 for i in range(4)]
    count=math.prod(sizes)
    for kind in ['real','imag']:
        ds=[d for d in extras if d['mask']==mask and d['kind']==kind]
        N=len(ds);C=np.zeros((16,16,16,N),dtype=np.int64)
        for k,d in enumerate(ds):
            for j,value in d['integer_coefficients'].items():
                r,t=divmod(int(j),256);a,b=divmod(t,16);C[r,a,b,k]=value
        assert np.max(np.abs(C))<=78
        normal=np.zeros((count,16,16,N),dtype=np.int64)
        parity=-1 if kind=='real' else 1
        for r,a,b in product(range(16),repeat=3):
            t=r^mask
            if not np.any(C[r,b]) and not np.any(C[t,a]):continue
            raw=T[r,a,:,None,None]*C[r,b,None,:,:]+parity*C[t,a,:,None,:]*T[t,b,None,:,None]
            assert np.max(np.abs(raw))<=2*4*78
            pieces=[reduce_local(WORDS[r][i],WORDS[a][i],WORDS[t][i],WORDS[b][i]) for i in range(4)]
            for choices in product(*pieces):
                key=0;sign=1
                for size,(digit,sg) in zip(sizes,choices):key=key*size+digit;sign*=sg
                normal[key]+=sign*raw
        assert not np.any(normal), (mask,kind)
        # Check independent rational directions remain independent modulo PRIME
        # over the independently reconstructed cut/boundary span.
        for d in ds:
            inv=pow(d['denominator'],-1,PRIME)
            vector={int(j):int(value)*inv%PRIME for j,value in d['integer_coefficients'].items()}
            assert insert(vector,generators[mask,kind]), d['free_index']
        extra_records.append({'mask':mask,'kind':kind,'directions':N,
                              'all_normal_coefficients_checked':count*256*N,
                              'defect_coefficients':0})
        print('Forward raw-word exact verification PASS',mask,kind,N,flush=True)
lower=sum(len(v) for v in generators.values())
assert lower==583

# Separate concrete two-dimensional-ancilla independence certificate for the
# constant and twelve U4-conjugation block functions.
H=s.Matrix([[1,1],[1,-1]])/s.sqrt(2);S=s.diag(1,s.I)
CNOT=s.zeros(4)
for i in range(4):CNOT[2*(i//2)+((i%2)^(i//2)),i]=1
gates=[s.kronecker_product(H,I2),s.kronecker_product(I2,H),
       s.kronecker_product(S,I2),s.kronecker_product(I2,S),CNOT]
initial=tuple(s.kronecker_product(p,I2) for p in [X,Y,Z])
queue=deque([(initial,())]);seen=set();evalrows=[];contexts=[];rank=0
while queue and rank<13:
    triple,word=queue.popleft();key=tuple(tuple(m) for m in triple)
    if key in seen:continue
    seen.add(key);contexts.append(list(word))
    for r,t in product(range(2),repeat=2):
        evalrows.append([int(r==t)]+[triple[k][2*b+r,2*d+t]
                                   for k in range(3) for b,d in product(range(2),repeat=2)])
    rank=s.Matrix(evalrows).rank()
    for k,g in enumerate(gates):
        nxt=tuple((g.H*m*g).applyfunc(s.simplify) for m in triple)
        queue.append((nxt,word+(k,)))
assert rank==13
M=s.Matrix(evalrows);selected=list(M.T.rref()[1]);minor=M.extract(selected,list(range(13)))
assert len(selected)==13 and minor.det()!=0

report={'status':'PASS','exact_complete_tangent_real_dimension':583,
        'all_32_retained_modular_rank_systems_recomputed':True,
        'constraint_nullity_upper_bound':upper,
        'independent_boundary_cut_dimension':cut_total,
        'all_26_rational_extras_checked_by_forward_raw_word_reduction':True,
        'independent_extra_dimensions_over_cut_space':26,
        'lower_bound_dimension':lower,
        'private_ancilla_word_independence':{'ancilla_dimension':2,'function_count':13,
             'explicit_Clifford_evaluation_rank':13,'evaluation_context_gate_words':contexts,
             'selected_evaluation_rows':selected,'nonzero_minor_determinant':str(minor.det()),
             'gates':['H physical','H ancillary','S physical','S ancillary','CNOT physical to ancillary']},
        'cut_blocks':cut_records,'extra_blocks':extra_records,
        'scope':'Exact real-linear complete tangent space only; no auxiliary integration or routed-host inference'}
(ROOT/'auxiliary_tangent_independent_audit_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2),flush=True)
