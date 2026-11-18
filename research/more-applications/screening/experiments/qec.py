"""Exact Pauli-history enumeration and independent matrix checks for QEC screens."""
from core import *
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent

def symplectic(s):
    n=len(s);x=z=0
    for i,c in enumerate(s):
        if c in 'XY':x|=1<<i
        if c in 'ZY':z|=1<<i
    return x|(z<<n)

def anti(a,b,n):
    m=(1<<n)-1
    return (((a&m)&(b>>n)).bit_count()+((a>>n)&(b&m)).bit_count())%2

def all_paulis(n):return np.arange(4**n,dtype=np.int64)

def weight(a,n):
    return ((a&((1<<n)-1))|(a>>n)).bit_count()

def code_data(n,generator_strings,Lx,Lz):
    gens=[symplectic(s) for s in generator_strings]
    assert all(anti(a,b,n)==0 for a in gens for b in gens)
    group={0}
    for g in gens: group|={h^g for h in list(group)}
    assert len(group)==2**len(gens) and len(gens)==n-1
    assert anti(symplectic(Lx),symplectic(Lz),n)==1
    assert all(anti(symplectic(Lx),g,n)==anti(symplectic(Lz),g,n)==0 for g in gens)
    ns=2**len(gens);total=4**n
    syn=np.array([sum(anti(a,g,n)<<j for j,g in enumerate(gens)) for a in range(total)])
    corr=np.full(ns,-1,dtype=np.int64)
    for a in sorted(range(total),key=lambda a:weight(a,n)):
        if corr[syn[a]]<0:corr[syn[a]]=a
    assert np.all(corr>=0)
    lx,lz=symplectic(Lx),symplectic(Lz)
    logical=np.array([anti(a^int(corr[syn[a]]),lz,n)+2*anti(a^int(corr[syn[a]]),lx,n) for a in range(total)])
    return syn,logical,corr,np.array([weight(a,n) for a in range(total)])

def dist_single_axis(n,axis,p):
    out=np.zeros(4**n)
    ps=[symplectic('I'*i+axis+'I'*(n-i-1)) for i in range(n)]
    for flags in itertools.product([0,1],repeat=n):
        a=0;prob=1
        for bit,P in zip(flags,ps): a^=P if bit else 0;prob*=p if bit else 1-p
        out[a]+=prob
    return out

def dist_depol(n,p):
    return np.array([(1-p)**(n-weight(a,n))*(p/3)**weight(a,n) for a in range(4**n)])

def syndrome_logical_table(prob,syn,logical):
    out=np.zeros((max(syn)+1,4));np.add.at(out,(syn,logical),prob);return out

def ordinary_intermediate(ta,tb):
    # full joint history of the two ideal syndrome readouts retained.
    vals=np.zeros((ta.shape[0],tb.shape[0],4))
    for x in range(4):
        for y in range(4):vals[:,:,x^y]+=ta[:,x,None]*tb[None,:,y]
    return float(vals.max(axis=2).sum())

def score(n,pa,pb,syn,logical):
    ia=np.flatnonzero(pa);ib=np.flatnonzero(pb);S=np.zeros((int(max(syn))+1,4,2))
    # bound memory independent of number of points; 1024x1024 is modest.
    aa=ia[:,None];bb=ib[None,:];P=aa^bb
    m=(1<<n)-1
    count=np.array([a.bit_count()%2 for a in range(1<<n)],dtype=np.int8)
    b=count[(aa&m)&(bb>>n)]^count[(aa>>n)&(bb&m)]
    w=pa[ia,None]*pb[None,ib]
    np.add.at(S,(syn[P].ravel(),logical[P].ravel(),b.ravel()),w.ravel())
    serial=float(S.sum(axis=2).max(axis=1).sum())
    switch=float(S.max(axis=1).sum())
    mid=ordinary_intermediate(syndrome_logical_table(pa,syn,logical),syndrome_logical_table(pb,syn,logical))
    return dict(F_final_only=serial,F_with_switch_flag=switch,F_with_intermediate_syndrome=mid,p_minus=float(S[:,:,1].sum()),switch_logical_error=1-switch,serial_logical_error=1-serial,intermediate_logical_error=1-mid)

rows=[]
for n,gs,lx,lz,name in [(3,['ZZI','IZZ'],'XXX','ZZZ','repetition3'),(5,['XZZXI','IXZZX','XIXZZ','ZXIXZ'],'XXXXX','ZZZZZ','perfect5'),(7,['XIXIXIX','IXXIIXX','IIIXXXX','ZIZIZIZ','IZZIIZZ','IIIZZZZ'],'XXXXXXX','ZZZZZZZ','Steane7')]:
    syn,logical,corr,weights=code_data(n,gs,lx,lz)
    for p in [.001,.01,.05,.1,.2]:
        for kind in (['depol_depol','X_Z','X_X'] if n<7 else ['X_Z','X_X']):
            if kind=='depol_depol':pa=pb=dist_depol(n,p)
            elif kind=='X_Z':pa=dist_single_axis(n,'X',p);pb=dist_single_axis(n,'Z',p)
            else:pa=pb=dist_single_axis(n,'X',p)
            rows.append(dict(code=name,noise=kind,p=p,**score(n,pa,pb,syn,logical)))
    # deliberately adversarial logical-normalizer noise.
    pa=np.zeros(4**n);pb=pa.copy();pa[symplectic(lx)]=.5;pa[symplectic(lx)^symplectic(lz)]=.5;pb=pa.copy()
    rows.append(dict(code=name,noise='logical_X_or_Y',p=.5,**score(n,pa,pb,syn,logical)))

# Matrix verification: switch of ideal recovery and any Pauli noise on code.
rng=np.random.default_rng(5921)
gens=[pauli_string(s) for s in ['ZZI','IZZ']]
projectors=code_projectors(gens)
R=[]
for bits,P in projectors:
    if bits==(0,0):C=np.eye(8)
    elif bits==(0,1):C=pauli_string('IIX')
    elif bits==(1,0):C=pauli_string('XII')
    else:C=pauli_string('IXI')
    R.append(C@P)
Pcode=projectors[0][1];rho=Pcode/2
allstrings=[''.join(s) for s in itertools.product('IXYZ',repeat=3)]
maxerr=0
for _ in range(20):
    probs=rng.dirichlet(np.ones(64));N=[np.sqrt(p)*pauli_string(s) for p,s in zip(probs,allstrings)]
    # Fraction whose syndrome is nonzero.
    detected=sum(p for p,s in zip(probs,allstrings) if any(np.linalg.norm(pauli_string(s)@g-g@pauli_string(s))>1e-8 for g in gens))
    maxerr=max(maxerr,abs(metrics(R,N,rho)['p_minus']-detected/2))

# A known stabilizer readout with strong signal only on gauge, not on logical data.
# Logical/gauge toy uses I_L tensor Delta_Z and I_L tensor Delta_X.
A=tensor_channels([I2],dephase_axis([0,0,1]));B=tensor_channels([I2],dephase_axis([1,0,0]))
gauge=metrics(A,B)

out={'definitions':{'F':'optimal logical Pauli correction given stated records, NOT optimal unrestricted quantum strategy','intermediate':'ordinary two-layer protocol with perfect syndrome extraction between layers and all syndrome histories retained'},'cases':rows,'matrix_recovery_identity_trials':20,'max_recovery_signal_error':maxerr,'gauge_only_minus_probability':gauge['p_minus']}
(ROOT/'qec_results.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
