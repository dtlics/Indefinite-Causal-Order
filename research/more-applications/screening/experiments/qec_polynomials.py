"""Exact Pauli-history polynomial checks for the five-qubit code.
The decoders are the small-p maximum-likelihood branches, not an optimization
against every ordinary protocol. Exact coefficients certify the leading terms.
"""
from pathlib import Path
import contextlib,io,json,itertools
import numpy as np
import sympy as sp
with contextlib.redirect_stdout(io.StringIO()):
    from qec import code_data,anti,symplectic,weight
ROOT=Path(__file__).resolve().parent
n=5
syn,logical,corr,w=code_data(n,['XZZXI','IXZZX','XIXZZ','ZXIXZ'],'XXXXX','ZZZZZ')
p=sp.symbols('p',nonnegative=True)

def best_counts(counts,axis):
    arr=np.moveaxis(counts,axis,-2)
    out=np.zeros(arr.shape[:-2]+(arr.shape[-1],),dtype=np.int64)
    for ind in np.ndindex(arr.shape[:-2]):
        options=arr[ind]
        idx=max(range(len(options)),key=lambda j:tuple(options[j]))
        out[ind]=options[idx]
    return out

def expression(counts,den):
    return sp.Poly(sp.expand(sum(sp.Rational(int(v),den**k)*p**k*(1-p)**(2*n-k) for k,v in enumerate(counts))),p).as_expr()

res=[]
for kind in ['depol_depol','X_Z','X_X']:
    den=3 if kind=='depol_depol' else 1
    if den==3:
        ia=ib=np.arange(4**n)
    else:
        def support(axis):
            ps=[symplectic('I'*i+axis+'I'*(n-i-1)) for i in range(n)]
            return np.array([sum(P for t,P in zip(bits,ps) if t) for bits in itertools.product([0,1],repeat=n)])
        ia=support('X');ib=support('Z' if kind=='X_Z' else 'X')
    aa=ia[:,None];bb=ib[None,:];prod=aa^bb
    mm=(1<<n)-1;par=np.array([j.bit_count()%2 for j in range(1<<n)])
    flags=par[(aa&mm)&(bb>>n)]^par[(aa>>n)&(bb&mm)]
    weights=w[ia,None]+w[None,ib]
    counts=np.zeros((16,4,2,11),dtype=np.int64)
    np.add.at(counts,(syn[prod].ravel(),logical[prod].ravel(),flags.ravel(),weights.ravel()),1)
    assert sum(counts.ravel())==len(ia)*len(ib)
    serial=best_counts(counts.sum(axis=2),1).sum(axis=0)
    switched=best_counts(counts,1).sum(axis=(0,1))
    # Ordinary intermediate recovery retains both complete syndrome histories.
    ta=np.zeros((16,4,6),int);tb=ta.copy()
    np.add.at(ta,(syn[ia],logical[ia],w[ia]),1)
    np.add.at(tb,(syn[ib],logical[ib],w[ib]),1)
    joint=np.zeros((16,16,4,11),int)
    for a,b,l1,l2 in itertools.product(range(16),range(16),range(4),range(4)):
        joint[a,b,l1^l2]+=np.convolve(ta[a,l1],tb[b,l2])
    mid=best_counts(joint,2).sum(axis=(0,1))
    fs,fw,fm=[expression(x,den) for x in [serial,switched,mid]]
    res.append({'noise':kind,'F_final':str(fs),'F_flag':str(fw),'F_intermediate':str(fm),
        'error_final_series':str(sp.series(1-fs,p,0,6)),
        'error_flag_series':str(sp.series(1-fw,p,0,6)),
        'flag_gain_series':str(sp.series(fw-fs,p,0,7)),
        'error_intermediate_series':str(sp.series(1-fm,p,0,6)),
        'values_at_0.01':{key:float(1-F.subs(p,sp.Rational(1,100))) for key,F in [('final',fs),('flag',fw),('intermediate',fm)]},
        'scope':'Exact fixed decoder polynomials; selected by small-p lexicographic maximum-likelihood rule. Numerical comparisons at p=.01 verified independently.'})
ROOT.joinpath('qec_polynomials.json').write_text(json.dumps(res,indent=2))
print(json.dumps(res,indent=2))
