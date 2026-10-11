"""Exact spectral multiplicity obstruction for a strict-oriented full auxiliary.

If a nontrivial unital M_r auxiliary commutes with every partition cocycle,
each cocycle eigenvalue has multiplicity divisible by r. One odd multiplicity
therefore excludes r=2,4,8,16 on the dimension-16 boundary.
"""
from pathlib import Path
from itertools import product
import json,numpy as np,sympy as s
from phase_endpoint_exact import row_tensor,WORDS
ROOT=Path(__file__).parent;T=row_tensor(4,1)
# Real Pauli representatives I, X, Z, XZ. Their scalar phases cancel from C_L.
us=[s.eye(2),s.Matrix([[0,1],[1,0]]),s.diag(1,-1),s.Matrix([[0,-1],[1,0]])]
values={}
for choice in product(range(4),repeat=4):
    A=np.zeros((16,16),dtype=np.int64)
    for r,rw in enumerate(WORDS):
        nw=[];sg=1
        for k,o in enumerate(rw):
            n=next(a for a in range(2) if us[choice[k]][o,a]);nw.append(n);sg*=int(us[choice[k]][o,n])
        n=sum(a<<(3-k) for k,a in enumerate(nw));A[r]=sg*T[r,n]
    values[choice]=A
assert np.array_equal(values[(0,0,0,0)],4*np.eye(16,dtype=np.int64))
x=s.Symbol('x');results=[]
for mask in range(1,15):
    left=[i for i in range(4) if mask&(1<<(3-i))];right=[i for i in range(4) if i not in left];witness=None;gcd_all=16;tested=0
    for choice in product(range(4),repeat=4):
        if sum(c!=0 for c in choice)<2:continue
        ll=tuple(c if i in left else 0 for i,c in enumerate(choice));rr=tuple(c if i in right else 0 for i,c in enumerate(choice));C64=values[rr].T@values[choice]@values[ll].T
        assert np.array_equal(C64.T@C64,64**2*np.eye(16,dtype=np.int64))
        char=s.Matrix(C64.tolist()).charpoly(x).as_expr();fac=s.factor_list(char)[1];multip=[int(e) for f,e in fac];gcd_all=int(s.gcd(gcd_all,s.igcd(*multip))) if len(multip)>1 else int(s.gcd(gcd_all,multip[0]));tested+=1
        if any(e%2 for e in multip):
            witness={'real_Pauli_indices':list(choice),'cocycle_integer_scale':64,'characteristic_factors':[{'polynomial':str(f),'multiplicity':int(e)} for f,e in fac],'odd_eigenvalue_multiplicity':True};break
    results.append({'before_queries':[i+1 for i in left],'contexts_tested':tested,'gcd_of_spectral_multiplicities':gcd_all,'witness':witness});print(results[-1],flush=True)
(ROOT/'strict_auxiliary_cocycle_spectral_test_checks.json').write_text(json.dumps({'status':'EXACT_FINITE_SPECTRAL_TEST','results':results,'scope':'An odd-multiplicity witness excludes any nontrivial full matrix auxiliary with that strict partition, including arbitrary multiplicity; absent witness gives no conclusion.'},indent=2)+'\n')
