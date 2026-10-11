"""Enumerate exact maximal linear spaces for the factorizable curvature forms."""
from pathlib import Path
import json,collections,time
import sympy as s
ROOT=Path(__file__).parent;j=json.loads((ROOT/'auxiliary_host_rank_two_factor_graph.json').read_text());V=[s.Matrix(1,37,[s.Rational(x) for x in row]) for row in j['vectors']];freq=collections.Counter(i for pair in j['pairs'] for i in pair)
pairs=sorted(j['pairs'],key=lambda p:-(freq[p[0]]+freq[p[1]]));start=time.time()
def mat(key):return s.Matrix(key) if key else s.zeros(0,37)
def canon(A):
    rr,p=A.rref();return tuple(tuple(rr[i,:]) for i in range(len(p)))
def contains(A,B):
    # True iff kernel(A) is contained in kernel(B).
    M=mat(A);N=mat(B)
    if len(B)>len(A):return False
    return M.col_join(N).rank()==len(A)
components=[()]
for k,pair in enumerate(pairs):
    cand=set()
    for key in components:
        M=mat(key)
        for index in pair:cand.add(canon(M.col_join(V[index])))
    components=[]
    for key in sorted(cand,key=lambda x:(len(x),str(x))):
        if not any(contains(key,small) for small in components):components.append(key)
    if k%10==0:print(k+1,'components',len(components),'codims',collections.Counter(map(len,components)),'seconds',time.time()-start,flush=True)
out={'status':'EXACT_RANK_TWO_SUBFAMILY_ALTERNATIVES','quotient_dimension':37,'components':[{'codimension':len(key),'rows':[[str(x) for x in row] for row in key]} for key in components],'scope':'Only factorizable RREF forms included; remaining irreducible quadrics must still be imposed.'}
(ROOT/'auxiliary_host_rank_two_components_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('DONE',len(components),collections.Counter(map(len,components)),time.time()-start,flush=True)
