"""Exact search of universal scalar Kraus-word filters (no floating arithmetic).
For m independent dxd matrix variables, solve for linear combinations of all
m! orderings whose off-diagonal entries and diagonal differences vanish.
This is a classification inside homogeneous multilinear permutation filters,
not a no-go theorem for all quantum algorithms.
"""
from itertools import permutations, product
from collections import defaultdict
from pathlib import Path
import json
import sympy as s

OUT=Path(__file__).resolve().parent

def words(d,m):
    perms=list(permutations(range(m)))
    entries={}
    for r in range(d):
      for c in range(d):
        polys=[]
        for pi in perms:
            poly=defaultdict(int)
            for inner in product(range(d), repeat=m-1):
                path=(r,)+inner+(c,)
                mon=[None]*m
                for j,var in enumerate(pi):mon[var]=(path[j],path[j+1])
                poly[tuple(mon)]+=1
            polys.append(poly)
        entries[r,c]=polys
    return perms,entries

def solve(d,m):
    perms,E=words(d,m); n=len(perms)
    constraints=defaultdict(lambda:[0]*n)
    for r in range(d):
      for c in range(d):
        if r==c:continue
        for j,poly in enumerate(E[r,c]):
          for mon,coeff in poly.items():constraints[(r,c,mon)][j]+=coeff
    for r in range(1,d):
      for j in range(n):
        for mon,coeff in E[0,0][j].items():constraints[('diag',r,mon)][j]+=coeff
        for mon,coeff in E[r,r][j].items():constraints[('diag',r,mon)][j]-=coeff
    rows=[v for v in constraints.values() if any(v)]
    # duplicate and sign duplicate rows discarded without changing row span
    uniq={}
    for row in rows:
      first=next(x for x in row if x)
      if first<0:row=[-x for x in row]
      uniq[tuple(row)]=1
    mat=s.Matrix(list(uniq))
    ker=mat.nullspace()
    allmon=sorted(set().union(*(set(p) for p in E[0,0])))
    evals=s.Matrix([[sum(E[0,0][j].get(mon,0)*v[j] for j in range(n)) for v in ker] for mon in allmon]) if ker else s.zeros(len(allmon),0)
    central_dim=evals.rank()
    res={'dimension':d,'degree':m,'words':n,'constraint_rows':len(uniq),
         'kernel_dimension':len(ker),'nonzero_central_polynomial_dimension':central_dim,
         'polynomial_identity_dimension':len(ker)-central_dim,
         'kernel_basis':[[int(x) if x.q==1 else str(x) for x in v] for v in ker],
         'word_order':[''.join(chr(65+x) for x in pi) for pi in perms]}
    return res

if __name__=='__main__':
    results=[]
    for d,m in [(2,1),(2,2),(2,3),(2,4),(3,4)]:
        r=solve(d,m);results.append(r)
        print({k:v for k,v in r.items() if k not in ['kernel_basis','word_order']},flush=True)
    (OUT/'polynomial_search.json').write_text(json.dumps(results,indent=2))
