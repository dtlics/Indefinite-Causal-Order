"""Portable Gaussian-rational quartet fixtures, copied from source archive without altering values."""
from itertools import product, combinations
from pathlib import Path
import sympy as s

I2=s.eye(2);I16=s.eye(16);X=s.Matrix([[0,1],[1,0]]);Y=s.Matrix([[0,-s.I],[s.I,0]]);Z=s.diag(1,-1)
WORDS=list(product(range(2),repeat=4))
def tensor(items):return s.kronecker_product(*items)
def local(i,a):return tensor([a if j==i else I2 for j in range(4)])
def proj(a):
 b=s.Matrix.hstack(*a.columnspace());return s.simplify(b*(b.H*b).inv()*b.H)
vectors=[({(0,0,0):1,(0,1,1):1},2),({(0,0,1):2,(1,0,0):1,(1,0,1):1,(1,1,0):-1,(1,1,1):-1},8),({(0,1,0):1},1),({(1,1,0):1,(1,1,1):1},2)]
E=[]
for i,(v,den) in enumerate(vectors):
 e=s.zeros(16)
 for r,p in enumerate(WORDS):
  for c,q in enumerate(WORDS):
   if p[i]==q[i]:e[r,c]=s.Rational(v.get(p[:i]+p[i+1:],0)*v.get(q[:i]+q[i+1:],0),den)
 E.append(e)
choices={};envelopes={}
for i,j in combinations(range(4),2):
 hi=proj(sum((local(j,a)*E[i]*local(j,a).H for a in [I2,X,Y,Z]),s.zeros(16)))
 hj=proj(sum((local(i,a)*E[j]*local(i,a).H for a in [I2,X,Y,Z]),s.zeros(16)))
 cc=I16-hi-hj;choices[i,j]=[hj,hj+cc];envelopes[i,j]=(hi,hj,cc)
def remove(i,a):
 inds=[n for n,p in enumerate(WORDS) if p[i]==0];return a.extract(inds,inds)
def present(p):
 return str(p)

def comm(a,b): return a*b-b*a

def commutant_basis(matrices):
    n = matrices[0].rows
    constraints = s.Matrix.vstack(*[
        s.kronecker_product(a, s.eye(n))-s.kronecker_product(s.eye(n), a.T) for a in matrices])
    result = [s.Matrix(n, n, v) for v in constraints.nullspace()]
    assert all(comm(a, b) == s.zeros(n) for a in result for b in matrices)
    return result


def simple_components(basis):
    n = basis[0].rows
    equations = s.Matrix.vstack(*[
        s.Matrix.hstack(*[comm(a, b).reshape(n*n, 1) for a in basis])
        for b in basis])
    center = [sum((v[j]*basis[j] for j in range(len(basis))), s.zeros(n))
              for v in equations.nullspace()]
    for trial in range(2, 30):
        separator = sum((trial**j*c for j, c in enumerate(center)), s.zeros(n))
        spectrum = separator.eigenvals()
        if len(spectrum) == len(center):
            break
    else:
        raise AssertionError('A separating central element was not found')
    result = []
    for value in spectrum:
        p = s.eye(n)
        for other in spectrum:
            if other != value:
                p = p*(separator-other*s.eye(n))/(value-other)
        assert p == p.H and p*p == p
        dim = s.Matrix.hstack(*[(p*a).reshape(n*n, 1) for a in basis]).rank()
        size, exact = s.integer_nthroot(dim, 2)
        assert exact
        result.append((int(size), p))
    assert sum((p for _, p in result), s.zeros(n)) == s.eye(n)
    return result


origins=[I2,X,Y,Z]+[(3*I2+4*s.I*a)/5 for a in [X,Y,Z]]
R=[I16+(local(i,Z)-I16)*E[i] for i in range(4)]
def transport(i,j,p,c):
 cj=local(j,c);aj=R[j]*cj*R[j]
 v=cj.H*(p+(I16-p)*aj)
 vi=s.simplify(R[i]*v*R[i])
 assert (vi*vi.H-I16).applyfunc(s.expand)==s.zeros(16)
 assert all((vi*local(i,x)-local(i,x)*vi).applyfunc(s.expand)==s.zeros(16) for x in [X,Y,Z])
 return remove(i,vi)
