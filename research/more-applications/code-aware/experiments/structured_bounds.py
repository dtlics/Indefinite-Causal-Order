"""Exact support counts, partial records, rare-fault bounds, and fermionic tests."""
from __future__ import annotations
from collections import Counter
import json,itertools,math
import numpy as np
from core import *

def pauli_support(n,edges):
 out={(0,0)}
 for j in range(n):
  for a,b in [(1,0),(0,1),(1,1)]:out.add((a<<j,b<<j))
 for j,k in edges:
  for (a,b),(c,e) in itertools.product([(1,0),(0,1),(1,1)],repeat=2):
   out.add(((a<<j)|(c<<k),(b<<j)|(e<<k)))
 return sorted(out)

def support_norm(n,edges):
 P=pauli_support(n,edges);counts=Counter()
 for u,(x,z) in enumerate(P):
  for y,w in P[u+1:]:
   if ((x&w).bit_count()+(z&y).bit_count())%2:counts[(x^y,z^w)]+=2
 deg=[0]*n
 for j,k in edges:deg[j]+=1;deg[k]+=1
 return max(counts.values()),2+6*max(deg),len(P)

def records():
 rng=np.random.default_rng(8421);res=[]
 for d in [2,4,8,16]:
  for k in range(8):
   U,_=np.linalg.qr(rng.normal(size=(d,d))+1j*rng.normal(size=(d,d)))
   F=np.exp(2j*np.pi*np.outer(np.arange(d),np.arange(d))/d)/np.sqrt(d)
   O=np.abs(U.conj().T@(U@F))**2
   joint=O@O.T/d
   labels=np.arange(d)%2
   equal=(labels[:,None]==labels[None,:])
   observed=float(joint[equal].sum())
   res.append(abs(observed-.5))
 assert max(res)<1e-12
 eta=.01;gap=(1-2*eta)**2/2
 N=math.ceil(2*math.log(100)/gap**2)
 return {'cases':len(res),'max_MUB_coarse_record_residual':max(res),'balanced_bit_99pct_noiseless_trials':7,
 'noisy_bit_eta':eta,'conservative_99pct_trials':N,'calls':3*N}

def fermion():
 rng=np.random.default_rng(8873);rows=[]
 lower=np.array([[0,1],[0,0]],complex)
 for n in [2,3,4]:
  d=2**n
  ops=[kron_all([Z if k<j else lower if k==j else I2 for k in range(n)]) for j in range(n)]
  full=np.zeros(d,complex);full[-1]=1;rho=np.outer(full,full.conj())
  eff=np.diag([int(i.bit_count()==n-2) for i in range(d)])
  for rep in range(16):
   u=rng.normal(size=n)+1j*rng.normal(size=n);u/=np.linalg.norm(u)
   v=rng.normal(size=n)+1j*rng.normal(size=n);v/=np.linalg.norm(v)
   a=sum(x*k for x,k in zip(u,ops));b=sum(x*k for x,k in zip(v,ops))
   ga,gb=rng.uniform(.01,1,2);ha=1-np.sqrt(1-ga);hb=1-np.sqrt(1-gb)
   A=[np.eye(d)-ha*a.conj().T@a,np.sqrt(ga)*a]
   B=[np.eye(d)-hb*b.conj().T@b,np.sqrt(gb)*b]
   overlap=abs(np.vdot(u,v))**2
   p=metrics(A,B)['p_minus']
   expected=ha**2*hb**2*overlap*(1-overlap)/8+overlap*(ga*hb**2+gb*ha**2)/8+ga*gb*(1-overlap)/4
   twoholes=float(np.trace(eff@apply(B,apply(A,rho))).real)
   ordinary=ga*gb*(1-overlap)
   rows.append({'n':n,'gA':float(ga),'gB':float(gb),'overlap':float(overlap),
     'switch_residual':float(abs(p-expected)),'ordinary_residual':float(abs(twoholes-ordinary))})
 assert max(r['switch_residual'] for r in rows)<1e-12
 assert max(r['ordinary_residual'] for r in rows)<1e-12
 return rows

def main():
 rng=np.random.default_rng(51);graphs=[]
 for n in range(2,13):
  pairs=list(itertools.combinations(range(n),2))
  for density in [0,.1,.25,.5,1]:
   edges=[p for p in pairs if rng.random()<density]
   found,formula,r=support_norm(n,edges)
   assert found==formula,(n,edges,found,formula)
   graphs.append({'n':n,'edges':len(edges),'span_dimension':r,'norm_squared':found})
 rare=[]
 for p in [1e-3,1e-6,1e-9]:
  rare.append({'event_probability':p,'all_higher_order_99pct_balanced_lower_bound':math.ceil(math.log(.02)/math.log1p(-p))})
 out={'graph_support_checks':graphs,'partial_records':records(),'fermionic_cases':fermion(),'rare_event_bounds':rare}
 open('structured_bounds.json','w').write(json.dumps(out,indent=2))
 print('PASS',len(graphs),'exact graph counts;',len(out['fermionic_cases']),'fermionic pairs;',out['partial_records'])
if __name__=='__main__':main()
