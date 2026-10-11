"""Independent exact free-word/spectral-quotient and physical-realization tests.
No SDP solver, approximate eigenvalue, or floating arithmetic is used.
"""
from fractions import Fraction as F
from pathlib import Path
import json, math, datetime, hashlib
import numpy as np
import sympy as sp
ROOT=Path(__file__).resolve().parents[1]
OUT=Path(__file__).parent
PRIME=1000000007

def red(w):
 s=[]
 for a in w:
  if s and s[-1]==a:s.pop()
  else:s.append(a)
 return tuple(s)
def words(L):return [()]+[tuple((a+j)%2 for j in range(k)) for k in range(1,L+1) for a in range(2)]
def add(*terms):
 d={}
 for k,p in terms:
  for w,c in p.items():d[w]=d.get(w,F(0))+k*c
 return {w:F(c) for w,c in d.items() if c}
def mul(p,q):
 d={}
 for a,c in p.items():
  for b,e in q.items():
   w=red(a+b);d[w]=d.get(w,F(0))+c*e
 return {w:c for w,c in d.items() if c}
def star(p):return {tuple(reversed(w)):c for w,c in p.items()}
def vec(p,ws):return [p.get(w,F(0)) for w in ws]
def mod(x):
 x=F(x);return (x.numerator%PRIME)*pow(x.denominator%PRIME,-1,PRIME)%PRIME
def rankmod(M):
 A=[[mod(x) for x in row] for row in M]; nr=len(A);nc=len(A[0]) if nr else 0;r=0;piv=[]
 for c in range(nc):
  k=next((k for k in range(r,nr) if A[k][c]),None)
  if k is None:continue
  A[r],A[k]=A[k],A[r];z=pow(A[r][c],-1,PRIME);A[r]=[(v*z)%PRIME for v in A[r]]
  for k in range(r+1,nr):
   if A[k][c]:z=A[k][c];A[k]=[(v-z*u)%PRIME for v,u in zip(A[k],A[r])]
  piv.append(c);r+=1
  if r==nr:break
 return r,piv
I={():F(1)};A={(0,):F(1)};B={(1,):F(1)};C={(0,1):F(1,2),(1,0):F(1,2)}

def relation(cs,ends):
 q=I
 for c in cs:q=mul(q,add((1,C),(-c,I)))
 if not ends:g=I;positive=I
 elif ends==[1]:g=add((1,A),(-1,B));positive=add((2,I),(-2,C))
 elif ends==[-1]:g=add((1,A),(1,B));positive=add((2,I),(2,C))
 else:g={(0,1):F(1),(1,0):F(-1)};positive=add((4,I),(-4,mul(C,C)))
 r=mul(g,q);assert mul(star(r),r)==mul(positive,mul(q,q))
 return r

def eval_words(pairs,L):
 """Scalar-split endpoints and full M2 interiors, column vec convention."""
 ws=words(L);rows=[];dims=[];cs=[];ends=[]
 for p,q in pairs:
  d=p*p+q*q;c=F(q*q-p*p,d);s=F(2*p*q,d)
  if not p or not q:
   e=1 if not p else -1;ends.append(e)
   for sig in [1,-1]:
    rr=[np.array([[F(sig)]],object),np.array([[F(e*sig)]],object)];block=[]
    for w in ws:
     V=np.eye(1,dtype=object)
     for a in w:V=V@rr[a]
     block.append(V.T.ravel())
    rows.append(np.array(block,dtype=object).T);dims.append(1)
  else:
   cs.append(c);rr=[np.diag([F(1),F(-1)]),np.array([[c,s],[s,-c]],object)];block=[]
   for w in ws:
    V=np.eye(2,dtype=object)
    for a in w:V=V@rr[a]
    block.append(V.T.ravel())
   rows.append(np.array(block,dtype=object).T);dims.append(2)
 return np.vstack(rows),dims,cs,sorted(ends,reverse=True)

def structural_case(label,pairs,extra_levels=(0,1)):
 E0,dims,cs,ends=eval_words(pairs,1);N=2*len(cs)+len(ends);r=relation(cs,ends);rows=[]
 assert max(map(len,r))==N
 for extra in extra_levels:
  L=N+extra;ws=words(L);ws2=words(2*L);E,*_=eval_words(pairs,L)
  rank,piv=rankmod(E.tolist());assert rank==2*N
  J=[mul(r,{w:F(1)}) for w in words(L-N)]
  Jvec=np.array([vec(z,ws) for z in J],object).T
  assert all(v==0 for v in (E@Jvec).ravel())
  jrank,_=rankmod(Jvec.tolist());assert jrank==len(ws)-2*N
  image=[]
  for z in J:
   for w in ws:
    image.append(vec(mul({tuple(reversed(w)):F(1)},z),ws2))
    image.append(vec(mul(star(z),{w:F(1)}),ws2))
  srank,_=rankmod(np.array(image,object).T.tolist());assert srank==len(ws2)-2*N
  # The image is in the exact evaluation kernel, so this modular rank certifies equality over Q.
  E2,*_=eval_words(pairs,2*L)
  assert all(v==0 for v in (E2@np.array(image[:min(8,len(image))],object).T).ravel())
  rows.append({'L':L,'word_count':len(ws),'spectral_algebra_dimension':2*N,'evaluation_rank_mod_prime':rank,'local_kernel_dimension':jrank,'overlap_kernel_image_rank_mod_prime':srank,'required_overlap_ideal_dimension':len(ws2)-2*N,'exact_rational_annihilator_checks':True})
 return {'label':label,'pairs':pairs,'N':N,'sector_dimensions':dims,'endpoint_central_values':ends,'relation':{' '.join(map(str,w)):str(v) for w,v in sorted(r.items(),key=lambda kv:(len(kv[0]),kv[0]))},'levels':rows}

def projector_ns(Q,ws):
 n=len(ws);T=Q.reshape(2,2,n,n,n,n).transpose(0,2,4,1,3,5).reshape(2*n*n,2*n*n).copy();groups={}
 for x in [0,1]:
  for i,u in enumerate(ws):
   for j,v in enumerate(ws):
    w=red(tuple(reversed(v))+u)
    if w:groups.setdefault(w,[]).append((x*n+i)*n+j)
 for g in groups.values():
  mean=np.sum(T[:,g],axis=1)*F(1,len(g));T[:,g]-=mean[:,None]
 for g in groups.values():
  mean=np.sum(T[g,:],axis=0)*F(1,len(g));T[g,:]-=mean[None,:]
 return T.reshape(2,n,n,2,n,n).transpose(0,3,1,4,2,5).reshape(Q.shape)

def physical_test():
 pairs=[(8,15),(15,8)];L=4;ws=words(L);n=len(ws);E,dims,cs,ends=eval_words(pairs,L);r=relation(cs,ends)
 z=np.array([[1,0],[0,-1]],dtype=object);x=np.array([[0,1],[1,0]],dtype=object);eye=np.eye(2,dtype=object)
 kron=lambda *args: __import__('functools').reduce(np.kron,args)
 AA=kron(x,x,eye);BB=kron(z,eye,eye);CC=kron(z,z,eye);DD=kron(x,eye,eye)
 H=kron(AA,BB)+kron(CC,DD);II=np.eye(64,dtype=object);assert np.array_equal(H@H,2*II)
 factor=II+H;Znum=3*II+2*H;assert np.array_equal(factor@factor.T,Znum)
 Z=Znum*F(1,48)
 assert np.trace(Z)*4==16
 V=np.kron(E,E);qq=V.T@Z@V;Q=np.repeat(qq[None],4,axis=0)
 proj=projector_ns(Q,ws);identity=np.repeat(np.eye(n*n,dtype=object)[None],4,axis=0)
 assert np.array_equal(proj,identity)
 rv=np.array(vec(r,ws),object);RA=np.kron(rv[:,None],np.eye(n,dtype=object));RB=np.kron(np.eye(n,dtype=object),rv[:,None])
 assert all(v==0 for v in (qq@RA).ravel());assert all(v==0 for v in (qq@RB).ravel())
 # Reconstruct on a square exact evaluation frame, including coherent off-angle terms.
 rank,piv=rankmod(E.tolist());Es=sp.Matrix(E[:,piv].tolist());inv=np.array(Es.inv().tolist(),dtype=object)
 inv=np.vectorize(lambda v:F(int(v.p),int(v.q)),otypes=[object])(inv)
 inds=[i*n+j for i in piv for j in piv];Ff=np.kron(inv,inv)
 restored=Ff.T@qq[np.ix_(inds,inds)]@Ff
 assert np.array_equal(restored,Z)
 # Aggregate moment, exact zero and positive scalar polynomial criterion.
 M=sum(Q[k].reshape(n,n,n,n).diagonal(axis1=1,axis2=3).sum(axis=-1) for k in range(4))*F(1,4*n)
 defect=(rv@M@rv);assert defect==0
 # Full physical lift: independently build all 3x3 local charge pairs.
 # Integer matrices avoid any spectral positivity assertion; every block is a CP image of factor factor^T/48.
 sectors=[None,(0,1),(1,0)];sizes=[8,4,4];blocks={}
 for ai,a in enumerate(sectors):
  for bi,b in enumerate(sectors):
   W=Z.copy();da=8;db=8
   if a is not None:
    i,j=a;sub=W.reshape(8,8,8,8)[4*i:4*i+4,:,4*i:4*i+4,:].reshape(2,2,8,2,2,8)
    W=np.einsum('iobjoc->ibjc',sub)*F(1,2)
    W=np.einsum('ibjc,op->iobjpc',W,eye).reshape(4*8,4*8);da=4
   if b is not None:
    i,j=b;sub=W.reshape(da,8,da,8)[:,4*i:4*i+4,:,4*i:4*i+4].reshape(da,2,2,da,2,2)
    W=np.einsum('aiocjo->aicj',sub)*F(1,2)
    W=np.einsum('aicj,op->aiocjp',W,eye).reshape(da*4,da*4);db=4
   assert W.shape==(sizes[ai]*sizes[bi],)*2
   blocks[ai,bi]=W
 total=4*sum(np.trace(W) for W in blocks.values());assert total==64
 # Exact all-charge full normalization by existing INTEGER projector, used only as a secondary checker.
 import sys
 sys.path.insert(0,str(ROOT/'physical-process'))
 from check_exact_lift import lift_num, full_p0_num, full_trace, ChargeModel
 from certify_reduced_process import p0_num
 nums=np.repeat(Znum[None],4,axis=0)
 # p0_num is the traceless projector multiplied by its documented scale; use its source implementation convention.
 lifted=lift_num(nums,2)
 for key,W in blocks.items():
  # lift_num applies both /2 operations through one common factor 4.
  assert np.array_equal(lifted[key][0],W*192)
 model=ChargeModel(2)
 fullP=full_p0_num(model,lifted);assert full_trace(lifted)==64*192
 for key in model.keys:
  assert np.array_equal(fullP[key],1024*lifted[key]-64*192*np.eye(lifted[key].shape[-1],dtype=object)[None])
 score=F(0)
 for a in [0,1]:
  for b in [0,1]:
   k=np.zeros(n*n,dtype=object)
   for aa in [0,1]:
    for bb in [0,1]:k[(ws.index((a,)) if aa else 0)*n+(ws.index((b,)) if bb else 0)]=F((-1)**(aa*b+bb*a),8)
   score+=k@qq@k
 return {'word_level':L,'word_count':n,'positive_tester_flag_blocks':4,'exact_NS_dual_affine_identity':True,'local_annihilator_nullity_per_party':1,'scalar_flatness_defect':str(defect),'exact_coherent_reconstruction':True,'physical_charge_pairs_checked':len(blocks),'physical_flag_charge_blocks_checked':4*len(blocks),'full_physical_affine_projector_exact':True,'physical_trace':str(total),'GYNI_score':str(score),'PSD_proof':'Explicit Z=(I+H)(I+H)^T/48 with H^2=2I; every peripheral block is its CP output-repair image.'}

def main():
 cases=[('one_endpoint_plus',[(0,1)]),('one_endpoint_minus',[(1,0)]),('one_interior',[(3,4)]),('one_interior_plus',[(3,4),(0,1)]),('one_interior_minus',[(3,4),(1,0)]),('one_interior_both',[(3,4),(0,1),(1,0)]),('two_interiors',[(8,15),(15,8)])]
 rows=[structural_case(label,pairs) for label,pairs in cases]
 six=json.loads((ROOT/'objective/endpoint_lower1653.json').read_text())['rational_tangent_pairs']
 rows.append(structural_case('certified_six_angle_support',six,(0,)))
 result={'status':'PASS_EXACT','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'used_floating_arithmetic':False,'modular_rank_prime':PRIME,'modular_rank_scope':'Nonzero minors modulo prime certify lower ranks over Q; exact vanishing and dimensions certify upper ranks.','structural_cases':rows,'physical_realization_test':physical_test(),'scope':'Conditional realization criterion and exact algebra/physical tests. No matching optimum or angle cutoff.'}
 (OUT/'exact_tests.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='structural_cases'},indent=2));print('structural cases',len(rows))
if __name__=='__main__':main()
