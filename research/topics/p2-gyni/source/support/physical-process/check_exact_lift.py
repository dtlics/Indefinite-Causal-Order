"""Cross-check reduced integer affine identities against full charged ones."""
import json,sys
from pathlib import Path
import numpy as np
from reduced_process import ReducedProcess,ROOT
from certify_reduced_process import p0_num
sys.path.insert(0,str(ROOT))
from charged_grid_admm import ChargeModel
from certify_charged_grid import p0_num as full_p0_num,trace as full_trace

def lift_num(W,K):
 m=ChargeModel(K);n=4*K;out=m.zeros(object);out[0,0]=4*W
 def addA(out,bs):
  for i in range(K):
   for b in bs:
    db=m.sizes[b];z=out[0,b].reshape(4,n,db,n,db)[:,4*i:4*i+4,:,4*i:4*i+4,:].reshape(4,2,2,db,2,2,db)
    t=sum(z[:,:,o,:,:,o,:] for o in range(2));assert all(int(x)%2==0 for x in t.ravel());t=t//2
    emb=np.zeros((4,2,2,db,2,2,db),dtype=object)
    for o in range(2):emb[:,:,o,:,:,o,:]=t
    for j in range(K):
     if i!=j:out[m.sectors.index((i,j)),b]=emb.reshape(4,4*db,4*db).copy()
  return out
 out=addA(out,[0]);out=m.swap(addA(m.swap(out),range(len(m.sectors))))
 return out

def test():
 rng=np.random.default_rng(33490);checks=[]
 for K in [1,2,3]:
  r=ReducedProcess(K);m=ChargeModel(K);seed=rng.integers(-20,21,size=(4,r.N,r.N)).astype(object);seed=seed+seed.transpose(0,2,1)
  D=64*K*K;Z=p0_num(seed,K)+16*np.eye(r.N,dtype=object)[None];W=lift_num(Z,K);wd=4*D
  assert np.array_equal(W[0,0],4*Z);assert full_trace(W)==16*K*K*wd
  P=full_p0_num(m,W);Df=64*K**4
  for key in m.keys:
   expected=Df*W[key]-16*K*K*wd*np.eye(W[key].shape[-1],dtype=object)[None]
   assert np.array_equal(P[key],expected),(K,key)
  checks.append({'K':K,'integer_full_affine_equations':True,'integer_full_normalization':True,'zero_zero_right_inverse':True,'physical_charge_blocks':len(m.keys),'flag_blocks':4*len(m.keys)})
 out={'status':'PASS_EXACT_INTEGER_LIFT_TESTS','cases':checks,'floating_arithmetic':False};Path(__file__).with_name('exact_lift_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':test()
