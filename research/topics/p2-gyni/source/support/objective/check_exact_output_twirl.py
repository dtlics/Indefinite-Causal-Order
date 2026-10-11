"""Integer verification of output-twirl/reduced-projector/full-charge-lift commutation."""
import json,sys,math
from pathlib import Path
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'physical-process'))
from certify_reduced_process import p0_num
from check_exact_lift import lift_num
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'foundations'))
from charged_grid_admm import ChargeModel

def reflection_data(K):
 pairs=[(0,1),(3,4),(5,12)][:K];D=math.lcm(*[p*p+q*q for p,q in pairs]);R=[]
 for x in [0,1]:
  r=[]
  for p,q in pairs:
   r.append(np.array([[D,0],[0,-D]],dtype=object) if x==0 else (D//(p*p+q*q))*np.array([[q*q-p*p,2*p*q],[2*p*q,p*p-q*q]],dtype=object))
  R.append(r)
 return D,R

def local(m,charge,R,x):
 d=m.sizes[charge];U=np.zeros((d,d),dtype=object)
 for i,j,start in m.groups[charge]:
  for inp in [0,1]:U[start+2*inp:start+2*inp+2,start+2*inp:start+2*inp+2]=R[x][j]
 return U

def conj_sparse(W,U):
 out=np.empty_like(W)
 for i,row in enumerate(U):
  nz=[(j,int(v)) for j,v in enumerate(row) if v]
  out[i]=sum(v*W[j] for j,v in nz)
 tmp=out.T;out2=np.empty_like(tmp)
 for i,row in enumerate(U):
  nz=[(j,int(v)) for j,v in enumerate(row) if v]
  out2[i]=sum(v*tmp[j] for j,v in nz)
 return out2.T

def twirl_one(Z,Ua,Ub,D):
 nA,nB=len(Ua),len(Ub);A=np.kron(Ua,np.eye(nB,dtype=object));B=np.kron(np.eye(nA,dtype=object),Ub)
 X=D*D*Z+conj_sparse(Z,A)
 return D*D*X+conj_sparse(X,B)

def twirl_blocks(W,m,R,D):
 out={}
 for a,b in m.keys:
  out[a,b]=np.empty_like(W[a,b])
  for x in [0,1]:
   for y in [0,1]:out[a,b][2*x+y]=twirl_one(W[a,b][2*x+y],local(m,a,R,x),local(m,b,R,y),D)
 return out
rng=np.random.default_rng(72901);rows=[]
for K in [1,2,3]:
 m=ChargeModel(K);D,R=reflection_data(K);n=4*K;seed=rng.integers(-3,4,size=(4,n*n,n*n)).astype(object);seed+=seed.transpose(0,2,1)
 Z=p0_num(seed,K)+16*np.eye(n*n,dtype=object)[None];ZD=np.empty_like(Z)
 for x in [0,1]:
  for y in [0,1]:ZD[2*x+y]=twirl_one(Z[2*x+y],local(m,0,R,x),local(m,0,R,y),D)
 # This checks the trace-zero reduced affine projector; twirl also fixes identity.
 P=p0_num(Z,K);PD=np.empty_like(P)
 for x in [0,1]:
  for y in [0,1]:PD[2*x+y]=twirl_one(P[2*x+y],local(m,0,R,x),local(m,0,R,y),D)
 assert np.array_equal(p0_num(ZD,K),PD)
 left=lift_num(ZD,K);right=twirl_blocks(lift_num(Z,K),m,R,D)
 assert all(np.array_equal(left[key],right[key]) for key in m.keys)
 scale=4*D**4
 assert sum(np.trace(v) for v in ZD)==scale*sum(np.trace(v) for v in Z)
 fixed=0
 for x in [0,1]:
  for a in [0,1]:
   for j in range(K):
    P=D*np.eye(2,dtype=object)+(-1)**a*R[x][j]
    assert np.array_equal(R[x][j]@P,(-1)**a*D*P);fixed+=1
 rows.append({'K':K,'charge_pairs':len(m.keys),'full_flag_blocks':4*len(m.keys),'projector_commutation_exact':True,'CP_lift_commutation_exact':True,'trace_preservation_exact':True,'winning_Kraus_eigenidentities':fixed,'off_angle_blocks_retained':True})
out={'status':'PASSED_EXACT_INTEGER','floating_arithmetic_used':False,'cases':rows};Path(__file__).with_name('exact_output_twirl_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
