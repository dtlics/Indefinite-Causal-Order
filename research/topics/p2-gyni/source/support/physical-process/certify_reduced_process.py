"""Integer-only replay for a reduced process, with exact rational CP physical lift."""
import argparse,gzip,json,math,time
from pathlib import Path
from fractions import Fraction as F
import numpy as np
from reduced_process import ReducedProcess

def RA_num(W,K):
 n=4*K;z=W.reshape(2,2,n,n,n,n);out=np.zeros_like(z)
 for j in range(K):
  s=slice(4*j,4*j+4);v=z[:,:,s,:,s,:].reshape(2,2,2,2,n,2,2,n)
  # np.einsum does not implement object arrays.
  t=sum(v[x,:,:,o,:,:,o,:] for x in range(2) for o in range(2))
  e=np.zeros((2,2,2,n,2,2,n),dtype=object)
  for o in range(2):e[:,:,o,:,:,o,:]=t
  out[:,:,s,:,s,:]=e.reshape(1,2,4,n,4,n)
 return out.reshape(W.shape)
def DA_num(W,K):
 n=4*K;z=W.reshape(2,2,n,n,n,n);t=sum(z[x,:,a,:,a,:] for x in range(2) for a in range(n));out=np.zeros_like(z)
 for a in range(n):out[:,:,a,:,a,:]=t[None]
 return out.reshape(W.shape)
def swap(W,K):
 n=4*K;return W.reshape(2,2,n,n,n,n).transpose(1,0,3,2,5,4).reshape(W.shape)
def p0_num(W,K):
 D=64*K*K;A=RA_num(W,K);B=swap(RA_num(swap(W,K),K),K);AB=RA_num(B,K);DA=DA_num(W,K);DB=swap(DA_num(swap(W,K),K),K)
 v=D//4*(A+B)-D//16*AB-D//(8*K)*(DA+DB)+D//(32*K)*(DA_num(B,K)+swap(DA_num(swap(A,K),K),K))
 tr=sum(int(W[f,i,i]) for f in range(4) for i in range(16*K*K))
 return v-tr*np.eye(16*K*K,dtype=object)[None]
def norm_bound(E):
 out=0
 for e in E:
  n2=int(np.sum(e*e));fr=math.isqrt(n2)+(math.isqrt(n2)**2<n2);rows=max(map(int,np.sum(np.abs(e),axis=1)));out=max(out,min(fr,rows))
 return out

def objective_num(pairs):
 K=len(pairs);d=math.lcm(*[int(p*p+q*q) for p,q in pairs]);I=np.tile(np.array([d,0,0,d],dtype=object),K);P0=np.tile(np.array([d,0,0,0],dtype=object),K)
 P1=np.concatenate([np.array([q*q,p*q,p*q,p*p],dtype=object)*(d//(p*p+q*q)) for p,q in pairs]);P=[[P0,I-P0],[P1,I-P1]]
 G=[]
 for x in range(2):
  for y in range(2):v=np.kron(P[x][y],P[y][x]);G.append(np.outer(v,v))
 return np.array(G,dtype=object),4*d**4

def reconstruct(p):
 K=p['K'];D=64*K*K;sd=1<<p['bits'];shift=F(p['shift']);seed=np.array(p['seed'],dtype=object);L=np.array(p['factors'],dtype=object);eye=np.eye(16*K*K,dtype=object)[None]
 Znum=p0_num(seed,K)+16*sd*eye;den=math.lcm(D*sd,sd*sd,shift.denominator);Z=Znum*(den//(D*sd));s=shift.numerator*(den//shift.denominator)
 Gram=(L@L.transpose(0,2,1))*(den//(sd*sd));E=Z+s*eye-Gram;err=norm_bound(E);W=Z+(s+err)*eye;wd=den+4*K*K*(s+err)
 assert np.array_equal(W,W.transpose(0,2,1));assert sum(int(W[f,i,i]) for f in range(4) for i in range(16*K*K))==16*wd
 assert np.array_equal(p0_num(W,K),D*W-16*wd*eye)
 G,gd=objective_num(p['pairs']);lower=F(int(np.sum(G*W)),gd*wd)
 return {'lower':lower,'repair':F(err,den),'denominator':wd}

def create(a):
 start=time.time();q=np.load(a.input);angles=q['angles'];K=len(angles);r=ReducedProcess(K);seedfloat=q['Z'] if 'Z' in q else q['Z_0_0'];bits=a.bits;sd=1<<bits;seed=np.rint(seedfloat*sd).astype(np.int64).astype(object);Znum=p0_num(seed,K)+16*sd*np.eye(r.N,dtype=object)[None];Z=np.array(Znum,dtype=float)/(64*K*K*sd)
 shift=F(a.shift) if a.shift else F(max(1,math.ceil(-float(np.linalg.eigvalsh(Z).min())*10**12)+100),10**12)
 factors=np.rint(np.linalg.cholesky(Z+float(shift)*np.eye(r.N)[None])*sd).astype(np.int64).astype(object)
 pairs=json.load(open(a.pairs)) if a.pairs else [[F(float(np.tan(t))).limit_denominator(10**8).numerator,F(float(np.tan(t))).limit_denominator(10**8).denominator] if abs(t-np.pi/2)>1e-10 else [1,0] for t in angles]
 p={'K':K,'bits':bits,'shift':str(shift),'pairs':pairs,'seed':seed.tolist(),'factors':factors.tolist()};result=reconstruct(p)
 out={'status':'EXACT_REDUCED_PROCESS_LOWER_CERTIFICATE','K':K,'input_dimension':2*K,'output_dimension':4*K,'bits':bits,'initial_shift':str(shift),'residual_operator_bound':str(result['repair']),'rational_tangent_pairs':pairs,'GYNI_lower_rational':str(result['lower']),'GYNI_lower_decimal':float(result['lower']),'process_denominator':str(result['denominator']),'seconds':time.time()-start,'scope':'Exact positive reduced process with exact rational output-repair lift to all physical output charge sectors. Requires the reduced-process lift theorem; no optimality claim.'}
 Path(a.output+'.json').write_text(json.dumps(out,indent=2)+'\n')
 with gzip.open(a.output+'_data.json.gz','wt') as f:json.dump(p,f)
 print(json.dumps(out,indent=2))
def verify(a):
 start=time.time();claim=json.load(open(a.input))
 with gzip.open(a.output,'rt') as f:p=json.load(f)
 out=reconstruct(p);assert out['lower']==F(claim['GYNI_lower_rational']);res={'status':'VERIFIED_EXACT_REDUCED_PROCESS','lower_rational':str(out['lower']),'lower_decimal':float(out['lower']),'used_floating_arithmetic_for_certificate':False,'seconds':time.time()-start};Path(a.input).with_name(Path(a.input).stem+'_verification.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('input');p.add_argument('output');p.add_argument('--verify',action='store_true');p.add_argument('--bits',type=int,default=38);p.add_argument('--shift');p.add_argument('--pairs');a=p.parse_args();verify(a) if a.verify else create(a)
