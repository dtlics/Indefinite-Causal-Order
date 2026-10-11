"""Exact upper bound for one fixed angle set in the audited reduced process cone."""
import argparse,gzip,json,math,sys,time
from fractions import Fraction as F
from pathlib import Path
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'physical-process'))
from certify_reduced_process import p0_num,norm_bound,objective_num

def replay(p):
 st=time.time();K=p['K'];bits=p['bits'];D=64*K*K;sd=1<<bits;gd=sd*sd;G,gden=objective_num(p['pairs']);L=np.array(p['factors'],dtype=object);den=math.lcm(gden,gd);H=G*(den//gden)+(L@L.transpose(0,2,1))*(den//gd);E=p0_num(H,K);err=norm_bound(E);Y=D*H-E+err*np.eye(16*K*K,dtype=object)[None];yd=D*den
 assert np.array_equal(p0_num(Y,K),np.zeros_like(Y));assert np.array_equal(Y,Y.transpose(0,2,1));tr=sum(int(Y[f,i,i]) for f in range(4) for i in range(16*K*K));upper=F(tr,4*K*K*yd)
 return {'status':'VERIFIED_EXACT_FIXED_ANGLE_UPPER','K':K,'rational_tangent_pairs':p['pairs'],'upper_rational':str(upper),'upper_decimal':float(upper),'repair_cost':str(F(16*err,yd)),'repair_cost_decimal':float(F(16*err,yd)),'floating_arithmetic_in_verification':False,'seconds':time.time()-st,'scope':'Upper bound ONLY for the specified fixed projective instruments in every valid process at these ports. Not an unrestricted upper bound.'}

def main():
 a=argparse.ArgumentParser();a.add_argument('--input');a.add_argument('--stem');a.add_argument('--bits',type=int,default=46);a.add_argument('--verify');q=a.parse_args()
 if q.verify:
  p=json.load(gzip.open(q.verify,'rt'));o=replay(p);print(json.dumps(o,indent=2));return
 from outcome_reduced import OutcomeReduced
 data=np.load(q.input);angles=data['angles'];K=len(angles);r=OutcomeReduced(K);FF=r.expand(data['F'],angles);pairs=[]
 for t in angles:
  f=F(float(np.tan(t))).limit_denominator(10**8);pairs.append([f.numerator,f.denominator])
 G,gden=objective_num(pairs);Gf=np.asarray(G,dtype=float)/gden;fac=[]
 for f in range(4):
  S=(FF[f]-Gf[f]);ev,V=np.linalg.eigh((S+S.T)/2);root=V*np.sqrt(np.maximum(ev,0))[None,:];fac.append(np.rint(root*(1<<q.bits)).astype(np.int64).tolist())
 p={'K':K,'bits':q.bits,'pairs':pairs,'factors':fac};o=replay(p)
 with gzip.open(q.stem+'_factors.json.gz','wt') as fp:json.dump(p,fp)
 Path(q.stem+'.json').write_text(json.dumps(o,indent=2)+'\n');print(json.dumps(o,indent=2))
if __name__=='__main__':main()
