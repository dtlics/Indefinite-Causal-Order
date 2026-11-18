"""Noise-adapted Petz recovery benchmarks, not optimal-decoder claims.
All outcome fidelities are subnormalized and summed; no rejected runs.
"""
from __future__ import annotations
import itertools,json,time
import numpy as np
from core import *

def compress(Ks, tol=2e-13):
 shape=Ks[0].shape;M=np.column_stack([vec(k) for k in Ks]);J=M@M.conj().T
 vals,V=np.linalg.eigh((J+J.conj().T)/2)
 return [np.sqrt(v)*V[:,i].reshape(shape,order='F') for i,v in enumerate(vals) if v>tol]

def invsqrt(A):
 w,V=np.linalg.eigh((A+A.conj().T)/2);a=np.zeros_like(w);a[w>1e-12]=w[w>1e-12]**(-.5)
 return (V*a)@V.conj().T

def petz(L):
 L=compress(L)
 if not L:return [],[],0.
 S=sum((l@l.conj().T for l in L),np.zeros((L[0].shape[0],)*2,complex));Q=invsqrt(S)
 R=[l.conj().T@Q for l in L];D=L[0].shape[1]
 C=np.array([[np.trace(r@l) for l in L] for r in R]);Fe=float(np.sum(abs(C)**2)/D**2)
 return R,L,Fe

def product_noise(K,n):return [kron_all(x) for x in itertools.product(K,repeat=n)]

def code_ad4():
 V=np.zeros((16,2),complex);V[0,0]=V[15,0]=1/np.sqrt(2);V[3,1]=V[12,1]=1/np.sqrt(2);return V

def code_dual():
 V=np.zeros((4,2),complex);V[1,0]=1;V[2,1]=1;return V

def code_rep3():
 V=np.zeros((8,2),complex);V[0,0]=1;V[7,1]=1;return V

def evaluate(A,B,V):
 AB=[b@a@V for a in A for b in B];BA=[a@b@V for a in A for b in B]
 fAB=petz(AB)[2];fBA=petz(BA)[2]
 plus=[(a+b)/2 for a,b in zip(AB,BA)];minus=[(a-b)/2 for a,b in zip(AB,BA)]
 fplus=petz(plus)[2];fminus=petz(minus)[2]
 joint=[np.vstack([a,b])/np.sqrt(2) for a,b in zip(AB,BA)];fj=petz(joint)[2]
 def intermediate(A,B):
  RA,LA,fa=petz([a@V for a in A]);logical=compress([r@a for r in RA for a in LA])
  return petz([b@V@l for b in B for l in logical])[2]
 fmid=max(intermediate(A,B),intermediate(B,A));eff=effect(minus);ev=np.linalg.eigvalsh(eff)
 out={'serial_petz':max(fAB,fBA),'serial_AB':fAB,'serial_BA':fBA,'flagged_petz':fplus+fminus,
   'coherent_petz':fj,'intermediate_petz':fmid,'p_minus_Bell':float(np.trace(eff).real/2),
   'p_minus_min':float(ev[0]),'p_minus_max':float(ev[-1])}
 assert all(-1e-8<=out[k]<=1+1e-8 for k in ['serial_petz','flagged_petz','coherent_petz','intermediate_petz'])
 return out

def main():
 out=[];H=(X+Z)/np.sqrt(2)
 for name,V in [('AD4',code_ad4()),('dualrail2',code_dual()),('rep3',code_rep3())]:
  n=int(np.log2(V.shape[0]))
  for strength in [.01,.1,.3,.6]:
   K=amplitude(strength)
   models={'same_cooling':(K,K),'cooling_heating':(K,amplitude(strength,True)),
    'orthogonal_cooling':(K,[H@k@H for k in K]),'thermal_opposed':(thermal(strength,.15),thermal(strength,.85))}
   for label,(a,b) in models.items():
    res=evaluate(product_noise(a,n),product_noise(b,n),V)
    row={'code':name,'family':label,'strength':strength,**res};out.append(row)
    print(name,label,strength,res,flush=True);open('nonpauli_qec_results.json','w').write(json.dumps(out,indent=2))
 n=3;V=code_rep3();d=8;low=np.array([[0,1],[0,0]],complex)
 lowers=[kron_all([low if j==k else I2 for k in range(n)]) for j in range(n)]
 J=sum(lowers);Jphase=sum(np.exp(2j*np.pi*j/n)*l for j,l in enumerate(lowers))
 for t in [.02,.2,1]:
  for label,L1,L2 in [('collective_cool_heat',[J],[J.conj().T]),('collective_phase',[J],[Jphase]),('collective_vs_individual',[J],lowers)]:
   A=lindblad_channel(np.zeros((d,d)),L1,t);B=lindblad_channel(np.zeros((d,d)),L2,t)
   row={'code':'rep3','family':label,'strength':t,**evaluate(A,B,V)};out.append(row)
   print(label,t,row,flush=True);open('nonpauli_qec_results.json','w').write(json.dumps(out,indent=2))
 print('DONE',len(out))
if __name__=='__main__':main()
