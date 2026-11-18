"""Finite-dimensional oscillator-surrogate QEC screening; not an infinite-energy CV theorem."""
import json
import numpy as np
from core import lindblad_channel
from nonpauli_qec import evaluate

def main():
 d=12
 a=np.diag(np.sqrt(np.arange(1,d)),1).astype(complex);N=a.conj().T@a
 V=np.zeros((d,2),complex);V[0,0]=V[6,0]=1/np.sqrt(2);V[3,1]=1
 out=[]
 for t in [.001,.01,.05,.1]:
  A=lindblad_channel(np.zeros((d,d)),[a],t)
  for name,L in [('loss_loss',[a]),('loss_gain',[a.conj().T]),('loss_number_dephasing',[.5*N])]:
   B=A if name=='loss_loss' else lindblad_channel(np.zeros((d,d)),L,t)
   row={'dimension':d,'time':t,'family':name,**evaluate(A,B,V)}
   out.append(row);print(row,flush=True)
   open('bosonic_results.json','w').write(json.dumps(out,indent=2))
 print('DONE',len(out))
if __name__=='__main__':main()
