"""Optimized FINAL recovery, plus a constructive ordinary intermediate decoder.
No optimization over all adaptive interventions or encodings is claimed.
"""
import json,numpy as np
from core import *
from nonpauli_qec import product_noise,code_dual,compress,petz
from decoder_opt import solve

def clean_result(r):return {k:v for k,v in r.items() if k!='decoder'}

def evaluate(A,B,V):
 AB=[b@a@V for a in A for b in B];BA=[a@b@V for a in A for b in B]
 sab=solve(AB,tol=2e-6);sba=solve(BA,tol=2e-6)
 sp=solve([(a+b)/2 for a,b in zip(AB,BA)],tol=1e-6)
 sm=solve([(a-b)/2 for a,b in zip(AB,BA)],tol=1e-6)
 sj=solve([np.vstack([a,b])/np.sqrt(2) for a,b in zip(AB,BA)],tol=2e-6)
 def mid(A,B):
  s1=solve([a@V for a in A],tol=2e-6)
  logical=compress([r@a@V for r in s1['decoder'] for a in A])
  return solve([b@V@l for b in B for l in logical],tol=2e-6)['lower']
 m=max(mid(A,B),mid(B,A))
 return {'serial_AB':clean_result(sab),'serial_BA':clean_result(sba),'switch_flagged_lower':sp['lower']+sm['lower'],
 'switch_flagged_upper':sp['upper']+sm['upper'],'switch_coherent':clean_result(sj),'ordinary_intermediate_achieved':m}

def main():
 rows=[];V=code_dual();H=(X+Z)/np.sqrt(2)
 for g in [.01,.1,.3,.6]:
  for label,a,b in [('cool_heat',amplitude(g),amplitude(g,True)),('orthogonal_cool',amplitude(g),[H@k@H for k in amplitude(g)])]:
   ans=evaluate(product_noise(a,2),product_noise(b,2),V);r={'g':g,'family':label,**ans};rows.append(r)
   print(r,flush=True);open('decoder_optimized_results.json','w').write(json.dumps(rows,indent=2))
 # A noiseless subsystem for any collective SU(2) Lindblad noise on 3 qubits.
 W=np.zeros((8,4),complex)
 W[2,0]=1/np.sqrt(2);W[4,0]=-1/np.sqrt(2)
 W[3,1]=1/np.sqrt(2);W[5,1]=-1/np.sqrt(2)
 W[2,2]=W[4,2]=1/np.sqrt(6);W[1,2]=-2/np.sqrt(6)
 W[6,3]=2/np.sqrt(6);W[3,3]=W[5,3]=-1/np.sqrt(6)
 low=np.array([[0,1],[0,0]],complex);J=sum(kron_all([low if j==k else I2 for k in range(3)]) for j in range(3))
 assert np.linalg.norm(J@W-W@np.kron(I2,low))<1e-12
 assert np.linalg.norm(J.conj().T@W-W@np.kron(I2,low.conj().T))<1e-12
 V=W[:,[0,2]];decoder=[np.kron(I2,np.eye(2)[g:g+1])@W.conj().T for g in [0,1]]
 checks=[]
 for t in [.02,.2,1,3]:
  A=lindblad_channel(np.zeros((8,8)),[J],t);B=lindblad_channel(np.zeros((8,8)),[J.conj().T],t)
  L=[r@b@a@V for r in decoder for a in A for b in B]
  fe=sum(abs(np.trace(l))**2 for l in L)/4
  checks.append({'time':t,'logical_infidelity':float(1-fe)})
  assert abs(fe-1)<1e-11
 open('collective_dfs.json','w').write(json.dumps({'basis':W.real.tolist(),'checks':checks},indent=2))
 print('DFS PASS',checks,flush=True)
if __name__=='__main__':main()
