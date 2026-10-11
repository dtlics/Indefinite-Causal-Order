#!/usr/bin/env python3
"""Independent finite checks of the analytical ancilla-uniform proof, not its substitute."""
from pathlib import Path
from functools import reduce
import json
import numpy as np
import sympy as sp
rng=np.random.default_rng(20261001)
kron=lambda *x:reduce(np.kron,x)
I=np.eye(2);X=np.array([[0,1],[1,0.]]);Z=np.diag([1.,-1.]);A=kron(Z,Z,Z,I);B=kron(X,I,Z,Z)
t=.6;V=(np.eye(16)+t*(A+B))/4;O=np.eye(16)/4

def instrument(di,na):
 kr=max(3,(di+2*na-1)//(2*na))
 U=rng.normal(size=(2*na*kr,di))+1j*rng.normal(size=(2*na*kr,di));U=np.linalg.qr(U)[0]
 out=[]
 for a in range(na):
  vec=U.reshape(na,kr,2,di)[a].transpose(0,2,1).reshape(kr,di*2).conj()
  out.append(vec.T@vec.conj())
 return np.array(out)
def phi(M,T,d):
 return np.einsum('ikjl,jalibk->ab',T.reshape(2,2,2,2),M.reshape(2,d,2,2,d,2))/2

def resource(W,rho,da,db):
 R=np.kron(W,rho).reshape(2,2,2,2,da,db,2,2,2,2,da,db)
 pp=[0,4,1,2,5,3];return R.transpose(pp+[i+6 for i in pp]).reshape(16*da*db,16*da*db)
def flag_resource(W,rho,da,db):
 # W input order FA,AI,AO,FB,BI,BO; rho RA,RB.
 R=np.kron(W,rho).reshape(2,2,2,2,2,2,da,db,2,2,2,2,2,2,da,db)
 pp=[0,1,6,2,3,4,7,5];return R.transpose(pp+[i+8 for i in pp]).reshape(64*da*db,64*da*db)
def wfmatrix():
 W=np.zeros((64,64))
 for f in range(2):
  for g in range(2):
   P=np.zeros((4,4));P[2*f+g,2*f+g]=1
   T=np.kron(P,V if f*g else O).reshape([2]*12)
   pp=[0,2,3,1,4,5];W+=T.transpose(pp+[i+6 for i in pp]).reshape(64,64)/4
 return W
Wflag=wfmatrix();eye4=np.eye(4)
stats={'max_direct_contraction_error':0.,'max_flag_coherence_refinement_error':0.,'max_directed_formula_error':0.,'minimum_operator_direction_slack':1.,'minimum_rectangle_slack':1.,'minimum_graph_slack':1.,'maximum_graph_bound_residual':-1.,'cases':0}
for da,db in [(1,1),(2,2),(2,3),(3,2)]:
 for trial in range(8):
  D=da*db;T=rng.normal(size=(D,D))+1j*rng.normal(size=(D,D));rho=T@T.conj().T;rho/=np.trace(rho)
  # Genuine flag-coherent instruments, not instruments assumed diagonal at creation.
  MA=instrument(4*da,3);NB=instrument(4*db,3)
  m=[[M.reshape(2,2,da,2,2,2,da,2)[f,:,:,:,f,:,:,:].reshape(4*da,4*da) for M in MA] for f in range(2)]
  n=[[N.reshape(2,2,db,2,2,2,db,2)[g,:,:,:,g,:,:,:].reshape(4*db,4*db) for N in NB] for g in range(2)]
  RV=resource(V,rho,da,db);RQ=resource(O,rho,da,db);RW=flag_resource(Wflag,rho,da,db)
  for a,b in [(0,0),(1,2)]:
   full=np.trace(RW@np.kron(MA[a],NB[b])).real
   refined=sum(np.trace((RV if f*g else RQ)@np.kron(m[f][a],n[g][b])).real/4 for f in range(2) for g in range(2))
   stats['max_flag_coherence_refinement_error']=max(stats['max_flag_coherence_refinement_error'],abs(full-refined))
  for case in range(100):
   MM=[sum((m[f][a] for a in range(3) if rng.integers(2)),np.zeros((4*da,4*da),complex)) for f in range(2)]
   NN=[sum((n[g][b] for b in range(3) if rng.integers(2)),np.zeros((4*db,4*db),complex)) for g in range(2)]
   EE=[phi(M,eye4,da) for M in MM];FF=[phi(N,eye4,db) for N in NN]
   aa=np.array([np.trace(rho@np.kron(E,np.eye(db))).real for E in EE]);bb=np.array([np.trace(rho@np.kron(np.eye(da),F)).real for F in FF])
   q=np.array([[np.trace(rho@np.kron(E,F)).real for F in FF] for E in EE]);mis=aa[:,None]+bb[None,:]-2*q
   p=np.trace(RV@np.kron(MM[1],NN[1])).real
   LA=phi(MM[1],kron(Z,Z),da);RA=phi(MM[1],kron(X,I),da);RB=phi(NN[1],kron(Z,I),db);LB=phi(NN[1],kron(Z,Z),db)
   Delta=t*(np.kron(LA,RB)+np.kron(RA,LB));dform=np.trace(rho@Delta).real
   stats['max_directed_formula_error']=max(stats['max_directed_formula_error'],abs(p-q[1,1]-dform))
   directq=np.trace(RQ@np.kron(MM[1],NN[1])).real
   stats['max_direct_contraction_error']=max(stats['max_direct_contraction_error'],abs(directq-q[1,1]))
   G=t*(np.kron(EE[1],np.eye(db)-FF[1])+np.kron(np.eye(da)-EE[1],FF[1]))-Delta
   stats['minimum_operator_direction_slack']=min(stats['minimum_operator_direction_slack'],np.linalg.eigvalsh((G+G.conj().T)/2)[0])
   Dwhite=.5*mis.sum();rect=Dwhite-(p-q[1,1]);graph=Dwhite-(2/3)*mis[1,1]
   stats['minimum_rectangle_slack']=min(stats['minimum_rectangle_slack'],rect)
   stats['minimum_graph_slack']=min(stats['minimum_graph_slack'],graph)
   stats['maximum_graph_bound_residual']=max(stats['maximum_graph_bound_residual'],mis[1,1]-3*(mis.sum()-mis[1,1]))
   stats['cases']+=1
# Exact seed and witness algebra.
Is=sp.eye(2);Xs=sp.Matrix([[0,1],[1,0]]);Zs=sp.diag(1,-1)
As=sp.kronecker_product(Zs,Zs,Zs,Is);Bs=sp.kronecker_product(Xs,Is,Zs,Zs)
Vs=(sp.eye(16)+sp.Rational(3,5)*(As+Bs))/4;Ss=sp.eye(16)-As-Bs
exact={'anticommutator_zero':As*Bs+Bs*As==sp.zeros(16),'pauli_squares_identity':As**2==sp.eye(16) and Bs**2==sp.eye(16),'seed_trace':str(sp.trace(Vs)),'flagged_witness_value':str(sp.trace(Vs*Ss)/4),'t':'3/5','causal_bridge_margin':'2/3 - 3/5 = 1/15','flagged_dimensions':[4,2,4,2],'flagged_spectrum':{'(5 - 3*sqrt(2))/80':8,'(5 + 3*sqrt(2))/80':8,'1/16':48},'ancilla_dimensions_checked':[[1,1],[2,2],[2,3],[3,2]],'role':'Finite algebra and contraction checks supplement the dimension-uniform analytical theorem'}
out={'numerical_checks':stats,'exact_checks':exact}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
