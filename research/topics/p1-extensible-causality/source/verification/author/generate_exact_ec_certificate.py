#!/usr/bin/env python3
"""Generate/check the rational 64x64 EC example using only Python's standard library."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
DIMS=(4,2,4,2)
TUPLES=list(product(*(range(d) for d in DIMS)))
INDEX={t:i for i,t in enumerate(TUPLES)}
N=[[0]*64 for _ in range(64)];S=[[0]*64 for _ in range(64)];P=[[0]*64 for _ in range(64)]
AA=[[0]*64 for _ in range(64)];BB=[[0]*64 for _ in range(64)]
for j in range(64):
 fa,ai,ao,fb,bi,bo=[(j>>k)&1 for k in range(5,-1,-1)]
 flag=fa*fb;a=(-1)**(ai+ao+bi);b=(-1)**(bi+bo)
 N[j][j]=5+3*flag*a;N[j^16][j]+=3*flag*b
 S[j][j]=flag*(1-a);S[j^16][j]-=flag*b
 P[j][j]=flag;AA[j][j]=flag*a;BB[j^16][j]=flag*b

def replace(M,factors):
 factors=tuple(factors);den=1
 for k in factors:den*=DIMS[k]
 out=[[F(0) for _ in range(64)] for _ in range(64)]
 for i,ii in enumerate(TUPLES):
  for j,jj in enumerate(TUPLES):
   if any(ii[k]!=jj[k] for k in factors):continue
   v=0
   for kk in product(*(range(DIMS[k]) for k in factors)):
    ri=list(ii);cj=list(jj)
    for k,x in zip(factors,kk):ri[k]=x;cj[k]=x
    v+=M[INDEX[tuple(ri)]][INDEX[tuple(cj)]]
   out[i][j]=F(v,den)
 return out

def same(A,B):return all(A[i][j]==B[i][j] for i in range(64) for j in range(64))
def matmul(A,B):return [[sum(A[i][k]*B[k][j] for k in range(64) if A[i][k] and B[k][j]) for j in range(64)] for i in range(64)]
def add(A,B,s=1):return [[A[i][j]+s*B[i][j] for j in range(64)] for i in range(64)]
checks={}
checks['normalization']=sum(N[i][i] for i in range(64))==320
checks['symmetric_rational_matrix']=same(N,list(map(list,zip(*N))))
checks['constraint_BIBO_AOBIBO']=same(replace(N,(2,3)),replace(N,(1,2,3)))
checks['constraint_AIAO_AIAOBO']=same(replace(N,(0,1)),replace(N,(0,1,3)))
checks['no_two_output_terms']=same(N,add(add(replace(N,(1,)),replace(N,(3,))),replace(N,(1,3)),-1))
checks['input_baseline']=same(replace(N,(1,3)),[[5*int(i==j) for j in range(64)] for i in range(64)])
checks['flagged_pauli_squares']=same(matmul(AA,AA),P) and same(matmul(BB,BB),P)
checks['flagged_pauli_anticommutator']=same(add(matmul(AA,BB),matmul(BB,AA)),[[0]*64 for _ in range(64)])
checks['witness_AO_reduction']=same(replace(S,(1,)),add(P,BB,-1))
checks['witness_BO_reduction']=same(replace(S,(3,)),add(P,AA,-1))
witness=F(sum(N[i][j]*S[j][i] for i in range(64) for j in range(64)),80)
checks['witness_negative_one_fifth']=witness==F(-1,5)
assert all(checks.values()),checks
out={'name':'independently flagged extensibly causal nonseparable process','dimensions':list(DIMS),'basis_order':['F_A','A_I','A_O','F_B','B_I','B_O'],'basis_bits':'lexicographic binary; each flag is the leading bit of its enlarged local input','W_denominator':80,'W_integer_numerator':N,'S_integer_matrix':S,'trace_W':'4','witness_expectation':str(witness),'spectrum':[{'value':'(5 - 3*sqrt(2))/80','multiplicity':8},{'value':'(5 + 3*sqrt(2))/80','multiplicity':8},{'value':'1/16','multiplicity':48}],'random_robustness':{'convention':'(W + lambda Omega_flag)/(1 + lambda)','lambda_min':'1/5','actual_white_noise_mixture_fraction':'1/6'},'exact_checks':checks,'scope':'Exact validity and nonseparability certificate; the separate analytical theorem supplies the ancilla-uniform causal model.'}
path=Path(__file__).with_name('exact_ec_matrix_certificate.json');path.write_text(json.dumps(out,indent=2))
print(json.dumps({'certificate':path.name,'all_exact_checks_passed':all(checks.values()),'checks':checks,'witness_expectation':str(witness)},indent=2))
