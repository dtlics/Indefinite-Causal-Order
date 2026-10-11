"""Exact quartet obstruction to a branch-central pair-order comparison.

The graph-to-centrality proof is in the accompanying note. This independent
finite check uses the actual normalized singles and tests the necessary
order identities outside every other port's maximal active support.
"""
from pathlib import Path
from itertools import product
import json
import sympy as s
from exact_fixtures import E,R,WORDS,I2,I16,X,Y,Z,local,tensor
ROOT=Path(__file__).parent

def cylinder(i,small):
 cols=[]
 for bit in [0,1]:
  for v in small:
   col=s.zeros(16,1)
   for n,w in enumerate(WORDS):
    if w[i]==bit:
     k=0
     for j,t in enumerate(w):
      if j!=i:k=2*k+t
     col[n]=v[k]
   cols.append(col)
 B=s.Matrix.hstack(*cols)
 return B*(B.H*B).inv()*B.H
S=[cylinder(0,[[1,0,1,0,0,0,0,0],[1,0,0,1,0,0,0,0]]),
   cylinder(1,[[0,1,0,0,0,0,0,0],[0,0,0,0,1,1,-1,-1]]),E[2],E[3]]
assert [int(s.trace(Q)) for Q in S]==[4,4,2,2]
assert all(Q*Q==Q and Q.H==Q for Q in S)
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16))

def F(us):
 W=tensor(us)
 value=W+sum((tensor([Z*us[j]*Z-us[j] if j==i else us[j] for j in range(4)])*E[i] for i in range(4)),s.zeros(16))
 # Independent raw-normalizer reconstruction at each witness context.
 assert value==(W+sum(((local(i,Z)-I16)*W*E[i] for i in range(4)),s.zeros(16)))*D0
 return value
records=[]
for i,j in product(range(4),repeat=2):
 if i==j:continue
 witnesses=[]
 for target in ['i_before_j','j_before_i']:
  for (an,a),(bn,b) in product([('X',X),('Y',Y),('Z',Z)],repeat=2):
   us=[I2]*4;us[i]=a;us[j]=b
   alpha=R[i]*local(i,a)*R[i];beta=R[j]*local(j,b)*R[j]
   G=F(us);assert G.H*G==I16
   ordered=beta*alpha if target=='i_before_j' else alpha*beta
   defect=(G-ordered)*(I16-S[j])
   if defect!=s.zeros(16):break
  else:raise AssertionError((i,j,target))
  row,col=next((r,c) for r in range(16) for c in range(16) if defect[r,c])
  witnesses.append({'uniform_order_on_complement':target,'i_matrix':an,'j_matrix':bn,
    'defect_HS_squared':str(s.trace(defect.H*defect)),
    'nonzero_entry':[row,col,str(defect[row,col])]})
 records.append({'proposed_unbranched_query':i+1,'other_native_query':j+1,'witnesses':witnesses})
 print('i',i+1,'j',j+1,'both orders fail outside S_j:',[w['defect_HS_squared'] for w in witnesses],flush=True)
# Algebraic comparison check for the actually routed switch calibration.
a=s.Matrix(2,2,s.symbols('a0:4'));b0=s.Matrix(2,2,s.symbols('b0:4'));b1=s.Matrix(2,2,s.symbols('c0:4'))
alpha=s.diag(a,a);beta=s.diag(b0,b1);P=s.diag(1,1,0,0)
assert P*beta==beta*P and P*alpha==alpha*P
assert s.diag(a*b0,b1*a)==alpha*beta*P+beta*alpha*(s.eye(4)-P)
out={'status':'PASS','quartet_complement_order_witnesses':records,'total_exact_defects':24,
 'switch_branch_central_comparison_identity':True,
 'quartet_consequence_conditional_on_graph_lemma':'Every original query has a nonzero active native ideal. Therefore all four original query vertices have at least two reachable branches, and Q3=E3,Q4=E4.',
 'scope':'The exact matrices certify the algebraic contradiction. The graph implication and its pinning/end-extraction proof require the accompanying theorem review.'}
(ROOT/'native_single_branch_centrality_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: all24 complementary order defects and exact switch comparison identity',flush=True)
