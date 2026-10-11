"""Exact graph-independent coefficient-mask obstruction for the safe OPB.
Imports only the portable audited quartet coefficients from exact_fixtures.py.
No numerical tolerance, graph assumptions, or native-algebra classification is used.
"""
from itertools import product
from pathlib import Path
import json
import sympy as s
from exact_fixtures import E,I16,I2,X,WORDS,tensor,local
letters={'0':s.Matrix([1,0]),'1':s.Matrix([0,1]),'+':s.Matrix([1,1]),'-':s.Matrix([1,-1])}
def word(w):return tensor([letters[t] for t in w])
def key(v):
 c=next(x for x in v if x!=0)
 return tuple(s.simplify(x/c) for x in v)
words=['001-','10+0','0001','11-+','0100','0110','11+0','11+1','0000','001+','0101','0111','10+1','10-+','10--','11--']
B=s.Matrix.hstack(*[word(w)/s.sqrt((word(w).T*word(w))[0]) for w in words])
assert B.H*B==I16
lookup={key(word(w)):w for w in product('01+-',repeat=4)}
masks={i:s.ones(16) for i in [2,3]}
for r,o in enumerate(WORDS):
 V=I16-2*sum((o[i]*E[i] for i in range(4)),s.zeros(16))
 for p in range(16):
  ray=lookup[key(V*B[:,p])]
  for i in masks:
   masks[i][r,p]=(-1 if ray[i] in '+-' else 1)
U=(3*I2+4*s.I*X)/5
assert U.H*U==I2
W=local(0,U)
G=(W-2*sum((local(i,s.diag(0,1))*W*E[i] for i in range(4)),s.zeros(16)))*B
assert (G.H*G-I16).applyfunc(s.simplify)==s.zeros(16)
results=[]
for i,mask in masks.items():
 M=G.multiply_elementwise(mask)
 D=(M.H*M-I16).applyfunc(s.simplify)
 hs=s.simplify(s.trace(D.H*D));assert hs==s.Rational(2304,625)
 assert D[0,14]==(1 if i==2 else -1)*12*s.sqrt(2)*s.I/25
 results.append({'basis_flag':i+1,'HS_squared_Gram_defect':str(hs),'entry_0_14':str(D[0,14]),'nonzero_Gram_entries':[(r,c,str(D[r,c])) for r in range(16) for c in range(16) if D[r,c]!=0]})
M=G.multiply_elementwise(masks[2].multiply_elementwise(masks[3]));D=(M.H*M-I16).applyfunc(s.simplify)
parity=masks[2].multiply_elementwise(masks[3])
parity_rowcol=parity==parity[:,0]*parity[0,:]/parity[0,0]
assert all(parity[r,p]==parity[0,p] for r in range(16) for p in range(16))
parity_input_words=[words[p] for p in range(16) if parity[0,p]==-1]
quarter=parity.applyfunc(lambda z:1 if z==1 else s.I)
Mquarter=G.multiply_elementwise(quarter);Dquarter=(Mquarter.H*Mquarter-I16).applyfunc(s.simplify)
report={'original_query_context':['(3I+4iX)/5','I','I','I'],'source_basis':words,'unitarity_without_mask':True,'individual_flag_masks':results,'joint_parity_mask_Gram_defect_HS2':str(s.simplify(s.trace(D.H*D))),'joint_parity_quarter_phase_Gram_defect_HS2':str(s.simplify(s.trace(Dquarter.H*Dquarter))),'parity_sign_is_row_column_factor':parity_rowcol,'parity_depends_only_on_input':True,'parity_one_input_words':parity_input_words,'scope':'Each explicit coefficient mask is forbidden for any otherwise valid full-filler routed host realizing this tensor; nonorthogonal encodings without this mask are not excluded.'}
print(json.dumps(report,indent=2));Path(__file__).with_name('basis_flag_obstruction_checks.json').write_text(json.dumps(report,indent=2)+'\n')
