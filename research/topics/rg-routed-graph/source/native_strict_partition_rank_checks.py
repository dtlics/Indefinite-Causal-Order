"""Exact rank-four cocycle witnesses for every ordered crossing pair."""
from pathlib import Path
import json
import sympy as s
from exact_fixtures import E,R,I2,I16,X,Y,Z,local,tensor
ROOT=Path(__file__).parent
D0=I16+sum(((local(i,Z)-I16)*E[i] for i in range(4)),s.zeros(16))
P={'X':X,'Y':Y,'Z':Z}
out=[]
for rec in json.loads((ROOT/'native_branch_cover_checks.json').read_text())['quartet_pair_nonseriality']:
 i=rec['before']-1;j=rec['after']-1;a,b=[P[n] for n in rec['queries']]
 us=[I2]*4;us[i]=a;us[j]=b;W=tensor(us)
 F=(W+sum(((local(k,Z)-I16)*W*E[k] for k in range(4)),s.zeros(16)))*D0
 alpha=R[i]*local(i,a)*R[i];beta=R[j]*local(j,b)*R[j]
 C=beta.H*F*alpha.H;assert C.H*C==I16
 defect=C-I16;assert defect.rank()==4
 out.append({'before':i+1,'after':j+1,'queries':rec['queries'],'cocycle_minus_identity_rank':4})
assert len(out)==12
(ROOT/'native_strict_partition_rank_checks.json').write_text(json.dumps({'status':'PASS','witnesses':out,'consequence':'Once strict global auxiliary/original orientations give a partition and C in beta(M_d) prime, any proper partition forces d to divide4. Thus unital full M8 and M16 auxiliary slots with those orientations are boundary-only without a separate cocycle-removal lemma.'},indent=2)+'\n')
print('PASS: all12 ordered crossing-pair cocycles differ from identity by rank4')
