from context_closure import *
import json
v={'0':s.Matrix([1,0]),'1':s.Matrix([0,1]),'+':s.Matrix([1,1]),'-':s.Matrix([1,-1])}
def vec(w):return tensor([v[k] for k in w])
words=['001-','10+0','0001','11-+','0100','0110','11+0','11+1','0000','001+','0101','0111','10+1','10-+','10--','11--']
assert all((vec(a).H*vec(b))[0]==0 for a,b in combinations(words,2))
viol=[]
for word in words:
 for bits in product([0,1],repeat=4):
  W=I16-2*sum((b*e for b,e in zip(bits,E)),s.zeros(16));u=W*vec(word)
  ranks=[]
  for i in range(4):
   inds0=[k for k,w in enumerate(WORDS) if w[i]==0];inds1=[k for k,w in enumerate(WORDS) if w[i]==1]
   ranks.append(s.Matrix([list(u.extract(inds0,[0])),list(u.extract(inds1,[0]))]).rank())
  if max(ranks)>1:viol.append((word,bits,ranks))
print('product-preserving cases',256-len(viol),'of256; first violations',viol[:10])
