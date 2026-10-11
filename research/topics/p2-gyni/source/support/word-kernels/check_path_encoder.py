import json,math
from pathlib import Path
import numpy as np

def g(j):
    k,b=divmod(j,2);return (-k,0) if b==0 else (k,1)
def mul(a,b):return(a[0]+(-1)**a[1]*b[0],a[1]^b[1])
def inv(a):return((-1)**(a[1]+1)*a[0],a[1])
def length(a):
    k,b=a
    return abs(2*k+1) if b else abs(2*k)
rows=[]
for N in range(2,41):
    js=list(range(-N+1,N+1));reps=list(map(g,js));ids={(k%N,b):i for i,(k,b) in enumerate(reps)};assert len(ids)==2*N
    eta=np.zeros(2*N);eta[1:-1]=np.sqrt(2/(2*N-1))*np.sin(np.pi*np.arange(1,2*N-1)/(2*N-1));assert abs(eta@eta-1)<1e-14
    overlaps=[]
    for s in [(0,1),(-1,1)]:
        perm=[]
        for z in reps:
            h=mul(s,z);perm.append(ids[(h[0]%N,h[1])])
        for j in range(1,2*N-1):assert reps[perm[j]]==mul(s,reps[j])
        overlaps.append(float(eta@eta[np.array(perm)]))
    z=math.cos(math.pi/(2*N-1));assert abs(sum(overlaps)/2-z)<1e-14
    ml=max(length(mul(h,inv(gg))) for h in reps for gg in reps[1:-1]);assert ml<=2*N-1
    alpha=[(1+x)/2 for x in overlaps];twirl=sum(alpha[x]*alpha[y] for x in range(2) for y in range(2))/4;assert abs(twirl-((1+z)/2)**2)<1e-14
    rows.append({'N':N,'word_bound':2*N-1,'actual_max_word':ml,'overlaps':overlaps,'twirled_retention':twirl,'upper_multiplier':1/twirl})
out={'status':'passed','finite_groups_checked':39,'scope':'Exact finite group alias/support/word-length checks; numerical sine overlap and twirled retention identities. Full analytic proof in hierarchy_completeness.md.','results':rows};Path(__file__).with_name('path_encoder_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='results'},indent=2))
