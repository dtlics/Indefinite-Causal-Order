"""Actual routed calibration: scalar record bypass versus quantum subdivision.

The base graph is the time-reversed binary Lugano hub. All route branches and
their full forward/reverse choice domains are explicit. No process rank test
is used as a routing certificate.
"""
from pathlib import Path
from itertools import product
import json
ROOT=Path(__file__).parent
WORDS=list(product(range(2),repeat=3))
CHOICES=list(product(range(2),repeat=6))
def winner(p):
    a,b,c=p;return (b*(1-c),(1-a)*c,a*(1-b))
def lab(i,x,part='L'):return (part,i,x)
def hub(p):return ('H',*p)
S=('S',)
def number(p):return 4*p[0]+2*p[1]+p[2]
def record(p):
    n=number(p);return 0 if n in [0,7] else n
def split(p):return ('split',number(p))
def merge(p):return ('merge',number(p))
def phase(p):return ('record',record(p))


def audit(mode):
    sections=[]
    for p in WORDS:
        x=winner(p)
        if mode=='quantum_subdivision':
            status={S,hub(p)}|{lab(i,x[i],part) for i in range(3) for part in ['B','A']}
        else:
            status={S,hub(p)}|{lab(i,x[i]) for i in range(3)}
            if mode=='scalar_bypass':status|={split(p),merge(p),phase(p)}
        sections.append({'p':p,'x':x,'status':frozenset(status)})
    nodes=set().union(*(v['status'] for v in sections))
    # The only forward choice is the source's eight-valued p.
    forward={p:next(v for v in sections if v['p']==p) for p in WORDS}
    assert len(forward)==8
    reverse={}
    for f in CHOICES:
        sol=[v for v in sections if all(v['p'][i]==f[2*i+v['x'][i]] for i in range(3))]
        assert len(sol)==1
        reverse[f]=sol[0]
    edges=set()
    for p,v in forward.items():
        for q in WORDS:
            for n in v['status']^forward[q]['status']:edges.add((S,n,'green'))
    # Reverse influence from a branch's input choice to another status is
    # drawn in the opposite direction, exactly as in the primary definition.
    for f,v in reverse.items():
        for k in range(6):
            ff=list(f);ff[k]^=1
            target=lab(k//2,k%2,'B' if mode=='quantum_subdivision' else 'L')
            for n in v['status']^reverse[tuple(ff)]['status']:edges.add((n,target,'red'))
    wires={}
    def add(wire,src,dst,value,dimension):
        wires.setdefault((wire,src,dst),set()).add((value,dimension))
    for v in sections:
        p,x=v['p'],v['x'];h=hub(p)
        if mode=='scalar_bypass':
            add('source_split',S,split(p),number(p),1)
            add('record_in',split(p),phase(p),record(p),1)
            add('record_out',phase(p),merge(p),record(p),1)
            add('multiplicity_bypass',split(p),merge(p),number(p),1)
            add('merge_hub',merge(p),h,number(p),1)
        else:add('source_hub',S,h,number(p),1)
        for i in range(3):
            if mode=='quantum_subdivision':
                b=lab(i,x[i],'B');a=lab(i,x[i],'A')
                add(('hub_lab',i),h,b,(x[i],p[i]),1)
                add(('quantum_internal',i),b,a,x[i],2)
                add(('lab_hub',i),a,h,x[i],1)
            else:
                a=lab(i,x[i]);add(('hub_lab',i),h,a,(x[i],p[i]),1)
                add(('lab_hub',i),a,h,x[i],1)
    for (wire,a,b),values in wires.items():
        if len(values)>1 or next(iter(values))[1]>1:edges.add((a,b,'solid'))
    reach={n:{n} for n in nodes}
    for a,b,color in edges:reach[a].add(b)
    for k in nodes:
        for a in nodes:
            if k in reach[a]:reach[a]|=reach[k]
    comps={frozenset(b for b in nodes if b in reach[a] and a in reach[b]) for a in nodes}
    cyclic=[]
    valid=True
    for c in comps:
        internal=[(a,b,col) for a,b,col in edges if a in c and b in c]
        if len(c)>1 or any(a==b for a,b,col in internal):
            colors={col for a,b,col in internal};weak=(colors=={'green'} or colors=={'red'})
            valid &= weak
            cyclic.append({'nodes':sorted(c),'edge_colors':sorted(colors),'weak':weak})
    if mode=='scalar_bypass':
        assert valid and not any(c=='solid' for a,b,c in edges)
        assert sorted(sum(record(p)==k for p in WORDS) for k in range(7))==[1,1,1,1,1,1,2]
    if mode=='quantum_subdivision':
        assert not valid and any('solid' in c['edge_colors'] for c in cyclic)
    if mode=='base':assert valid
    return {'mode':mode,'complete_forward_choice_count':len(forward),
            'complete_reverse_choice_count':len(reverse),'consistent_sections':len(sections),
            'nodes':len(nodes),'green_edges':sum(c=='green' for a,b,c in edges),
            'red_edges':sum(c=='red' for a,b,c in edges),
            'solid_edges':sum(c=='solid' for a,b,c in edges),
            'weak_loops_pass':valid,'cyclic_components':cyclic,
            'native_branches':('source M8, hub C^8, labs (M2+M2)^3; splitter C^8, record C^7, merger C^8'
                if mode=='scalar_bypass' else 'source M8, hub C^8; each original lab is one M2+M2 vertex'
                if mode=='base' else 'source M8, hub C^8; each lab is two separate M2+M2 vertices connected by dimension2 sectors')}


results=[audit(mode) for mode in ['base','scalar_bypass','quantum_subdivision']]
assert results[0]['weak_loops_pass'] and results[1]['weak_loops_pass'] and not results[2]['weak_loops_pass']
(ROOT/'seven_context_lugano_rewrite_checks.json').write_text(json.dumps({'status':'PASS',
    'results':results,
    'positive_construction':'An actually present scalar edge label can be coarsened into one C^7 phase vertex with a residual-index bypass, preserving the full choice domains and weak loops in this host.',
    'negative_calibration':'Serially subdividing the recurrent M2 lab branches preserves the complete tensor through matrix multiplication but this naive graph gains solid/red cycles.',
    'scope':'Exact calibration on the reversed Lugano host only. No automatic scalar-record realization or graph rewrite for the quartet follows.'},indent=2)+'\n')
for r in results:print(r['mode'],'choices',r['complete_forward_choice_count'],r['complete_reverse_choice_count'],
                      'solid',r['solid_edges'],'weak loops',r['weak_loops_pass'],flush=True)
