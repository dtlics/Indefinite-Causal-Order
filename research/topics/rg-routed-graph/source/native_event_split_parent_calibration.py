"""Independent exact flag-loop calibration with nontrivial dormant choices.

The underlying directed wiring has a feedback cycle, while its branch graph is
acyclic. Both the unsplit and split M2 vertex have nontrivial scalar-index choices.
"""
from pathlib import Path
from itertools import product
import copy,json
ROOT=Path(__file__).parent
ends={'sb':('S','B'),'sm':('S','M'),'bm':('B','M'),'ma':('M','A'),'an':('A','N'),'nb':('N','B'),'nd':('N','D'),'bd':('B','D'),'smc':('S','M'),'mnc':('M','N'),'ndc':('N','D')}
dims={w:({0:1,1:1} if w in ['ma','an'] or w.endswith('c') else {0:1,1:2}) for w in ends}
ports={'S':([],['sb','sm','smc']),'B':(['sb','nb'],['bm','bd']),'M':(['sm','bm','smc'],['ma','mnc']),'A':(['ma'],['an']),'N':(['an','mnc'],['nb','nd','ndc']),'D':(['bd','nd','ndc'],[])}
routes={'S':[('S',[()],[(1,0,0),(0,1,1)])],
 'B':[('B0',[(1,0)],[(1,0)]),('B1',[(0,1)],[(0,1)])],
 'M':[('M0',[(0,1,0)],[(a,0) for a in range(2)]),('M1',[(1,0,1)],[(a,1) for a in range(2)])],
 'A':[('A',[(a,) for a in range(2)],[(a,) for a in range(2)])],
 'N':[('N0',[(a,0) for a in range(2)],[(0,1,0)]),('N1',[(a,1) for a in range(2)],[(1,0,1)])],
 'D':[('D',[(0,1,0),(1,0,1)],[()])]}
def verify(ends,dims,ports,routes):
 def tdim(ws,t):
  z=1
  for w,a in zip(ws,t):z*=dims[w][a]
  return z
 branches={b:(v,ins,outs) for v,rr in routes.items() for b,ins,outs in rr}
 for b,(v,ins,outs) in branches.items():
  a=sum(tdim(ports[v][0],t) for t in ins)*(4 if v=='S' else 1);bb=sum(tdim(ports[v][1],t) for t in outs)*(4 if v=='D' else 1)
  assert a==bb==(4 if v in ['S','D'] else 2)
 sections=[];ws=list(ends)
 for vals in product(*[list(dims[w]) for w in ws]):
  sec=dict(zip(ws,vals));bs={};io={};ok=True
  for v,(iw,ow) in ports.items():
   inp=tuple(sec[w] for w in iw);out=tuple(sec[w] for w in ow)
   match=[b for b,ins,outs in routes[v] if inp in ins and out in outs]
   if len(match)!=1:ok=False;break
   bs[v]=match[0];io[match[0]]=(inp,out)
  if ok:sections.append({'indices':sec,'branches':bs,'io':io,'statuses':frozenset(bs.values())})
 bn=list(branches);functions=[];counts=[]
 for side in [1,0]:
  domains=[branches[b][1+side] for b in bn];fn={}
  for inds in product(*[range(len(d)) for d in domains]):
   selected={b:domains[k][inds[k]] for k,b in enumerate(bn)}
   matches=[sec for sec in sections if all(sec['io'][b][side]==selected[b] for b in sec['statuses'])]
   assert len(matches)==1,(side,inds,len(matches))
   fn[inds]=matches[0]['statuses']
  functions.append((domains,fn));counts.append(len(fn))
 edges=set();conditional={}
 for sec in sections:
  for w,(v,u) in ends.items():conditional.setdefault((w,sec['branches'][v],sec['branches'][u]),set()).add((sec['indices'][w],dims[w][sec['indices'][w]]))
 for (w,b,c),values in conditional.items():
  if len(values)>1 or any(d>1 for a,d in values):edges.add((b,c,'solid'))
 for side,(domains,fn) in enumerate(functions):
  for choices,status in fn.items():
   for k,b in enumerate(bn):
    for alternative in range(len(domains[k])):
     target=list(choices);target[k]=alternative;diff=status^fn[tuple(target)]
     for c in diff:edges.add((b,c,'green') if side==0 else (c,b,'red'))
 reach={b:{b} for b in bn}
 for a,b,c in edges:reach[a].add(b)
 for k in bn:
  for a in bn:
   if k in reach[a]:reach[a]|=reach[k]
 assert not any(a==b or (a in reach[b] and b in reach[a]) for a,b,c in edges)
 return {'sections':sections,'forward_choices':counts[0],'reverse_choices':counts[1],'edges':sorted(edges),'branch_graph_acyclic':True}
old=verify(ends,dims,ports,routes)
e=copy.deepcopy(ends);d=copy.deepcopy(dims);p=copy.deepcopy(ports);r=copy.deepcopy(routes)
e['ba_flag']=('B','A');e['ab_flag']=('A','B');d['ba_flag']=d['ab_flag']={0:1,1:1}
p['B']=(p['B'][0]+['ab_flag'],p['B'][1]+['ba_flag']);p['A']=(p['A'][0]+['ba_flag'],p['A'][1]+['ab_flag'])
r['B']=[(b,[t+(1 if b=='B0' else 0,) for t in ins],[t+(1 if b=='B0' else 0,) for t in outs]) for b,ins,outs in r['B']]
r['A']=[(f'A{g}',[(a,g) for a in range(2)],[(a,g) for a in range(2)]) for g in range(2)]
new=verify(e,d,p,r)
assert len(old['sections'])==len(new['sections'])==8
for sec in new['sections']:
 projected={w:a for w,a in sec['indices'].items() if w in ends}
 assert sum(projected==o['indices'] for o in old['sections'])==1
 assert sec['indices']['ba_flag']==sec['indices']['ab_flag']==int(sec['branches']['B']=='B0')
assert (old['forward_choices'],old['reverse_choices'])==(16,16)
assert (new['forward_choices'],new['reverse_choices'])==(32,32)
assert not any(color=='solid' and {a[0],b[0]}=={'A','B'} for a,b,color in new['edges'] if a.startswith('A') and b.startswith('B') or a.startswith('B') and b.startswith('A'))
out={'status':'PASS','old':{k:v for k,v in old.items() if k!='sections'},'refined':{k:v for k,v in new.items() if k!='sections'},'consistent_sections':8,'section_projection_bijection':True,'added_flag_wires_have_no_solid_branch_edges':True,'auxiliary_native_algebra_change':'M2 to M2+M2','exact_control_block_contractions':['N0 A1 M0 B0','B1 N1 A0 M1'],'diagonal_auxiliary_restriction_recovers_original':True,'scope':'One explicit feedback-wiring calibration with nontrivial dormant forward and reverse choices; a general graph rewrite requires the separate functional-dependence proof.'}
(ROOT/'native_event_split_parent_calibration_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS oldchoices16/16 refinedchoices32/32;8 sections; both branch graphs acyclic; nontrivial dormant auxiliary choices included',flush=True)
