"""Independent exact audit/calibration of green-layer fixed future markers.

The proof is in green_layer_future_marker_independent_audit.md.  Here the
literal native binary Lugano host is checked on its full choice domains,
then its row contraction is checked coefficientwise and with three private
qubit ancillas.  No numerical ranks or generic random assertions are used.
"""
from pathlib import Path
from itertools import product
import json
import numpy as np
import sympy as s

ROOT=Path(__file__).parent
BITS=list(product((0,1),repeat=3))
def w(o):
 a,b,c=o;return (b*(1-c),(1-a)*c,a*(1-b))
def num(o):return 4*o[0]+2*o[1]+o[2]
LABS=[('L',i,x) for i,x in product(range(3),(0,1))]
D=('D',)
def status(o):return frozenset([D,('H',*o),*(('L',i,w(o)[i]) for i in range(3))])
# Hub branch H_o has fixed scalar input tuple o and output tuple (w(o),o).
# Lab branch (i,x) has external qubit input and two scalar output sectors.
# D is a native M8 decoder of the scalar tuple o. All practical dimensions
# are balanced: lab 2, hub 1, decoder 8. All six lab choices are retained.
forward={}
for f in product((0,1),repeat=6):
 sols=[o for o in BITS if all(o[i]==f[2*i+w(o)[i]] for i in range(3))]
 assert len(sols)==1;forward[f]=sols[0]
reverse={o:o for o in BITS} # the only reverse index coordinate is D's o
edges=set()
for f,o in forward.items():
 for k in range(6):
  ff=list(f);ff[k]^=1
  for b in status(o)^status(forward[tuple(ff)]):edges.add((LABS[k],b,'green'))
for o,p in product(BITS,repeat=2):
 for b in status(o)^status(p):edges.add((b,D,'red'))
# Conditional wire-sector sets are singleton 1D at each co-occurring pair:
# L_i->H_o carries o_i, H_o->L_i carries w_i(o), H_o->D carries o.
nodes=set().union(*(status(o) for o in BITS));reach={a:{a} for a in nodes}
for a,b,col in edges:reach[a].add(b)
for k in nodes:
 for a in nodes:
  if k in reach[a]:reach[a]|=reach[k]
comps={frozenset(b for b in nodes if b in reach[a] and a in reach[b]) for a in nodes}
cycles=[]
for cc in comps:
 ee=[e for e in edges if e[0] in cc and e[1] in cc]
 if len(cc)>1 or any(a==b for a,b,col in ee):
  assert {col for a,b,col in ee}=={'green'};cycles.append(cc)
assert cycles==[frozenset(('L',i,0) for i in range(3))]

# Independent literal row construction; rows are future o, columns past p.
def literal(U,branch=None):
 return s.Matrix(8,8,lambda a,b: (s.prod(U[i,w(BITS[a])[i]][BITS[a][i],BITS[b][i]] for i in range(3))
  if branch is None or w(BITS[a])[branch[0]]==branch[1] else 0))
I=s.eye(2);X=s.Matrix([[0,1],[1,0]]);R=s.Matrix([[3,-4],[4,3]])/5
# Distinct pinned winner baselines deliberately need not be identities.
pinned=[I,R,R.T]
vs=s.symbols('u0:12');variable=[s.Matrix(2,2,vs[4*i:4*i+4]) for i in range(3)]
U={(i,x):(variable[i] if x==0 else pinned[i]) for i,x in product(range(3),(0,1))}
G=literal(U)
Ps=[s.diag(*(int(w(o)[i]==0) for o in BITS)) for i in range(3)]
for i in range(3):
 assert literal(U,(i,0))==Ps[i]*G
# Full symbolic coefficient identities: each of 64 entries is a polynomial
# in the 12 independent losing-branch entries, pinned winners fixed.
coefficients=sum(len(s.Poly(x,*vs).terms()) for x in G if x!=0)
# A dense fixed future decoder and source rotate the physical marker.
Dec=s.kronecker_product(R,R.T,R);Src=s.kronecker_product(R.T,R,R)
for i in range(3):
 K=Dec*Ps[i]*Dec.T
 assert K*K==K and K.T==K
 assert Dec*literal(U,(i,0))*Src==K*(Dec*G*Src)

# Exact TWO-STAGE exchange recovery, including losing/winning siblings at
# each same native vertex. First all six lab branches are exchanged: the
# full partial exchange is a 512x512 permutation. R consists of winners;
# C consists of losers. Hub and decoder are fixed to their scalar baselines.
# Close an inactive exchange with Theta^dagger/d = I2/2, rather than an
# inverse variable trace. This makes recovery an everywhere-defined linear
# operation, polynomial in the desired active fillers.
from collections import defaultdict
T0=defaultdict(lambda:s.S.Zero)
T0marked=[defaultdict(lambda:s.S.Zero) for _ in range(3)]
full_exchange_images=set()
for p,t,v in product(BITS,repeat=3):
 sol=[o for o in BITS if all(o[i]==(t[i] if w(o)[i]==0 else v[i]) for i in range(3))]
 assert len(sol)==1;o=sol[0];xx=w(o)
 # A useful direct check of H2 in this literal example: losing status does
 # not depend on any R output coordinate, nor on the original data p.
 assert xx==w(t)
 c=tuple(p[i] if xx[i]==0 else t[i] for i in range(3))
 rr=tuple(p[i] if xx[i]==1 else v[i] for i in range(3))
 full_exchange_images.add((c,rr,o))
 # Q_q is diagonal in future o (hence independent of C_in). Its complement
 # at each vertex is precisely the losing sibling, not an absent vertex.
 wt=s.prod(int(v[i]==rr[i]) if xx[i]==1 else s.Rational(int(v[i]==rr[i]),2)
           for i in range(3))
 if wt:
  key=(c,o,p,t);T0[key]+=wt
  for j in range(3):
   if xx[j]==0:T0marked[j][key]+=wt
assert len(full_exchange_images)==512
assert len(T0)==64 and set(T0.values())=={1}
assert len({(c,o) for c,o,p,t in T0})==64
recovered=s.zeros(8);marked_recovered=[s.zeros(8) for _ in range(3)]
for (c,o,p,t),weight in T0.items():
 xx=w(o)
 # Same RIGHT-domain C pattern for every marked and unmarked recovery.
 # Its complement is the already recovered winning sibling.
 wt=weight*s.prod(variable[i][t[i],c[i]] if xx[i]==0 else
                    s.Rational(int(t[i]==c[i]),2) for i in range(3))
 recovered[num(o),num(p)]+=wt
 for j in range(3):
  if (c,o,p,t) in T0marked[j]:marked_recovered[j][num(o),num(p)]+=wt
all_winners_identity={(i,x):(variable[i] if x==0 else I) for i,x in product(range(3),(0,1))}
literal_identity=literal(all_winners_identity)
assert (recovered-literal_identity).applyfunc(s.expand)==s.zeros(8)
for j in range(3):
 assert (marked_recovered[j]-Ps[j]*literal_identity).applyfunc(s.expand)==s.zeros(8)

# Independent arbitrary private qubits at the three native vertices.
# Chosen native 4x4 rational unitaries have noncommuting operator blocks.
r=np.array([[3,-4],[4,3]],dtype=np.int64);i2=np.eye(2,dtype=np.int64)
cn=np.array([[1,0,0,0],[0,1,0,0],[0,0,0,1],[0,0,1,0]],dtype=np.int64)
sw=np.array([[1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,1]],dtype=np.int64)
Us=[np.kron(r,i2)@cn@np.kron(i2,r),np.kron(i2,r.T)@sw@np.kron(r,i2),
    np.kron(r.T,i2)@cn.T@np.kron(i2,r.T)]
for uu in Us:assert np.array_equal(uu.T@uu,625*np.eye(4,dtype=np.int64))
blocks=[]
for i in range(3):
 bb={(x,o,p):(Us[i][2*o:2*o+2,2*p:2*p+2] if x==0 else
       (25*i2 if o==p else np.zeros((2,2),dtype=np.int64)))
       for x,o,p in product((0,1),repeat=3)}
 assert any(np.any(bb[0,o,p]@bb[0,q,t]-bb[0,q,t]@bb[0,o,p])
            for o,p,q,t in product((0,1),repeat=4))
 blocks.append(bb)
GG=np.zeros((64,64),dtype=np.int64)
for a,o in enumerate(BITS):
 for b,p in enumerate(BITS):
  mats=[blocks[i][w(o)[i],o[i],p[i]] for i in range(3)]
  GG[8*a:8*a+8,8*b:8*b+8]=np.kron(np.kron(mats[0],mats[1]),mats[2])
den=25**3
assert int(np.max(np.abs(GG)))<=den
assert 64*den**2<2**63  # bound every first Gram dot product before computing it
assert np.array_equal(GG.T@GG,den**2*np.eye(64,dtype=np.int64))
assert np.array_equal(GG@GG.T,den**2*np.eye(64,dtype=np.int64))
assert 64*den**4==3814697265625000000<2**63
for i in range(3):
 pm=np.array([int(w(o)[i]==0) for o in BITS for a in range(8)],dtype=np.int64)
 marked=GG*pm[:,None]
 assert np.array_equal(marked@GG.T,den**2*np.diag(pm))
 gram=marked.T@marked
 # Exact unitarity makes gram/den^2 a positive contraction. Therefore every
 # entry has absolute value <=den^2; the explicit dot-product bound below
 # independently certifies that int64 cannot wrap in the quartic check.
 assert int(np.max(np.abs(gram)))<=den**2
 assert np.array_equal(gram@gram,den**2*gram)

# Time reversal gives a fixed PAST marker and generally no fixed future
# marker. Identity context fixes the only possible future marker to P_j.
# This negative calibration guards the color/orientation of the theorem.
UU={(i,x):I for i,x in product(range(3),(0,1))};UU[0,0]=X
H=literal(UU);assert H.T*H==s.eye(8)
negative=[]
for j in (1,2):
 defect=H.T*Ps[j]-Ps[j]*H.T
 if defect!=s.zeros(8):
  negative.append({'variable_losing_vertex':0,'marked_losing_vertex':j,
                   'squared_HS_defect':str(s.trace(defect.T*defect))})
assert negative
out={'status':'PASS','native_boundary_dimension':8,
 'native_algebras':{'labs':'(M2+M2)^3','hub':'C^8','future_decoder':'M8'},
 'full_forward_choices':len(forward),'full_reverse_choices':len(reverse),
 'sections':8,'solid_edges':0,'green_edges':sum(e[2]=='green' for e in edges),
 'red_edges':sum(e[2]=='red' for e in edges),
 'green_SCC':sorted(next(iter(cycles))),'losing_branch_markers_ranks':[int(p.trace()) for p in Ps],
 'full_symbolic_losing_branch_marker_identities':True,'nonzero_polynomial_row_terms':coefficients,
 'two_stage_partial_exchange_dimension':512,'after_future_recovery_dimension':64,
 'active_desired_inactive_normalized_bypass_recovery':True,
 'same_vertex_C_R_sibling_complements_checked':True,
 'identical_current_pattern_recovery_marked_unmarked':True,
 'rotated_source_decoder_marker_identities':True,
 'private_ancilla_dimensions':[2,2,2],'amplified_matrix_dimension':64,
 'amplified_integer_numerator_denominator':den,'exact_amplified_unitarity':True,
 'int64_quartic_dot_bound':64*den**4,'int64_overflow_excluded':True,
 'noncommuting_private_operator_blocks_at_every_vertex':True,
 'exact_amplified_fixed_future_markers':True,'time_reverse_fixed_future_counterexamples':negative,
 'scope':'Exact cyclic calibration and coefficient identity. Arbitrary ancillary completeness is proved in the accompanying exchange audit, not inferred from the finite 64x64 test.'}
(ROOT/'green_layer_future_marker_independent_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2),flush=True)
