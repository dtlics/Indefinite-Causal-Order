"""Exact checks of complementarity and positive-kernel continuation obstructions."""
from pathlib import Path
from fractions import Fraction as F
import sys,json,datetime,hashlib
import numpy as np
ROOT=Path(__file__).resolve().parents[1];OUT=Path(__file__).parent
sys.path.insert(0,str(ROOT/'finite-realization'))
from check_flat_tester import red,words,add,mul,star,vec,rankmod,projector_ns,eval_words
I={():F(1)};a={(0,):F(1)}
plus=add((F(1,2),I),(F(1,2),a));minus=add((F(1,2),I),(F(-1,2),a))

def escaping():
 rows=[]
 for m in range(1,13):
  tail=mul({(0,1)*m:F(1)},minus)
  assert add((1,mul(star(plus),plus)),(1,mul(star(tail),tail)))==I
  trace=sum(c*c for c in plus.values())+sum(c*c for c in tail.values());assert trace==1
  energy=sum((1+len(w))**2*c*c for w,c in plus.items())+sum((1+len(w))**2*c*c for w,c in tail.items())
  L=2*m-1;truncated={w:c for w,c in tail.items() if len(w)<=L};assert not truncated
  limit_overlap=mul(star(plus),plus);assert limit_overlap==plus and limit_overlap!=I
  rows.append({'m':m,'tail_word_lengths':sorted(map(len,tail)),'Gram_trace':str(trace),'quadratic_coefficient_energy':str(energy),'fixed_window_local_CPTP_failure_exact':True})
 return {'rows':rows,'finite_coefficient_limit_overlap':{' '.join(map(str,w)):str(c) for w,c in plus.items()},'lost_trace':str(F(1,2))}

def strict_repair():
 p=ROOT/'independent-upper-check/L8_r004_183_independent_result.json';audit=json.loads(p.read_text())
 e=int(audit['PSD_error_integer_bound']);den=int(audit['input_common_denominator'])*int(audit['projection_denominator_per_side'])**2
 rows=[]
 for i,b in enumerate(audit['norm_bounds']):
  sq=int(b['squared_Frobenius']);delta=e*e-sq;assert delta>0
  lower=F(delta,2*e*den);assert lower>0
  rows.append({'flag':i,'strict_squared_margin':str(delta),'rational_coefficient_slack_lower_bound':str(lower)})
 return {'scope':'Dependent exact consequence of the separately audited repair decomposition and saved exact integer residual bounds; no new SDP solve.','audit_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'all_four_slacks_strictly_positive':True,'complementary_normalized_tester_exists':False,'rows':rows}

def normalized_rank_example():
 pairs=[(8,15),(15,8)];L=2;ws=words(L);n=len(ws);d=4
 E,*_=eval_words(pairs,L)
 matrices=[]
 for j in range(n):
  R=np.zeros((d,d),object)
  for k in range(2):R[2*k:2*k+2,2*k:2*k+2]=E[4*k:4*k+4,j].reshape(2,2).T
  matrices.append(R)
 psi=np.eye(d,dtype=object).ravel();V=np.array([np.kron(A,B)@psi for A in matrices for B in matrices],object).T
 Qone=V.T@V*F(1,d);Q=np.repeat(Qone[None],4,axis=0)
 assert all(Qone[j,j]==1 for j in range(n*n))
 P=projector_ns(Q,ws);assert np.array_equal(P,np.repeat(np.eye(n*n,dtype=object)[None],4,axis=0))
 rank,piv=rankmod(Qone.tolist());nonzero_rows=sum(any(z for z in row) for row in V)
 assert rank==nonzero_rows==8
 M=sum(Q[k].reshape(n,n,n,n).diagonal(axis1=1,axis2=3).sum(axis=-1) for k in range(4))*F(1,4*n)
 mrank,_=rankmod(M.tolist());assert mrank==n==5
 assert np.array_equal(M,E.T@E*F(1,d))
 return {'pairs':pairs,'input_dimension':d,'output_dimension_with_flag':2*d,'word_level':L,'word_count':n,'tester_block_dimension':n*n,'tester_block_rank':rank,'full_exact_normalization':True,'all_word_pair_diagonals_one':True,'aggregate_local_rank':mrank,'aggregate_local_dimension':n,'PSD_factor':'Q=V^T V/4, four identical flag blocks','rank_upper_bound':'V has exactly eight nonzero rows; modular nonzero minor gives rank eight','local_annihilator_exists_at_this_level':False,'scope':'Actual physical normalized tester; not claimed complementary to an optimal GYNI dual.'}


def positive_lift_failure():
 rows=[]
 C={(0,1):F(1,2),(1,0):F(1,2)};b={(1,):F(1)}
 for c,s in [(F(7,25),F(24,25)),(F(161,289),F(240,289))]:
  assert c*c+s*s==1 and c!=0
  r=add((1,C),(-c,I));ff=add((1/s,b),(-c/s,a))
  assert mul(r,ff)==mul(ff,r)
  assert mul(ff,ff)==add((1,I),(-2*c/(s*s),r))
  rf=mul(r,ff);rr=mul(r,r)
  assert rf and all(len(w)%2==1 for w in rf)
  assert rr[(0,1,0,1)]==F(1,4)
  assert max(map(len,r))==2 and max(map(len,rr))==4
  rows.append({'c':str(c),'s':str(s),'minimal_word_level':2,'evaluation_kernel_relation':'C-cI','F_squared_identity_exact':True,'odd_cross_term_nonzero':True,'r_squared_length_four_coefficient':str(rr[(0,1,0,1)]),'positive_universal_TP_lift_at_level_two':False})
 return rows

out={'status':'PASS_EXACT','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'floating_arithmetic_used':False,'escaping_NS_example':escaping(),'current_upper_slack_test':strict_repair(),'normalized_global_rank_example':normalized_rank_example(),'minimal_level_positive_lift_obstruction':positive_lift_failure()}
(OUT/'exact_obstruction_tests.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'utc':out['utc'],'escaping_examples':len(out['escaping_NS_example']['rows']),'strict_current_slacks':True,'rank_example':out['normalized_global_rank_example']},indent=2))
