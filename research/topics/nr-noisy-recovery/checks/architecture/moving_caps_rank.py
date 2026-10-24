"""Exact normalization guards for the moving-CAPS minus-support corollary.

These finite fixtures guard the D8 scores, rank-three input support and
decoded-Kraus accounting.  The analytic source-specific support proof and
its SG3/FC2 dependencies belong to the linked moving-CAPS method note.
The checks do not establish the scattering model, packet truncation,
thermal tails, loss channels or a physical routing-loss budget.
Only standard-library integer and Fraction arithmetic is used.
"""
from fractions import Fraction as F
import json

D=8

def require(test,label):
    if not test:raise RuntimeError(label)

def zero():return [[F(0) for _ in range(D)] for _ in range(D)]
def identity():return [[F(i==j) for j in range(D)] for i in range(D)]
def add(a,b):return [[x+y for x,y in zip(r,s)] for r,s in zip(a,b)]
def scale(a,c):return [[c*x for x in row] for row in a]
def mul(a,b):return [[sum(a[i][k]*b[k][j] for k in range(D)) for j in range(D)] for i in range(D)]
def transpose(a):return [list(t) for t in zip(*a)]
def trace(a):return sum(a[i][i] for i in range(D))
def score(ks):
    return (sum(sum(x*x for row in k for x in row) for k in ks)/D,
            sum(trace(k)**2 for k in ks)/(D*D))

def valid_decoder(ls):
    comp=zero()
    for l in ls:comp=add(comp,mul(transpose(l),l))
    # All the concrete decoder fixtures have diagonal completeness.
    require(all(comp[i][j]==0 for i in range(D) for j in range(D) if i!=j),'fixture decoder diagonal completeness')
    require(all(0<=comp[i][i]<=1 for i in range(D)),'trace-nonincreasing decoder')

def support_guard(ks):
    require(all(k[i][j]==0 for k in ks for i in range(D) for j in range(5)),
            'minus annihilates H and V00 input columns')

def reject(fn,label):
    try:fn()
    except RuntimeError:return label
    raise RuntimeError('invalid fixture survived: '+label)

def verify():
    ident=identity();pi=zero()
    for j in (5,6,7):pi[j][j]=1
    # A trace-zero unitary 3-cycle on the minus input support.  This gives
    # raw g_minus=0 and a known decoder that saturates rank3/D8 after recovery.
    minus=zero()
    for source,target in [(5,6),(6,7),(7,5)]:minus[target][source]=1
    plus=add(ident,scale(pi,-1))
    x=add(plus,minus);y=add(plus,scale(minus,-1))
    require(mul(transpose(x),x)==ident and mul(transpose(y),y)==ident,'ordinary fixture unitary')
    pplus,gplus=score([plus]);pminus,gminus=score([minus])
    px,gx=score([x]);py,gy=score([y]);po=(px+py)/2;go=(gx+gy)/2
    require(po==pplus+pminus and go==gplus+gminus,'FC2 score completion')
    require((gplus/pplus-go/po)==(pminus/po)*(gplus/pplus-gminus/pminus),'sharp conditional identity')
    require((gplus/pplus-go/po)<=pminus/po,'sharp conditional upper bound')
    fine=[scale(minus,F(3,5)),scale(minus,F(4,5))]
    support_guard(fine)
    require(score(fine)==score([minus]),'fine Kraus split invariance')
    recovery=transpose(add(minus,plus))
    rank2=zero();rank2[5][5]=rank2[6][6]=1
    sign=identity();sign[5][5]=-1
    decoders={'identity':[ident],'known_unitary_recovery':[recovery],
              'accepted_rank2_filter':[rank2],
              'two_Kraus_phase_mixture':[scale(ident,F(3,5)),scale(sign,F(4,5))]}
    decoded={}
    for label,ls in decoders.items():
        valid_decoder(ls)
        output=[mul(l,k) for l in ls for k in fine]
        support_guard(output)
        p,g=score(output)
        require(g<=F(3,8)*p<=F(3,8)*pminus,'rank3 decoder bound')
        decoded[label]={'p':str(p),'g':str(g)}
    require(F(decoded['known_unitary_recovery']['g'])==F(3,8)*pminus,'rank bound saturation guard')
    mutant=[row[:] for row in minus];mutant[0][0]=F(1,100)
    invalid=[reject(lambda:support_guard([mutant]),'leaked H input'),
             reject(lambda:valid_decoder([scale(ident,2)]),'trace-increasing decoder')]
    return {'status':'passed','fixture_target':'identity on D8; proof covers arbitrary fixed target isometry',
            'support_rank':3,'input_dimension':D,'decoded_fixtures':decoded,
            'invalid_fixtures_rejected':invalid,
            'scope':'Exact finite normalization and decoded-Kraus fixtures for the moving-CAPS rank-three input-support corollary; no packet, truncation, thermal-tail, loss-channel or hardware certificate.'}

if __name__=='__main__':
    print(json.dumps(verify(),sort_keys=True))
