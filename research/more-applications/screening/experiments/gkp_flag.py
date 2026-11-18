"""Ideal square-GKP analog decoding with a switch-generated displacement-area bit.
Not a finite-energy GKP simulation and not an all-ordinary-protocol lower bound.
[q,p]=i; modular syndrome period sqrt(pi); independent Gaussian q/p kicks.
"""
from pathlib import Path
import numpy as np,json,math
from scipy.special import ndtr
ROOT=Path(__file__).resolve().parent
L=np.sqrt(np.pi)

def run(sigma_q,sigma_p,N=256,flag_flip=0):
    u=(np.arange(N)+.5)*L/N-L/2
    M=max(3,int(np.ceil(9*max(sigma_q,sigma_p)/L+.5)))
    weights=np.zeros((4,2,N,N))
    for m in range(-M,M+1):
        x=u+m*L;fx=np.exp(-x*x/(2*sigma_q*sigma_q))/(np.sqrt(2*np.pi)*sigma_q)
        for n in range(-M,M+1):
            y=u+n*L;fy=np.exp(-y*y/(2*sigma_p*sigma_p))/(np.sqrt(2*np.pi)*sigma_p)
            w=fx[:,None]*fy[None,:]
            cs=(1-2*flag_flip)*np.cos(x[:,None]*y[None,:])
            ell=(m%2)+2*(n%2)
            weights[ell,0]+=w*(1+cs)/2
            weights[ell,1]+=w*(1-cs)/2
    area=(L/N)**2
    normalization=float(weights.sum()*area)
    ordinary=float(weights.sum(axis=1).max(axis=0).sum()*area)
    flagged=float(weights.max(axis=0).sum()*area)
    pminus=float(weights[:,1].sum()*area)
    analytic=(1-1/np.sqrt(1+sigma_q*sigma_q*sigma_p*sigma_p))/2
    analytic=flag_flip+(1-2*flag_flip)*analytic
    # Independent exact ordinary nearest-parity probability, integrated Gaussian tails.
    def even_mass(sig):
        return sum(ndtr((m+.5)*L/sig)-ndtr((m-.5)*L/sig) for m in range(-M,M+1) if m%2==0)
    Fordinary_exact=even_mass(sigma_q)*even_mass(sigma_p)
    return {'sigma_q':sigma_q,'sigma_p':sigma_p,'grid':N,'max_integer':M,'control_flip':flag_flip,'normalization_error':abs(normalization-1),'p_minus':pminus,'p_minus_analytic':analytic,'p_minus_error':abs(pminus-analytic),'ordinary_error':1-ordinary,'ordinary_error_exact':1-Fordinary_exact,'flag_error':1-flagged,'relative_reduction':(flagged-ordinary)/(1-ordinary) if ordinary<1 else 0}

rows=[]
for s in [.2,.3,.4,.5,.6,.7,1.0]:
    a=run(s,s,192);b=run(s,s,384)
    b['grid_error_estimate']=abs(b['flag_error']-a['flag_error'])
    rows.append(b)
for sq,sp in [(.15,.6),(.3,.6),(.4,.7),(.6,1.0)]:
    a=run(sq,sp,192);b=run(sq,sp,384);b['grid_error_estimate']=abs(b['flag_error']-a['flag_error']);rows.append(b)
for eta in [.001,.01,.05]:
    rows.append(run(.5,.5,384,eta))
ROOT.joinpath('gkp_flag.json').write_text(json.dumps({'scope':'Ideal square GKP, exact noiseless modular syndrome, two independent Gaussian displacement channels, standard switch-paired errors. Compares optimal logical Pauli correction from analog syndromes vs those syndromes plus one flag. No all-ordinary bound, no finite-energy / extra noise overhead counted.','cases':rows},indent=2))
print(json.dumps(rows,indent=2))
