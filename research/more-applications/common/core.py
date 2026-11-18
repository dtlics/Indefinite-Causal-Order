"""Channel-switch algebra; normalized Choi convention vec(K)/sqrt(d)."""
from __future__ import annotations
import itertools
from dataclasses import dataclass
import numpy as np
from scipy.linalg import expm

I2=np.eye(2,dtype=complex)
X=np.array([[0,1],[1,0]],complex)
Y=np.array([[0,-1j],[1j,0]],complex)
Z=np.diag([1,-1]).astype(complex)
PAULI=[I2,X,Y,Z]

def kron_all(arrays):
    out=np.array([[1]],complex)
    for a in arrays: out=np.kron(out,a)
    return out

def apply(Ks,rho):
    return sum((K@rho@K.conj().T for K in Ks),np.zeros_like(rho,dtype=complex))

def compose(A,B):
    """A after B."""
    return [a@b for a in A for b in B]

def tensor_channels(A,B): return [np.kron(a,b) for a in A for b in B]

def mix(A,B,p): return [np.sqrt(p)*a for a in A]+[np.sqrt(1-p)*b for b in B]

def vec(A): return A.reshape(-1,order='F')

def choi(Ks):
    d=Ks[0].shape[1]
    return sum((np.outer(vec(k),vec(k).conj())/d for k in Ks),np.zeros((Ks[0].shape[0]*d,)*2,complex))

def effect(Ks):
    d=Ks[0].shape[1]
    return sum((k.conj().T@k for k in Ks),np.zeros((d,d),complex))

def tp_error(Ks): return float(np.linalg.norm(effect(Ks)-np.eye(Ks[0].shape[1])))

def switch_branches(A,B):
    return ([ (b@a+a@b)/2 for a in A for b in B],[(b@a-a@b)/2 for a in A for b in B])

def metrics(A,B,rho=None):
    d=A[0].shape[0]
    if rho is None: rho=np.eye(d)/d
    plus,minus=switch_branches(A,B)
    out={}
    for label,ks in [('plus',plus),('minus',minus)]:
        e=effect(ks); probs=np.linalg.eigvalsh(e)
        prob=float(np.trace(e@rho).real)
        pmix=float(np.trace(e).real/d)
        fe=float(sum(abs(np.trace(k))**2 for k in ks)/d**2)
        out['p_'+label]=prob
        out['p_'+label+'_min']=float(probs[0]);out['p_'+label+'_max']=float(probs[-1])
        out['Fe_'+label+'_joint']=fe
        out['Fe_'+label+'_conditional_Bell']=fe/pmix if pmix>1e-14 else None
    out['v']=1-2*out['p_minus']
    out['p_sum_error']=abs(out['p_plus']+out['p_minus']-1)
    out['Fe_AB']=float(sum(abs(np.trace(k))**2 for k in compose(A,B))/d**2)
    out['Fe_BA']=float(sum(abs(np.trace(k))**2 for k in compose(B,A))/d**2)
    return out

def pauli_channel(p):
    assert abs(sum(p)-1)<1e-10 and min(p)>=-1e-12
    return [np.sqrt(max(0,q))*a for q,a in zip(p,PAULI) if q>1e-15]

def depolarize(d,lam):
    # (1-lam)*id + lam*replacement, lam in [0,1].
    K=[np.sqrt(1-lam)*np.eye(d)] if lam<1 else []
    for i in range(d):
        for j in range(d):
            a=np.zeros((d,d),complex); a[i,j]=np.sqrt(lam/d); K.append(a)
    return K

def dephase_axis(axis,p=.5):
    a=np.array(axis,float); a/=np.linalg.norm(a)
    P=a[0]*X+a[1]*Y+a[2]*Z
    return [np.sqrt(1-p)*I2,np.sqrt(p)*P]

def weak_luders(axis,eta):
    a=np.array(axis,float); a/=np.linalg.norm(a);P=a[0]*X+a[1]*Y+a[2]*Z
    c=(np.sqrt((1+eta)/2)+np.sqrt((1-eta)/2))/2
    s=(np.sqrt((1+eta)/2)-np.sqrt((1-eta)/2))/2
    return [c*I2+s*P,c*I2-s*P]

def rotation(axis,theta):
    a=np.array(axis,float);a/=np.linalg.norm(a)
    P=a[0]*X+a[1]*Y+a[2]*Z
    return [np.cos(theta/2)*I2-1j*np.sin(theta/2)*P]

def amplitude(g,up=False):
    K=[np.diag([1,np.sqrt(1-g)]).astype(complex),np.array([[0,np.sqrt(g)],[0,0]],complex)]
    return [X@k@X for k in K] if up else K

def thermal(g,e):
    return [np.sqrt(1-e)*k for k in amplitude(g)]+[np.sqrt(e)*k for k in amplitude(g,True)]

def reset(tau):
    vals,V=np.linalg.eigh(tau);d=len(vals);ks=[]
    for j,t in enumerate(vals):
        if t>1e-14:
            for i in range(d): ks.append(np.sqrt(t)*np.outer(V[:,j],np.eye(d)[i]))
    return ks

def jump_channel(d,source,target,g):
    a=np.eye(d,dtype=complex);a[source,source]=np.sqrt(1-g)
    b=np.zeros((d,d),complex);b[target,source]=np.sqrt(g)
    return [a,b]

def pinching(projectors): return [p.astype(complex) for p in projectors]

def random_channel(d,r,rng):
    M=rng.normal(size=(r*d,d))+1j*rng.normal(size=(r*d,d))
    Q,_=np.linalg.qr(M)
    return [Q[j*d:(j+1)*d,:] for j in range(r)]

def commutator_test(d):
    """Projector Pi_comm = C†C/(2d), C: vec(A)⊗vec(B)->vec(BA-AB)."""
    E=[]
    for j in range(d):
        for i in range(d):
            e=np.zeros((d,d),complex); e[i,j]=1; E.append(e)
    C=np.column_stack([vec(b@a-a@b) for a in E for b in E])
    return C.conj().T@C/(2*d),C

def qubit_quadratic_p(A,B):
    # Tr(C_A)Tr(C_B)-Tr(C_A C_B), C error Pauli coefficient Gram.
    def gram(Ks):
        C=np.zeros((3,3),complex)
        for k in Ks:
            u=np.array([np.trace(P@k)/2 for P in PAULI[1:]])
            C+=np.outer(u,u.conj())
        return C
    Ca,Cb=gram(A),gram(B)
    return float((np.trace(Ca)*np.trace(Cb)-np.trace(Ca@Cb)).real)

def lindblad_channel(H,Ls,t):
    d=H.shape[0];eye=np.eye(d)
    G=-1j*(np.kron(eye,H)-np.kron(H.T,eye))
    for L in Ls:
        M=L.conj().T@L
        G+=np.kron(L.conj(),L)-.5*np.kron(eye,M)-.5*np.kron(M.T,eye)
    S=expm(t*G)
    J=np.zeros((d*d,d*d),complex)
    # standard vec convention (input block, output within)
    for a in range(d):
        for b in range(d):
            e=np.zeros((d,d));e[a,b]=1
            out=(S@vec(e)).reshape(d,d,order='F')
            J[a*d:(a+1)*d,b*d:(b+1)*d]=out
    vals,V=np.linalg.eigh((J+J.conj().T)/2)
    assert vals.min()>-1e-10
    return [np.sqrt(v)*V[:,i].reshape(d,d,order='F') for i,v in enumerate(vals) if v>1e-15]

def pauli_string(s): return kron_all([PAULI['IXYZ'.index(x)] for x in s])

def code_projectors(generators):
    d=len(generators[0]);m=len(generators);out=[]
    for bits in itertools.product([0,1],repeat=m):
        P=np.eye(d,dtype=complex)
        for bit,g in zip(bits,generators): P=P@(np.eye(d)+(-1)**bit*g)/2
        out.append((bits,P))
    return out
