"""Quantum-program compiler and code-aware coherent-error cancellation checks.
All full-channel comparisons use normalized Choi matrices, hence include references.
"""
import json
import numpy as np
from core import *

def partial_initial_kraus(U,sigma,d,r):
    w,V=np.linalg.eigh(sigma); K=[]
    for v in range(r):
        if w[v]<1e-13:continue
        start=np.kron(np.eye(d),V[:,v:v+1])
        for e in range(r):
            finish=np.kron(np.eye(d),np.eye(r)[e:e+1,:])
            K.append(np.sqrt(w[v])*finish@U@start)
    return K

def sw(A,B):
    d=A[0].shape[0];out=[]
    for a in A:
        for b in B:
            k=np.zeros((2*d,2*d),complex);k[:d,:d]=b@a;k[d:,d:]=a@b;out.append(k)
    return out

def compiler(V,sigma,B,d,r):
    # Retain exactly the SAME program through the first and final controlled V.
    Dr=d*r;eye=np.eye(Dr);zero=np.zeros((Dr,Dr))
    C0=np.block([[V,zero],[zero,eye]]);C1=np.block([[eye,zero],[zero,V]])
    w,U=np.linalg.eigh(sigma);out=[]
    for j,b in enumerate(B):
        total=C1@np.kron(np.eye(2),np.kron(b,np.eye(r)))@C0
        for v in range(r):
            if w[v]<1e-13:continue
            start=np.kron(np.eye(2*d),U[:,v:v+1])
            for e in range(r):
                finish=np.kron(np.eye(2*d),np.eye(r)[e:e+1,:])
                out.append(np.sqrt(w[v])*finish@total@start)
    return out

def controlled_cq_processor():
    # Bits: target, program_0, program_1, label. CNOT target->label, then
    # controlled-SWAP target with the indicated program. Known 16x16 unitary.
    V=np.zeros((16,16),complex)
    for x in range(16):
        t,p0,p1,l=[(x>>(3-j))&1 for j in range(4)]
        l^=t
        if l==0:t,p0=p0,t
        else:t,p1=p1,t
        y=8*t+4*p0+2*p1+l;V[y,x]=1
    assert np.linalg.norm(V.conj().T@V-np.eye(16))<1e-12
    return V

def mixed(d,rng):
    x=rng.normal(size=(d,d))+1j*rng.normal(size=(d,d));a=x@x.conj().T;return a/np.trace(a)

def logical_channel(K,V,Rs):return [r@k@V for k in K for r in Rs]

def fe(K,D=2):return float(sum(abs(np.trace(k))**2 for k in K)/D**2)

def main():
    rng=np.random.default_rng(930425);tests=[]
    for d,r in [(2,2),(2,3),(3,2),(4,2)]:
        for rep in range(8):
            z=rng.normal(size=(d*r,d*r))+1j*rng.normal(size=(d*r,d*r));V,_=np.linalg.qr(z)
            sigma=mixed(r,rng);B=random_channel(d,3,rng);A=partial_initial_kraus(V,sigma,d,r)
            residual=np.linalg.norm(choi(sw(A,B))-choi(compiler(V,sigma,B,d,r)))
            tests.append({'d':d,'program_dim':r,'residual':float(residual)})
    cq=[];Vproc=controlled_cq_processor()
    for rep in range(10):
        tau0=mixed(2,rng);tau1=mixed(2,rng);sigma=kron_all([tau0,tau1,np.diag([1,0])])
        A=partial_initial_kraus(Vproc,sigma,2,8)
        # Direct measure in the Z basis, prepare tau_i.
        Aref=[]
        for i,tau in enumerate([tau0,tau1]):
            w,v=np.linalg.eigh(tau)
            for j in range(2): Aref.append(np.sqrt(w[j])*np.outer(v[:,j],np.eye(2)[i]))
        assert np.linalg.norm(choi(A)-choi(Aref))<1e-12
        B=random_channel(2,4,rng)
        residual=np.linalg.norm(choi(sw(Aref,B))-choi(compiler(Vproc,sigma,B,2,8)))
        cq.append(float(residual))
    assert max(t['residual'] for t in tests)<1e-11 and max(cq)<1e-11
    # Code with two syndrome qubits and one logical qubit.
    P=pauli_string('XII');Q=pauli_string('ZXI');L=pauli_string('IIZ');R=1j*P@Q@L
    errors=[np.eye(8),P,Q,R]
    V=np.zeros((8,2),complex);V[0,0]=1;V[1,1]=1
    Pcode=V@V.conj().T
    # All four correctable error subspaces are mutually orthogonal and exhaust.
    recovery=[V.conj().T@e.conj().T for e in errors]
    assert np.linalg.norm(sum(r.conj().T@r for r in recovery)-np.eye(8))<1e-12
    for i,e in enumerate(errors):
        for j,f in enumerate(errors):
            assert np.linalg.norm(V.conj().T@e.conj().T@f@V-(np.eye(2) if i==j else np.zeros((2,2))))<1e-12
    rows=[]
    def random_supported():
        w=rng.dirichlet(np.ones(4));out=[]
        for prob in w:
            n=rng.normal(size=3);n/=np.linalg.norm(n);theta=rng.uniform(-np.pi,np.pi)
            u=np.cos(theta)*np.eye(8)-1j*np.sin(theta)*(n[0]*P+n[1]*Q+n[2]*R)
            out.append(np.sqrt(prob)*u)
        return out
    for rep in range(40):
        A=random_supported();B=random_supported();plus,minus=switch_branches(A,B)
        ordinary=logical_channel(compose(B,A),V,recovery)
        corrected=logical_channel(plus,V,recovery)+logical_channel([L@k for k in minus],V,recovery)
        residual=np.linalg.norm(choi(corrected)-choi([np.eye(2)]))
        assert residual<1e-11
        rows.append({'ordinary_fixed_recovery_fidelity':fe(ordinary),'switch_corrected_fidelity':fe(corrected),'residual':float(residual)})
    # Known noiseless subsystem removes this constructed advantage if encoding changes.
    # Pick chirality Z3=+1. Logical Z=X2, logical X=X1 Z2 commute with all noise.
    XL=pauli_string('XZI');ZL=pauli_string('IXI')
    for e in errors:
        assert np.linalg.norm(e@XL-XL@e)<1e-12
        assert np.linalg.norm(e@ZL-ZL@e)<1e-12
    # Input code for multiplicity: stabilizer X1=+1 (fix gauge), Z3=+1,
    # eigenvalues of X2 carry logical basis; noise acts on gauge, decode by traces.
    plusv=np.array([1,1])/np.sqrt(2);minusv=np.array([1,-1])/np.sqrt(2);zero=np.array([1,0])
    W=[]
    # Build gauge0 states P=+1 with ZL=X2=+/-; gauge1 reached by Q.
    for lv in [plusv,minusv]:
        z=kron_all([plusv[:,None],lv[:,None],zero[:,None]]).ravel()
        W.extend([z,Q@z])
    W=np.column_stack(W)
    assert np.linalg.norm(W.conj().T@W-np.eye(4))<1e-12
    Vdfs=W[:,[0,2]];decode=[W[:,[g,2+g]].conj().T for g in range(2)]
    for rep in range(20):
        A=random_supported();B=random_supported()
        ch=logical_channel(compose(B,A),Vdfs,decode)
        assert np.linalg.norm(choi(ch)-choi([np.eye(2)]))<1e-11
    out={'random_program_cases':tests,'measure_prepare_cases':cq,'graded_code_cases':rows,
         'graded_code_DFS_cases':20,'max_program_residual':max(t['residual'] for t in tests)}
    open('program_and_code_results.json','w').write(json.dumps(out,indent=2))
    print('PASS:',len(tests),'mixed-program cases;',len(cq),'unknown measure/prepare cases;',len(rows),'graded-code cases;20 ordinary DFS comparisons')
if __name__=='__main__':main()
