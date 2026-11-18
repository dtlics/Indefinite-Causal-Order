from core import *
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
low=np.array([[0,1],[0,0]],complex)
L1=np.kron(low,I2);L2=np.kron(I2,low)
I4=np.eye(4,dtype=complex)
phys={
'collective_dephasing':lindblad_channel(np.zeros((4,4)),[(np.kron(Z,I2)+np.kron(I2,Z))/2],.1),
'differential_dephasing':lindblad_channel(np.zeros((4,4)),[(np.kron(Z,I2)-np.kron(I2,Z))/2],.1),
'collective_decay':lindblad_channel(np.zeros((4,4)),[(L1+L2)/np.sqrt(2)],.1),
'phase_shifted_collective_decay':lindblad_channel(np.zeros((4,4)),[(L1+1j*L2)/np.sqrt(2)],.1),
'independent_decay':lindblad_channel(np.zeros((4,4)),[L1/np.sqrt(2),L2/np.sqrt(2)],.1),
'collective_heating':lindblad_channel(np.zeros((4,4)),[(L1+L2).conj().T/np.sqrt(2)],.1),
'coherent_ZZ_crosstalk': [expm(-.2j*np.kron(Z,Z))],
'local_Z_dephasing':lindblad_channel(np.zeros((4,4)),[np.kron(Z,I2)/2,np.kron(I2,Z)/2],.1),
}
rows=[]
for i,(an,A) in enumerate(phys.items()):
 for bn,B in list(phys.items())[i:]:rows.append({'family':'collective_twoqubit','A':an,'B':bn,**metrics(A,B)})
# Exact finite-Fock bosonic pure loss n<=4: no unphysical cutoff on upward transitions.
from math import comb
D=5
num=np.diag(np.arange(D)).astype(complex)
parity=np.diag([(-1)**j for j in range(D)]).astype(complex)

def pureloss(loss):
    eta=1-loss;Ks=[]
    for ell in range(D):
        K=np.zeros((D,D),complex)
        for n in range(ell,D):K[n-ell,n]=np.sqrt(comb(n,ell))*(1-eta)**(ell/2)*eta**((n-ell)/2)
        Ks.append(K)
    return Ks
bos={
'loss_001':pureloss(.01),'loss_01':pureloss(.1),
'number_dephasing':lindblad_channel(np.zeros((D,D)),[num],.1),
'parity_measurement':[(np.eye(D)+parity)/2,(np.eye(D)-parity)/2],
'parity_unitary':[parity],
'Kerr_unitary':[expm(-.1j*num@num)]}
for i,(an,A) in enumerate(bos.items()):
 for bn,B in list(bos.items())[i:]:rows.append({'family':'bosonic_Fock5','A':an,'B':bn,**metrics(A,B)})
# Bosonic binomial-code input: (|0>+|4>)/sqrt2 and |2>.
V=np.zeros((D,2),complex);V[0,0]=V[4,0]=1/np.sqrt(2);V[2,1]=1
code_rho=V@V.conj().T/2
bcode=[]
for an,bn in [('loss_001','loss_001'),('loss_01','parity_unitary'),('loss_01','parity_measurement'),('loss_01','number_dephasing')]:
    bcode.append({'A':an,'B':bn,**metrics(bos[an],bos[bn],code_rho)})
# Known parity measurement samples jump parity; classical accessible readout baseline.
res={'additional_models':len(phys)+len(bos),'additional_equal_dimension_pairs':len(rows),'max_TP_error':max(tp_error(A) for A in list(phys.values())+list(bos.values())),'cases':rows,'bosonic_code_cases':bcode}
ROOT.joinpath('physics_extensions.json').write_text(json.dumps(res,indent=2))
print('extra models',res['additional_models'],'pairs',res['additional_equal_dimension_pairs'])
for r in rows:
 if r['A']==r['B'] or (r['A'],r['B']) in [('collective_dephasing','differential_dephasing'),('collective_decay','phase_shifted_collective_decay'),('collective_decay','collective_heating')]:
  print(r['A'],r['B'],r['p_minus'])
