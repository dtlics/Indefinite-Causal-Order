exec(open('auxiliary_supported_cut_pair12_test.py').read().split('j=json.load')[0])
P=s.Matrix([1,-1]);v=tensor([I2,I2,P,s.Matrix([0,1])]);K=v
for aa in [[4,5,6,4],[5,4,5,6],[6,6,6,6],[4,4,4,4],[0,0,4,5],[4,5,0,0]]:
 us=[origins[a] for a in aa];l=[us[0],us[1],I2,I2];r=[I2,I2,us[2],us[3]]
 M=(F(r).H*F(us)*F(l).H-I16)*K;M=M.applyfunc(s.expand)
 print(aa,'zero',M==s.zeros(16,4),'rank',M.rank(),flush=True)
