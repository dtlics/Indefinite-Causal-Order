import json, math
rows=json.load(open('nonpauli_qec_results.json'))+json.load(open('bosonic_results.json'))
won=[]
for r in rows:
    upper=math.sqrt(max(0,min(1,r['coherent_petz'])))
    if r['intermediate_petz']>upper+1e-7:
        won.append({**r,'switch_optimum_upper_from_Barnum_Knill':upper})
open('near_optimality_eliminations.json','w').write(json.dumps(won,indent=2))
assert len(rows)==69
assert len(won)==6
print('PASS:69 modeled QEC cases;6 ordinary intermediate decoders exceed the analytic upper bound on any final switched decoder (numerical channel evaluations).')
