"""Reproduce the application screen, then assert the advertised checks.
Known software dependencies only; no network calls or external device access.
Outputs overwrite the current local result files; logs go under _build/.
"""
from __future__ import annotations
import subprocess,sys,os,time,json,csv,hashlib,platform
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parent
LOG=ROOT/'_build';LOG.mkdir(exist_ok=True)
SCRIPTS=['explore.py','derived_checks.py','physics_extensions.py','ordinary_compilation.py',
         'rare_fault_baseline.py','qec.py','qec_polynomials.py','recovery_policy.py',
         'magic_scan.py','reset_factory.py','gkp_flag.py']
env=dict(os.environ,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
runs=[]
for script in SCRIPTS:
    start=time.monotonic()
    with (LOG/(script+'.log')).open('w') as out:
        r=subprocess.run([sys.executable,str(ROOT/script)],cwd=ROOT,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=90)
    runs.append({'script':script,'returncode':r.returncode,'seconds':round(time.monotonic()-start,3)})
    if r.returncode:
        raise RuntimeError(f'{script} failed; see _build/{script}.log')
    print('PASS',script,flush=True)

def data(name):return json.loads((ROOT/name).read_text())
s=data('sweep_summary.json'); ext=data('physics_extensions.json');d=data('derived_checks.json')
assert s['model_count']+ext['additional_models']==64
assert s['pair_count']+ext['additional_equal_dimension_pairs']==632
assert max(s['max_TP_error'],ext['max_TP_error'],s['max_probability_sum_error'])<1e-11
for r in s['ordinary_commutator_checks']:
    assert r['projector_error']<1e-11 and r['max_ordinary_probability_error']<1e-11 and r['max_qubit_gram_error']<1e-11
assert max(d['max_PCS_identity_residual'],d['max_entanglement_fidelity_weight_identity_error'],d['max_one_visible_projector_ABA_error'])<1e-11
assert all(x['CCdagger_identity'] for x in d['exact_commutator_operator'])
assert all(abs(x['norm_squared']-2)<1e-11 for x in d['single_site_error_spans'])
q=data('qec_results.json');polys=data('qec_polynomials.json')
assert len(q['cases'])==43 and q['max_recovery_signal_error']<1e-11
for row in q['cases']:
    assert row['F_with_switch_flag']+1e-11>=row['F_final_only']
for pp in polys:
    ref=next(x for x in q['cases'] if x['code']=='perfect5' and x['noise']==pp['noise'] and x['p']==.01)
    for key,column in [('final','serial_logical_error'),('flag','switch_logical_error'),('intermediate','intermediate_logical_error')]:
        assert abs(pp['values_at_0.01'][key]-ref[column])<1e-11
m=data('magic_scan.json');f=data('reset_factory.json');rare=data('rare_fault_baseline.json')
assert m['tested']==4332 and m['positive_cases']==288
assert f['symbolic_formula'] and f['max_formula_residual']<1e-11
assert rare['max_formula_error']<1e-11 and rare['unknown_axis_example']['total_error_upper_bound']<.01
for r in data('ordinary_compilation.json')['checks']:
    assert max(r['max_Bell_sampling_error'],r['max_full_switch_Choi_error'])<1e-11
rp=data('recovery_policy.json');assert rp['max_error']<1e-11 and rp['different_decoder_verified']
gkp=data('gkp_flag.json');assert len(gkp['cases'])==14
for r in gkp['cases']:
    assert r['normalization_error']<1e-10 and r['p_minus_error']<1e-10
    assert r['flag_error']<=r['ordinary_error']+1e-10
    assert abs(r['ordinary_error']-r['ordinary_error_exact'])<1e-5
    if 'grid_error_estimate' in r:assert r['grid_error_estimate']<1e-5
files={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(ROOT.iterdir())
       if p.is_file() and p.name!='validation.json' and p.suffix in ['.py','.md','.csv','.json','.txt']}
import numpy,scipy,sympy,mpmath
report={'checked_utc':datetime.now(timezone.utc).isoformat(),'status':'passed',
'python':platform.python_version(),'packages':{k:v.__version__ for k,v in [('numpy',numpy),('scipy',scipy),('sympy',sympy),('mpmath',mpmath)]},
'runs':runs,'base_models':64,'pairings':632,'QEC_configurations':43,'magic_output_cases':4332,'GKP_cases':14,
'scope':'Rational/symbolic identities, finite Pauli-history enumeration, and seeded numerical regressions. Not an external proof audit, an optimal-strategy theorem beyond stated analytical constructions, a physical switch validation, or a circuit-level fault-tolerance threshold.',
'source_hashes':files}
(ROOT/'validation.json').write_text(json.dumps(report,indent=2));print('All checks passed; validation.json written.')
