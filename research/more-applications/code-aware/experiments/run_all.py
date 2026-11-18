"""Run the current research checks; record evidence scope and source hashes."""
from pathlib import Path
import sys,subprocess,time,json,os,hashlib,platform,datetime
import numpy, scipy
ROOT=Path(__file__).resolve().parent
os.chdir(ROOT)
logs=ROOT/'_build';logs.mkdir(exist_ok=True)
scripts=[
 ('retraction_tests.py','floating-point full-channel regression; analytical proof in note'),
 ('structured_bounds.py','exact integer support counts and numerical overlap identities'),
 ('nonpauli_qec.py','numerical noise-adapted QEC screening'),
 ('bosonic_screen.py','numerical finite-level oscillator screening, not an infinite-dimensional bound'),
 ('decoder_screen.py','numerical SDP primal/dual feasibility and exact-algebra DFS regression'),
 ('program_and_code.py','full-channel program/compiler and code-algebra regression'),
 ('self_switch_bound.py','analytical identity regression and numeric comparisons'),
 ('summarize.py','published recovery inequality applied to numerical fidelities')]
env=dict(os.environ,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1')
records=[]
for script,scope in scripts:
    t=time.monotonic()
    with open(logs/(script+'.log'),'w') as f:
        p=subprocess.run([sys.executable,script],env=env,stdout=f,stderr=subprocess.STDOUT)
    records.append({'script':script,'scope':scope,'returncode':p.returncode,'seconds':round(time.monotonic()-t,3)})
    print(script,p.returncode,flush=True)
    if p.returncode:raise SystemExit('FAILED:'+script)
record={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'python':sys.version.split()[0],
 'numpy':numpy.__version__,'scipy':scipy.__version__,'platform':platform.platform(),'status':'passed','checks':records,
 'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in ROOT.glob('*.py')},
 'scope':'Finite regression/optimization evidence. Not an independent proof audit, literature-priority check, physical interface verification, or fault-tolerance threshold.'}
(ROOT/'validation.json').write_text(json.dumps(record,indent=2)+'\n')
print('ALL CHECKS PASSED',flush=True)
