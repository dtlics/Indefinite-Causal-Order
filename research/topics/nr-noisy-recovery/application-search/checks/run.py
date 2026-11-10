#!/usr/bin/env python3
"""Replay scoped certificates and numerical checks in an ignored build directory."""
from __future__ import annotations
import argparse, hashlib, importlib.metadata, json, os, platform, shutil
import subprocess, sys, time
from datetime import datetime, timezone
from pathlib import Path
HERE=Path(__file__).resolve().parent
TOP=HERE.parent
ROOT=HERE.parents[4]
JOBS=[
 ('model','verify_results.py','numerical identities'),
 ('finite-query','certify_two_call.py','exact rational certificate'),
 ('baselines','check_identities.py','numerical identities'),
 ('baselines','check_finite_family.py','numerical identities; published threshold theorem not reproved'),
 ('finite-games','check_constants.py','exact finite-parameter substitutions'),
 ('network','check.py','exact finite ledgers and code; analytic converse not reproved'),
 ('algebra','explore.py','seeded numerical exploration'),
 ('algebra','polynomial_search.py','exact symbolic search in a specified ansatz'),
 ('algebra','verify_extensions.py','symbolic identities and numerical checks'),
 ('orders','exact_certificates.py','exact rational finite-order certificates'),
 ('orders','qubit_optimum.py','exact symbolic order-only optimum'),
 ('orders','modular_protocol.py','exact probability ledgers'),
 ('orders','verify_extra.py','symbolic recursion and numerical cross-checks'),
]
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--group',choices=sorted({j[0] for j in JOBS}))
 ap.add_argument('--record',action='store_true')
 ap.add_argument('--timeout',type=int,default=600)
 args=ap.parse_args()
 if args.record and args.group:ap.error('--record requires the complete suite')
 work=ROOT/'_build'/'application-search';work.mkdir(parents=True,exist_ok=True)
 for group in sorted({j[0] for j in JOBS if not args.group or j[0]==args.group}):
  dest=work/group
  if dest.exists():shutil.rmtree(dest)
  shutil.copytree(HERE/group,dest,ignore=shutil.ignore_patterns('__pycache__'))
 env=dict(os.environ,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1')
 env={k:v for k,v in env.items() if not any(s in k.upper() for s in ('TOKEN','SECRET','PASSWORD'))}
 checks=[]
 for group,script,evidence in JOBS:
  if args.group and group!=args.group:continue
  start=time.monotonic()
  try:
   p=subprocess.run([sys.executable,script],cwd=work/group,env=env,capture_output=True,text=True,timeout=args.timeout)
   code,out,err=p.returncode,p.stdout,p.stderr
  except subprocess.TimeoutExpired as e:
   code,out,err=124,str(e.stdout or ''),'Timeout exceeded'
  (work/group/(script+'.log')).write_text(out+'\n'+err,encoding='utf-8')
  checks.append(dict(group=group,script=script,evidence=evidence,returncode=code,seconds=round(time.monotonic()-start,3)))
  print(('PASS' if code==0 else 'FAIL')+': '+group+'/'+script,flush=True)
  if code:print(err[-2500:] or out[-2500:],flush=True)
 versions={}
 for name in ('numpy','scipy','sympy','threadpoolctl'):
  try:versions[name]=importlib.metadata.version(name)
  except importlib.metadata.PackageNotFoundError:versions[name]='unavailable'
 hashes={str(p.relative_to(TOP)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(TOP.rglob('*')) if p.is_file() and '__pycache__' not in p.parts and p.name!='validation.json'}
 report=dict(checked_utc=datetime.now(timezone.utc).isoformat(),python=platform.python_version(),platform=platform.platform(),packages=versions,status='passed' if all(c['returncode']==0 for c in checks) else 'failed',checks=checks,input_sha256=hashes,scope=['Finite rational/symbolic checks establish only their stated bounded certificates.','Seeded numerical cases are debugging evidence, not all-instance proofs.','No independent C4/C5/C6/P3 proof audit, Lean rebuild, physical-interface verification or priority review was performed.','Generated scans and optimizer intermediates are not checked-in source dependencies.'])
 (work/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
 if args.record and report['status']=='passed':(HERE/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
 return int(report['status']!='passed')
if __name__=='__main__':raise SystemExit(main())
