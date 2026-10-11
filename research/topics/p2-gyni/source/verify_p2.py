#!/usr/bin/env python3
"""Portable P2 checks. No option: hashes/scope only. --core: exact bounds. --all: exact structural checks too."""
from pathlib import Path
from fractions import Fraction
import argparse,hashlib,json,os,subprocess,sys,tempfile,shutil
ROOT=Path(__file__).resolve().parent

def integrity():
 count=0
 for line in (ROOT/'SHA256SUMS.txt').read_text().splitlines():
  digest,name=line.split('  ',1);p=ROOT/name
  assert p.is_file(),name
  assert hashlib.sha256(p.read_bytes()).hexdigest()==digest,name
  count+=1
 b=json.loads((ROOT/'CERTIFIED_BOUNDS.json').read_text());s=ROOT/'support'
 lo=json.loads((s/'objective/endpoint_lower1653.json').read_text())
 up=json.loads((s/'word-kernels/rational_L8_r004_certificate183.json').read_text())
 old=json.loads((s/'objective/Radau5_fixed_upper165.json').read_text())
 F=Fraction;a=F(lo['GYNI_lower_rational']);z=F(up['upper_rational']);o=F(old['upper_rational'])
 assert a==F(b['lower_rational']) and z==F(b['upper_rational'])
 assert F(b['outward_lower_decimal'])<=a<z<=F(b['outward_upper_decimal'])
 assert lo['rational_tangent_pairs'][:-1]==old['rational_tangent_pairs']
 assert lo['rational_tangent_pairs'][-1]==[1,0] and o<a
 assert not b['unrestricted_exact_value_proved'] and not b['unrestricted_finite_attainment_proved']
 print('PASS: hashes, exact rational interval, outward rounding, support separation and WIP scope;',count,'files')

def replay(all_checks):
 report=json.loads((ROOT/'REPLAY_COMMANDS.json').read_text())
 jobs=report['certificate_replays']+(report['structural_exact_checks'] if all_checks else [])
 with tempfile.TemporaryDirectory(prefix='p2_clean_replay_') as tmp:
  root=Path(tmp)/'P2';shutil.copytree(ROOT,root);cwd=root/'support'
  env={**os.environ,'PYTHONPATH':'','PYTHONDONTWRITEBYTECODE':'1','OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1'}
  for j in jobs:
   args=[sys.executable,*j['command'][1:]]
   p=subprocess.run(args,cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
   if p.returncode:
    print(p.stdout);raise RuntimeError('Failed: '+j['name'])
   print('PASS:',j['name'],flush=True)
 print('PASS: all requested exact replays; no solver used')

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--core',action='store_true');p.add_argument('--all',action='store_true');a=p.parse_args();integrity()
 if a.core or a.all:replay(a.all)
