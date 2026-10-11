"""Replay canonical exact certificates without overwriting imported evidence."""
from pathlib import Path
import os
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
if sys.version_info < (3, 9):
    raise SystemExit('Python 3.9 or newer is required.')
if not __debug__ or sys.flags.optimize:
    raise SystemExit('Assertions must be enabled: rerun without -O or -OO.')

output = ROOT.parent / '_build' / 'exact'
output.mkdir(parents=True, exist_ok=True)
inputs = ('integer_support_constraints.json', 'support_left_inverse.json',
          'modular_support_inverse.json', 'short_dual_relations.json',
          'verify_support_exact.py', 'verify_short_certificate.py')
for name in inputs:
    shutil.copy2(ROOT / name, output / name)
env = dict(os.environ)
env.pop('PYTHONOPTIMIZE', None)
for script in ('verify_support_exact.py', 'verify_short_certificate.py'):
    result = subprocess.run([sys.executable, str(output / script)], cwd=output,
                            env=env, check=True, capture_output=True, text=True)
    (output / (script + '.log')).write_text(result.stdout + result.stderr,
                                         encoding='utf-8')
    print(result.stdout, end='')
print('PASS: both exact finite certificates replayed from canonical data.')
print('Fresh reports: ' + str(output))
