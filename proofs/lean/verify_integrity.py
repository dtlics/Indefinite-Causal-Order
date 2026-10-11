"""Check proof sources against the recorded verification state (not a Lean proof check)."""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parent
closure = json.loads((root / 'audit/closure.json').read_text(encoding='utf-8'))
manifest = json.loads((root / 'audit/entry-hashes.json').read_text(encoding='utf-8'))
expected = {}
for module in closure['modules']:
    name = module['name']
    prefix = 'vendor/Lean-QIT/' if name.startswith('QIT.') else ''
    expected[prefix + name.replace('.', '/') + '.lean'] = module['sha256']
for name in ('ICO.lean', 'Audit.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json'):
    expected[name] = manifest[name]
actual = {p.relative_to(root).as_posix() for folder in ('ICO', 'vendor/Lean-QIT/QIT')
          for p in (root / folder).rglob('*.lean')}
module_paths = {name for name in expected if name not in ('ICO.lean', 'Audit.lean') and name.endswith('.lean')}
if actual != module_paths:
    raise SystemExit('Proof-module layout differs from recorded state: ' + str(sorted(actual ^ module_paths)))
for name, digest in expected.items():
    path = (root / name).resolve()
    if not path.is_relative_to(root) or not path.is_file():
        raise SystemExit('Missing or invalid recorded state path: ' + name)
    if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
        raise SystemExit('Recorded-state hash mismatch: ' + name)
print(f'PASS: {len(closure["modules"])} proof modules, both entry files, and dependency configuration match the recorded verification state.')
print('This checks source identity; it does not rerun Lean or validate repository documentation.')
