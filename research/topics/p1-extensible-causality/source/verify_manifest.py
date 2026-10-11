#!/usr/bin/env python3
from pathlib import Path
import hashlib
root=Path(__file__).resolve().parent
lines=(root/'MANIFEST_SHA256.txt').read_text().splitlines()
for line in lines:
    digest,name=line.split('  ',1)
    path=root/name
    assert path.is_file(),name
    assert hashlib.sha256(path.read_bytes()).hexdigest()==digest,name
print(f'PASS: {len(lines)} file hashes')
