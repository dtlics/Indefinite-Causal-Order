"""One-shot, hash-verified integration of the requested conversation sources.
Removed from the final source tree after successful validation.
"""
from __future__ import annotations
import base64, hashlib, json, lzma, os, subprocess, sys, urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
PREFIX='research/topics/nr-noisy-recovery/application-search/'
APP=ROOT/PREFIX
BLOBS=[
'a8cb537bd7976fffa715b5880a642d835e9f020a',
'cf1d14fa2a329e0010b313e0996b7fe945239650',
'ea97e19ff9b0413c470855d6106d6220e8191e30',
'0b35d3847c4470a1bad7b0380f1ca1f193ae4b1d',
'26f5115a3f105e68af8a87b0c670225a8ba664ea',
'6431c32aaa3d150284d06e1d10a4b73a4250a144',
'e9dedf4ec3336e63db6b091a2399a86e8ab449af',
'7a238dac16bb65278a94ab235bfb94225146ecd9',
'dfcad707cf8d3ac44a2d54d6a7384a9de10b1cb8']
repo='dtlics/Indefinite-Causal-Order'
assert os.environ.get('GITHUB_REPOSITORY',repo)==repo
chunks=[]
for sha in BLOBS:
 req=urllib.request.Request(f'https://api.github.com/repos/{repo}/git/blobs/{sha}',headers={'Authorization':'Bearer '+os.environ['GH_TOKEN'],'Accept':'application/vnd.github+json','User-Agent':'application-search-integration'})
 with urllib.request.urlopen(req,timeout=60) as response:
  record=json.load(response)
 assert record['encoding']=='base64'
 chunk=base64.b64decode(record['content'])
 assert hashlib.sha1(b'blob '+str(len(chunk)).encode()+b'\0'+chunk).hexdigest()==sha
 chunks.append(chunk)
compressed=base64.b64decode(b''.join(chunks),validate=True)
assert hashlib.sha256(compressed).hexdigest()=='db69f148fc0c7a7e87502e066d464cdf39bf7259745473df146ec97f1bcf5d00'
raw=lzma.decompress(compressed)
assert len(raw)==194130
assert hashlib.sha256(raw).hexdigest()=='80f9da503f968120111e5d64b28c7277a1e835877c3de8702778ea8230c388a7'
files=json.loads(raw)
assert len(files)==23
for name,content in files.items():
 target=(ROOT/name).resolve()
 assert name.startswith(PREFIX) and target.is_relative_to(APP.resolve())
 assert isinstance(content,str)
 target.parent.mkdir(parents=True,exist_ok=True)
 target.write_text(content,encoding='utf-8')
print('Materialized 23 hash-verified source files; no package blobs added to checkout.',flush=True)
# Keep the previously existing registry entries exactly as records; append owners.
path=ROOT/'research/results.json'
registry=json.loads(path.read_text(encoding='utf-8-sig'))
original=list(registry['results'])
rows=[
(23,'Matched-fidelity noise-model validation and conditional weak-noise scaling','model-validation.md',[('uses','C5-R02'),('qualified-by','NR-R25')]),
(24,'Exact finite two-call matched-fidelity discrimination certificate','finite-query.md',[('finite-case-of','NR-R23')]),
(25,'Finite-family and product-local ordinary model-validation baselines','ordinary-baselines.md',[('qualifies','NR-R23'),('qualifies','C6-R05')]),
(26,'Eigenbasis susceptibility identity and ordinary OTOC compilation boundaries','spectral-sensitivity.md',[('related-to','C6-R04'),('qualified-by','NR-R06')]),
(27,'Finite Bell-pair delivery under a declared standard-network cut','network-service.md',[('related-to','NR-R10')]),
(28,'Qubit central-polynomial recovery and scoped ordinary-code counterexamples','algebraic-recovery.md',[('related-to','NR-R06')]),
(29,'Bare order-geometry closure, finite activation certificates and modular ledgers','order-geometry.md',[('uses','NR-R28')]),
(30,'Finite verification games derived from existing query bounds','finite-games.md',[('numerical-corollary-of','C5-R02'),('game-corollary-of','C4-R01')])]
for number,title,file,relations in rows:
 identity=f'NR-R{number:02}'
 item={'id':identity,'topic':'NR','title':title,'canonical_path':PREFIX+file+'#'+identity.lower(),'relationships':[{'type':t,'target':r} for t,r in relations]}
 matches=[r for r in registry['results'] if r['id']==identity]
 if matches:
  assert matches==[item],f'Result ID conflict: {identity}'
 else: registry['results'].append(item)
assert registry['results'][:len(original)]==original
path.write_text(json.dumps(registry,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')

def insert_section(filename,marker,text):
 p=ROOT/filename
 s=p.read_text(encoding='utf-8-sig')
 if marker in s:return
 first,sep,rest=s.partition('\n')
 p.write_text(first+'\n\n'+text.strip()+'\n\n'+rest.lstrip('\n'),encoding='utf-8')

insert_section('README.md','Natural-black-box application-search handoff','''## Natural-black-box application-search handoff

The [current application investigation](research/topics/nr-noisy-recovery/application-search/README.md) organizes the model-validation results, ordinary baselines, exact certificates and secondary recovery/order-geometry work. The original goal remains a substantial advantage in a natural black-box quantum-computing or QEC workload; that application is not claimed complete. See the handoff before resuming exploration.''')
insert_section('research/topics/nr-noisy-recovery/README.md','Current application-search handoff','''## Current application-search handoff

[Investigation entry and scope](application-search/README.md) owns the navigation for NR-R23 through NR-R30. It preserves the model-validation and OTOC derivations, finite-family/product-local ordinary baselines, finite-query certificates and secondary communication/algebra/order-geometry findings. The latest direction is to return to naturally occurring black boxes in quantum computing/QEC; the later detours do not replace that objective. The manuscript and Lean tree are unchanged by this integration.''')
insert_section('research/topics/nr-noisy-recovery/architecture.md','Application-search synchronization','''## Application-search synchronization

The [current application-search handoff](application-search/README.md) records the additional derivations and ordinary baselines from the conversation. Recovery and order-geometry findings are retained as secondary results, not a completed practitioner application. Their evidence and limitations are separated from the existing results below.''')
insert_section('docs/VALIDATION.md','Application-search checks','''## Application-search checks

The [application-search check suite](../research/topics/nr-noisy-recovery/application-search/checks/README.md) has a single [current record](../research/topics/nr-noisy-recovery/application-search/checks/validation.json). It distinguishes exact rational certificates, restricted symbolic searches and seeded numerical tests. It does not independently audit C4/C5/C6/P3, establish publication priority, verify a physical switch interface or perform a Lean rebuild. Sources and source-attachment hashes are retained without importing duplicate generated archives.''')
for script in ['render_research_index.py','render_results.py']:
 subprocess.run([sys.executable,str(ROOT/'scripts'/script)],cwd=ROOT,check=True)
subprocess.run([sys.executable,'research/topics/nr-noisy-recovery/application-search/checks/run.py','--record'],cwd=ROOT,check=True)
subprocess.run([sys.executable,'scripts/validate_repo.py'],cwd=ROOT,check=True)
# Temporary materialization machinery is not part of the final research source.
(ROOT/'.github/workflows/integrate-application-search.yml').unlink()
Path(__file__).unlink()
print('Integration complete: registry preserved, 13 check groups passed, navigation validated.',flush=True)
