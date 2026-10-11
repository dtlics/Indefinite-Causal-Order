"""Check current-knowledge ownership, generated indexes, and navigation."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
from urllib.parse import unquote

ROOT = Path(__file__).resolve().parents[1]

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--proof-integrity', action='store_true', help='Compare Lean source to its current verification fingerprints')
    args = parser.parse_args()
    errors = []
    required = ['README.md','CONTRIBUTING.md','paper/main.tex','paper/README.md',
                'research/status.json','research/results.json','research/README.md','research/RESULTS.md',
                'proofs/lean/THEOREMS.txt','proofs/lean/README.md','docs/VALIDATION.md']
    for name in required:
        if not (ROOT/name).is_file():
            errors.append('Missing canonical file: '+name)
    for name in ('history','provenance','source-bundle'):
        if (ROOT/name).exists() and any(p.is_file() for p in (ROOT/name).rglob('*')):
            errors.append('Current knowledge must not contain a checkpoint/archive tree: '+name)
    if (ROOT/'scripts/archive.py').exists():
        errors.append('Archive retrieval is not part of the current-knowledge repository')
    for name in ('paper.tex','paper/paper.tex'):
        if (ROOT/name).exists():
            errors.append('Use paper/main.tex as the single manuscript source')

    status_path=ROOT/'research/status.json'
    topics=[]
    if status_path.exists():
        topics=json.loads(status_path.read_text(encoding='utf-8'))['topics']
        if len({t['id'] for t in topics})!=len(topics):
            errors.append('Duplicate stable topic IDs')
        for t in topics:
            p=(ROOT/'research'/t['dossier']).resolve()
            if not p.is_relative_to(ROOT/'research/topics') or not p.is_file():
                errors.append('Missing dossier for '+t['id'])

    records=[]
    result_path=ROOT/'research/results.json'
    if result_path.exists():
        records=json.loads(result_path.read_text(encoding='utf-8'))['results']
        ids=[r['id'] for r in records]
        owners=[]
        for r in records:
            if r['topic'] not in {t['id'] for t in topics}:
                errors.append('Unknown topic for '+r['id'])
            target=r['canonical_path'].split('#',1)[0]
            p=(ROOT/target).resolve()
            if not p.is_relative_to(ROOT) or not p.is_file():
                errors.append('Missing canonical result source: '+r['id']+' -> '+target)
            else:
                source=p.read_text(encoding='utf-8-sig')
                anchor=r['canonical_path'].partition('#')[2]
                if anchor and p.suffix=='.md':
                    explicit=re.findall(r'<a\s+(?:id|name)=[\"\']([^\"\']+)[\"\']',source)
                    headings=[]
                    for heading in re.findall(r'^#+\s+(.+)',source,re.M):
                        headings.append(re.sub(r'[^\w\- ]','',heading.lower()).replace(' ','-'))
                    if anchor not in explicit+headings:
                        errors.append('Missing result anchor: '+r['id']+' -> '+anchor)
                locator=r.get('locator','')
                if locator.startswith('LaTeX label: '):
                    label=locator.removeprefix('LaTeX label: ')
                    if '\\label{'+label+'}' not in source:
                        errors.append('Missing LaTeX result label: '+r['id'])
            owners.append((r['canonical_path'],r.get('locator','')))
            for relation in r.get('relationships',[]):
                if relation['target'] not in ids:
                    errors.append('Unknown related result: '+r['id']+' -> '+relation['target'])
        if len(ids)!=len(set(ids)):
            errors.append('Duplicate result IDs')
        if len(owners)!=len(set(owners)):
            errors.append('Multiple result IDs claim the same exact source/locator; consolidate or distinguish their scopes')

    for script in ('render_research_index.py','render_results.py'):
        if (ROOT/'scripts'/script).is_file() and status_path.exists() and result_path.exists():
            result=subprocess.run([sys.executable,str(ROOT/'scripts'/script),'--check'],capture_output=True,text=True)
            if result.returncode:
                errors.append('Generated index is stale or invalid: python scripts/'+script)

    maintained=[p for p in ROOT.rglob('*.md') if not any(x in p.relative_to(ROOT).parts for x in ('.git','_build','dist','vendor'))]
    links=0
    for path in maintained:
        content=re.sub(r'```.*?```','',path.read_text(encoding='utf-8-sig'),flags=re.S)
        content=re.sub(r'`+[^`]*`+','',content)
        content=re.sub(r'\\\[.*?\\\]|\$\$.*?\$\$','',content,flags=re.S)
        for match in re.finditer(r'(?<!\\)\[[^\]]*\]\(([^\s)]+)(?:\s+"[^"]*")?\)',content):
            target=match.group(1).strip('<>')
            if target.startswith(('#','http:','https:','mailto:')):
                continue
            target=unquote(target.split('#',1)[0])
            if not target:
                continue
            links+=1
            if not (path.parent/target).exists():
                errors.append(f'Broken link: {path.relative_to(ROOT)} -> {target}')
    if args.proof_integrity:
        result=subprocess.run([sys.executable,'verify_integrity.py'],cwd=ROOT/'proofs/lean',capture_output=True,text=True)
        print(result.stdout.strip())
        if result.returncode:
            errors.append('Proof fingerprints differ; check current verification scope')
    if errors:
        for error in sorted(set(errors)):
            print('ERROR:',error)
        return 1
    print(f'PASS: {len(topics)} topics, {len(records)} canonical result owners, {links} local links; current-knowledge layout.')
    return 0

if __name__=='__main__':
    raise SystemExit(main())
