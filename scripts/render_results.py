"""Generate result navigation from canonical ownership metadata, without copying claims."""
import argparse
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

def render():
    registry=json.loads((ROOT/'research/results.json').read_text(encoding='utf-8'))
    topics=json.loads((ROOT/'research/status.json').read_text(encoding='utf-8'))['topics']
    lines=['# Current results','',
           'Each entry identifies one canonical mathematical result or scoped finding. Follow its source for the statement, assumptions, proof, and limits. This page is generated from `results.json`; it does not maintain alternate statements.','',
           '[Research map](README.md) · [Ownership conventions](../docs/STRUCTURE.md)','']
    for topic in topics:
        lines+=['## '+topic['id']+' — '+topic['title'],'','| ID | Result owner | Location within source |','| --- | --- | --- |']
        for r in registry['results']:
            if r['topic']!=topic['id']:
                continue
            label=r['title'].replace('|','\\|')
            locator=r.get('locator','').replace('|','\\|')
            lines.append(f"| {r['id']} | [{label}](../{r['canonical_path']}) | {locator} |")
        lines+=['']
    return '\n'.join(lines).rstrip()+'\n'

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    path=ROOT/'research/RESULTS.md'
    expected=render()
    if args.check:
        if not path.exists() or path.read_text(encoding='utf-8')!=expected:
            raise SystemExit('Result index is stale: run python scripts/render_results.py')
        print('PASS: result index matches canonical ownership metadata')
    else:
        path.write_text(expected,encoding='utf-8',newline='\n')
        print('Updated current result navigation')

if __name__=='__main__':
    main()
