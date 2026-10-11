#!/usr/bin/env python3
"""Render the research index table from its sole status registry, or check drift."""
from pathlib import Path
import argparse
import json

ROOT = Path(__file__).resolve().parents[1]
START = '<!-- BEGIN GENERATED RESEARCH STATUS -->'
END = '<!-- END GENERATED RESEARCH STATUS -->'


def render_table(registry):
    rows = ['| ID | Topic | Recorded state |', '| --- | --- | --- |']
    seen = set()
    for topic in registry['topics']:
        assert topic['id'] not in seen, f"Duplicate topic ID: {topic['id']}"
        seen.add(topic['id'])
        path = (ROOT / 'research' / topic['dossier']).resolve()
        assert path.is_relative_to((ROOT / 'research').resolve()) and path.is_file(), topic['dossier']
        values = [topic[key] for key in ('id', 'title', 'status', 'qualification')]
        assert all('|' not in value and '\n' not in value for value in values)
        rows.append(f"| {topic['id']} | [{topic['title']}]({topic['dossier']}) | {topic['status']}: {topic['qualification']} |")
    return '\n'.join(rows)


def expected_index():
    registry = json.loads((ROOT / 'research/status.json').read_text(encoding='utf-8'))
    source = (ROOT / 'research/README.md').read_text(encoding='utf-8')
    assert source.count(START) == source.count(END) == 1, 'Missing or repeated generated-table markers'
    before, remainder = source.split(START, 1)
    _, after = remainder.split(END, 1)
    return before + START + '\n' + render_table(registry) + '\n' + END + after


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='Fail instead of rewriting if the table differs.')
    args = parser.parse_args()
    path = ROOT / 'research/README.md'
    expected = expected_index()
    if args.check:
        if path.read_text(encoding='utf-8') != expected:
            raise SystemExit('Research index is stale. Run python scripts/render_research_index.py after editing research/status.json.')
        print('PASS: research index matches research/status.json')
    else:
        path.write_text(expected, encoding='utf-8')
        print('Updated research index from research/status.json')


if __name__ == '__main__':
    main()
