"""Index the current selected Lean import closure without running Lean or Git."""
from __future__ import annotations

from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent
MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")


def code_only(text: str) -> str:
    """Blank strings and nested Lean comments, retaining newlines."""
    out = list(text)
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            width = 2 if text[i:i + 2] in ('/-', '-/') else 1
            if text[i:i + 2] == '/-':
                depth += 1
            elif text[i:i + 2] == '-/':
                depth -= 1
        elif string:
            width = 2 if text[i] == '\\' and i + 1 < len(text) else 1
            if text[i] == '"':
                string = False
        elif text[i:i + 2] == '--':
            end = text.find('\n', i)
            width = (len(text) if end < 0 else end) - i
        elif text[i:i + 2] == '/-':
            depth = 1
            width = 2
        elif text[i] == '"':
            string = True
            width = 1
        else:
            i += 1
            continue
        for j in range(i, i + width):
            if text[j] != '\n':
                out[j] = ' '
        i += width
    if depth or string:
        raise ValueError('Unterminated comment or string in Lean source.')
    return ''.join(out)


def imports(path: Path) -> list[str]:
    found = []
    for line in code_only(path.read_text(encoding='utf-8-sig')).splitlines():
        match = re.match(r'^\s*(?:(?:public|meta)\s+)*import\b(.*)$', line)
        if match:
            names = match[1].split()
            if not names or any(not MODULE.fullmatch(name) for name in names):
                raise ValueError(f'Unsupported import syntax in {path}: {line.strip()}')
            found.extend(names)
    return list(dict.fromkeys(found))


def local_path(root: Path, name: str) -> Path | None:
    if name == 'ICO' or name.startswith('ICO.'):
        return root / (name.replace('.', '/') + '.lean')
    if name == 'QIT' or name.startswith('QIT.'):
        return root / 'vendor/Lean-QIT' / (name.replace('.', '/') + '.lean')
    return None


def prepare(root: Path) -> tuple[dict, dict]:
    roots = list(dict.fromkeys(imports(root / 'ICO.lean') + imports(root / 'Audit.lean')))
    modules = {}
    order = []
    active = set()
    external = set()

    def visit(name: str) -> None:
        path = local_path(root, name)
        if path is None:
            external.add(name)
            return
        if name in active:
            raise ValueError('Local import cycle at ' + name)
        if name in modules:
            return
        if not path.is_file():
            raise ValueError('Missing local source for ' + name + ': ' + str(path))
        active.add(name)
        data = path.read_bytes()
        dependencies = imports(path)
        for dependency in dependencies:
            visit(dependency)
        active.remove(name)
        modules[name] = {'name': name, 'imports': dependencies,
                         'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}
        order.append(name)

    for name in roots:
        visit(name)
    audit = code_only((root / 'Audit.lean').read_text(encoding='utf-8-sig'))
    declarations = re.findall(r'^\s*#print\s+axioms\s+(\S+)\s*$', audit, re.MULTILINE)
    if not declarations or len(declarations) != len(set(declarations)):
        raise ValueError('Audit.lean must contain a nonempty, unique list of #print axioms declarations.')
    if any(not MODULE.fullmatch(name) for name in declarations):
        raise ValueError('Unsupported declaration name in Audit.lean.')
    config_files = ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
                    'vendor/Lean-QIT/lakefile.toml', 'vendor/Lean-QIT/lake-manifest.json',
                    'vendor/Lean-QIT/lean-toolchain', 'prepare_verification.py', 'verify.ps1', 'verify.sh')
    config = hashlib.sha256()
    for name in config_files:
        config.update(name.encode('utf-8') + b'\0' + (root / name).read_bytes() + b'\0')
    closure = {'status': 'Prepared from current source; not yet built or kernel-audited.',
               'roots': roots, 'order': order, 'modules': [modules[name] for name in order],
               'external': sorted(external), 'configuration_sha256': config.hexdigest()}
    return closure, {'declarations': declarations}


def validate_axioms(text: str, expected: list[str]) -> None:
    reports = re.findall(
        r"^'([^'\r\n]+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))",
        text, re.MULTILINE)
    if [name for name, _, _ in reports] != expected:
        raise ValueError('Axiom report names/order differ from the current Audit.lean endpoints.')
    for name, axioms, _ in reports:
        found = {axiom.strip() for axiom in axioms.split(',') if axiom.strip()}
        unexpected = found - {'propext', 'Classical.choice', 'Quot.sound'}
        if unexpected:
            raise ValueError(f'Unexpected axioms for {name}: {sorted(unexpected)}')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-audit', type=Path,
                        help='Check an audit log against the already prepared current endpoints.')
    args = parser.parse_args()
    if args.check_audit:
        expected = json.loads((ROOT / '_build/verification/theorem-roots.json').read_text(encoding='utf-8'))
        data = args.check_audit.read_bytes()
        text = data.decode('utf-16' if data.startswith((b'\xff\xfe', b'\xfe\xff')) else 'utf-8-sig')
        validate_axioms(text, expected['declarations'])
        print(f'PASS: {len(expected["declarations"])} current endpoint reports contain only allowed axioms.')
        return
    closure, theorems = prepare(ROOT)
    output = ROOT / '_build/verification'
    output.mkdir(parents=True, exist_ok=True)
    for name, data in (('closure.json', closure), ('theorem-roots.json', theorems)):
        (output / name).write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8')
    (output / 'source-order.txt').write_bytes(('\n'.join(closure['order']) + '\n').encode('utf-8'))
    print(f'Prepared {len(closure["modules"])} local modules and {len(theorems["declarations"])} endpoints from current source.')
    print('External imports are resolved by the pinned Lake environment during the build; no compiled-object fallback is used for missing ICO/QIT sources.')


if __name__ == '__main__':
    main()
