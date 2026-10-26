"""Compile the canonical manuscript and save a PDF with its source fingerprint."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'paper/main.tex'
BUILD = ROOT / '_build/paper'
DESTINATION = ROOT / 'dist'


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    compiler = shutil.which('pdflatex')
    if compiler is None:
        raise SystemExit('Install pdfLaTeX (TeX Live or MiKTeX), then run this script again.')
    BUILD.mkdir(parents=True, exist_ok=True)
    DESTINATION.mkdir(parents=True, exist_ok=True)
    command = [compiler, '-no-shell-escape', '-halt-on-error',
               '-interaction=nonstopmode', f'-output-directory={BUILD}', SOURCE.name]
    previous_aux = None
    for number in range(1, 5):
        result = subprocess.run(command, cwd=SOURCE.parent, capture_output=True, text=True,
                                errors='replace')
        (BUILD / f'pass-{number}.txt').write_text(result.stdout + result.stderr, encoding='utf-8')
        if result.returncode:
            raise SystemExit(f'pdfLaTeX failed on pass {number}. See {BUILD / f"pass-{number}.txt"}')
        log = (BUILD / 'main.log').read_text(encoding='utf-8', errors='replace')
        auxiliary = sha256(BUILD / 'main.aux')
        rerun = re.search(r'Rerun to get|Rerun LaTeX|Label\(s\) may have changed', log)
        if number >= 2 and auxiliary == previous_aux and not rerun:
            break
        previous_aux = auxiliary
    else:
        raise SystemExit(f'References did not settle after four passes. See {BUILD / "main.log"}')
    issues = re.findall(r'^.*(?:undefined|Overfull \\[hv]box|Underfull \\[hv]box).*$',
                        log, flags=re.MULTILINE | re.IGNORECASE)
    if issues:
        raise SystemExit('PDF checks failed:\n' + '\n'.join(issues))
    pdf = DESTINATION / 'quantum-switch-paper.pdf'
    shutil.copyfile(BUILD / 'main.pdf', pdf)
    version = subprocess.run([compiler, '--version'], capture_output=True, text=True,
                             errors='replace', check=True).stdout.splitlines()[0]
    info = {
        'source': SOURCE.relative_to(ROOT).as_posix(),
        'source_sha256': sha256(SOURCE),
        'pdf': pdf.name,
        'pdf_sha256': sha256(pdf),
        'compiler': version,
        'passes': number,
        'checks': 'No undefined references, overfull boxes, or underfull boxes in the final log.',
        'scope': 'Compilation checks do not verify the mathematical claims.',
    }
    (DESTINATION / 'paper-build.json').write_text(json.dumps(info, indent=2) + '\n', encoding='utf-8')
    print(f'{pdf}\nSource SHA-256 {info["source_sha256"]}\n{info["checks"]}')


if __name__ == '__main__':
    main()
