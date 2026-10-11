"""Build a deterministic Overleaf ZIP from the one canonical paper source."""
import hashlib
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parents[1]
output = ROOT / 'dist/overleaf.zip'
output.parent.mkdir(exist_ok=True)
files = {
    'main.tex': (ROOT / 'paper/main.tex').read_bytes(),
    'README.txt': b'Compile main.tex with pdfLaTeX. The bibliography and figures are embedded.\nCanonical source: paper/main.tex in dtlics/Indefinite-Causal-Order.\n',
}
with zipfile.ZipFile(output, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
    for name, data in sorted(files.items()):
        info = zipfile.ZipInfo(name, date_time=(2026, 10, 5, 0, 0, 0))
        info.compress_type = zipfile.ZIP_DEFLATED
        info.external_attr = 0o644 << 16
        archive.writestr(info, data)
print(f'{output}\nSHA-256 {hashlib.sha256(output.read_bytes()).hexdigest()}')
