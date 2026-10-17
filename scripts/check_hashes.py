"""Check the explicitly enumerated release manifest."""
from pathlib import Path
import hashlib
ROOT=Path(__file__).resolve().parents[1]
count=0
mismatches=[]
for line in (ROOT/'release/SHA256SUMS').read_text().splitlines():
    digest,name=line.split('  ',1)
    path=(ROOT/name).resolve()
    assert path.is_relative_to(ROOT),name
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != digest:
        mismatches.append((name, digest, actual))
    count+=1
if mismatches:
    for name, expected, actual in mismatches:
        print(f'MISMATCH {name}: manifest={expected}, actual={actual}')
    raise AssertionError(f'{len(mismatches)} SHA-256 mismatch(es)')
print('PASS',count,'SHA-256 entries')
