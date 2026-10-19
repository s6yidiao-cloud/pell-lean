#!/usr/bin/env python3
"""Bundle Lean sources and the manuscript PDF without contacting any service."""

import argparse
import gzip
import io
import os
from pathlib import Path
import tarfile

import verify


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=verify.ROOT / 'build/pell-lean-source.tar.gz')
    args = parser.parse_args()
    verify.scan_and_order(verify.authored_modules())
    verify.check_integrity(verify.authored_modules())
    excluded = {'.git', '.lake', 'build', '__pycache__', '.pytest_cache'}
    special = {'LICENSE', 'NOTICE', 'lean-toolchain', 'SOURCE_SHA256SUMS', '.gitignore', '.gitattributes'}
    extensions = {'.lean', '.md', '.toml', '.json', '.yaml', '.yml', '.py', '.sh', '.svg', '.png', '.cff'}
    files = []
    for directory, folders, filenames in os.walk(verify.ROOT):
        folders[:] = [name for name in folders if name not in excluded and not name.startswith('._')]
        for name in filenames:
            path = Path(directory) / name
            if not name.startswith('._') and (name in special or
                    name.endswith(('LICENSE', 'NOTICE', 'COPYING')) or path.suffix in extensions
                    or path == verify.ROOT / 'paper/main.pdf'):
                files.append(path)
    licenses = {verify.ROOT / name for name in [
        'vendor/TauCeti/LICENSE', 'vendor/TauCeti/MATHLIB_LICENSE',
        'third_party/FormalPantheon-LICENSE', 'third_party/PrimeNumberTheoremAnd-LICENSE']}
    verify.require(licenses.issubset(files), 'Source bundle omits a required license file')
    verify.require(verify.ROOT / 'paper/main.pdf' in files, 'Bundle omits the manuscript PDF')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open('wb') as raw, gzip.GzipFile(fileobj=raw, mode='wb', mtime=0, filename='') as compressed:
        with tarfile.open(fileobj=compressed, mode='w') as archive:
            for path in sorted(files):
                verify.require(not path.is_symlink(), f'Release source is a symlink: {path}')
                contents = path.read_bytes()
                entry = tarfile.TarInfo('PellFormalization/' + str(path.relative_to(verify.ROOT)))
                entry.size = len(contents)
                entry.mode = 0o644
                entry.mtime = entry.uid = entry.gid = 0
                archive.addfile(entry, io.BytesIO(contents))
    print(f'{len(files)} source files: {args.output.resolve()}')
    print(f'SHA-256: {verify.digest(args.output)}')


if __name__ == '__main__':
    main()
