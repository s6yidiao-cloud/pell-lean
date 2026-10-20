#!/usr/bin/env python3
"""Bundle the current sources, or verify a frozen release with --frozen."""

import argparse
import gzip
import hashlib
import io
import os
from pathlib import Path
import sys
import tarfile
import tempfile

import verify


def manifest_bytes(contents: dict[Path, bytes], base: Path, manifest: Path) -> bytes:
    """Hash exactly the archived bytes, excluding a manifest's own contents."""
    lines = ['# SHA-256 of bundled files; this manifest excludes itself.\n']
    for path in sorted(contents):
        if path != manifest and path.is_relative_to(base):
            lines.append(f'{hashlib.sha256(contents[path]).hexdigest()}  '
                         f'{path.relative_to(base).as_posix()}\n')
    return ''.join(lines).encode()


def write_archive(output: Path, contents: dict[Path, bytes]) -> None:
    with output.open('wb') as raw, gzip.GzipFile(fileobj=raw, mode='wb', mtime=0, filename='') as compressed:
        with tarfile.open(fileobj=compressed, mode='w') as archive:
            for path, data in sorted(contents.items()):
                entry = tarfile.TarInfo('PellFormalization/' + path.relative_to(verify.ROOT).as_posix())
                entry.size = len(data)
                entry.mode = 0o644
                entry.mtime = entry.uid = entry.gid = 0
                archive.addfile(entry, io.BytesIO(data))


def package_sources(output: Path, *, frozen: bool = False) -> int:
    modules = verify.authored_modules()
    verify.scan_and_order(modules)
    before = verify.check_integrity(modules, frozen=frozen)
    files = verify.source_files()
    licenses = {verify.ROOT / name for name in [
        'formalization/vendor/TauCeti/LICENSE', 'formalization/vendor/TauCeti/MATHLIB_LICENSE',
        'docs/licenses/FormalPantheon-LICENSE', 'docs/licenses/PrimeNumberTheoremAnd-LICENSE']}
    verify.require(licenses.issubset(files), 'Source bundle omits a required license file')
    verify.require(verify.ROOT / 'paper/main.pdf' in files, 'Bundle omits the manuscript PDF')
    verify.require(output.resolve() not in {path.resolve() for path in files},
                   'Archive output is also a source file')
    contents = {}
    for path in sorted(files):
        verify.require(path.is_relative_to(verify.ROOT), f'Source is outside repository: {path}')
        verify.require(not path.is_symlink(), f'Release source is a symlink: {path}')
        verify.require(path.suffix.lower() != '.tex', f'Private TeX source in bundle: {path}')
        data = path.read_bytes()
        relative = path.relative_to(verify.ROOT).as_posix()
        if relative in before:
            verify.require(hashlib.sha256(data).hexdigest() == before[relative],
                           f'Source changed while packaging: {relative}')
        contents[path] = data
    vendor = verify.package_root() / 'vendor/TauCeti'
    vendor_manifest = vendor / 'SOURCE_SHA256SUMS'
    root_manifest = verify.ROOT / 'checks/SOURCE_SHA256SUMS'
    if frozen:
        verify.check_hash_manifest(vendor_manifest, vendor,
                                   {path for path in contents if path.is_relative_to(vendor)
                                    and path != vendor_manifest})
        verify.check_hash_manifest(root_manifest, verify.ROOT, set(contents) - {root_manifest})
    else:
        contents[vendor_manifest] = manifest_bytes(contents, vendor, vendor_manifest)
        contents[root_manifest] = manifest_bytes(contents, verify.ROOT, root_manifest)
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=output.parent, prefix=output.name + '.',
                                     suffix='.tmp', delete=False) as stream:
        temporary = Path(stream.name)
    try:
        write_archive(temporary, contents)
        final_modules = verify.authored_modules()
        verify.require(set(final_modules) == set(modules),
                       'Authored module set changed while packaging')
        verify.scan_and_order(final_modules)
        after = verify.check_integrity(final_modules, frozen=frozen)
        verify.require(after == before, 'Sources changed while packaging')
        os.replace(temporary, output)
    finally:
        temporary.unlink(missing_ok=True)
    return len(contents)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=verify.ROOT / 'build/pell-lean-source.tar.gz')
    parser.add_argument('--frozen', action='store_true',
                        help='Require checked-in release manifests and preserve their bytes')
    args = parser.parse_args()
    count = package_sources(args.output, frozen=args.frozen)
    print(f'{count} source files: {args.output.resolve()}')
    print(f'SHA-256: {verify.digest(args.output)}')


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, OSError, ValueError) as error:
        print(f'FAIL: {error}', file=sys.stderr)
        sys.exit(1)
