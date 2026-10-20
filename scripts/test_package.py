#!/usr/bin/env python3
"""Fast source archive checks; no Lean installation or network required."""

import hashlib
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch

import package
import verify


class SourcePackageTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.vendor = self.root / 'formalization/vendor/TauCeti'
        self.root_manifest = self.root / 'checks/SOURCE_SHA256SUMS'
        self.vendor_manifest = self.vendor / 'SOURCE_SHA256SUMS'
        sources = {
            'README.md': 'Current documentation\n',
            'formalization/Pell.lean': 'theorem verified : True := .intro\n',
            'formalization/vendor/TauCeti/TauCeti/A.lean': 'theorem vendor : True := .intro\n',
            'formalization/vendor/TauCeti/LICENSE': 'TauCeti license\n',
            'formalization/vendor/TauCeti/MATHLIB_LICENSE': 'Mathlib license\n',
            'docs/licenses/FormalPantheon-LICENSE': 'FormalPantheon license\n',
            'docs/licenses/PrimeNumberTheoremAnd-LICENSE': 'PrimeNumberTheoremAnd license\n',
            'paper/main.pdf': '%PDF-test\n',
            'checks/SOURCE_SHA256SUMS': 'stale root manifest\n',
            'formalization/vendor/TauCeti/SOURCE_SHA256SUMS': 'stale vendor manifest\n',
        }
        for name, text in sources.items():
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        self.integrity_modes = []
        replacements = {
            'ROOT': self.root,
            'package_root': lambda: self.root / 'formalization',
            'source_files': self.files,
            'authored_modules': lambda: {
                'Pell': (self.root / 'formalization/Pell.lean', self.root / 'formalization')},
            'scan_and_order': lambda modules: ['Pell'],
            'check_integrity': self.integrity,
        }
        for name, replacement in replacements.items():
            patcher = patch.object(verify, name, replacement)
            patcher.start()
            self.addCleanup(patcher.stop)

    def files(self):
        return {path for path in self.root.rglob('*')
                if path.is_file() and 'build' not in path.relative_to(self.root).parts}

    def integrity(self, modules, *, frozen=False):
        self.integrity_modes.append(frozen)
        files = self.files()
        if frozen:
            verify.check_hash_manifest(self.vendor_manifest, self.vendor,
                                       {p for p in files if p.is_relative_to(self.vendor)
                                        and p != self.vendor_manifest})
            verify.check_hash_manifest(self.root_manifest, self.root, files - {self.root_manifest})
        return {path.relative_to(self.root).as_posix(): verify.digest(path) for path in files}

    def read_archive(self, path):
        with tarfile.open(path) as archive:
            result = {}
            for member in archive.getmembers():
                self.assertTrue(member.isfile())
                self.assertEqual(member.mtime, 0)
                self.assertEqual(member.uid, 0)
                self.assertEqual(member.gid, 0)
                self.assertEqual(member.mode, 0o644)
                self.assertTrue(member.name.startswith('PellFormalization/'))
                result[member.name.removeprefix('PellFormalization/')] = archive.extractfile(member).read()
            return result

    def assert_manifest(self, contents, name, base=''):
        entries = {}
        for line in contents[name].decode().splitlines():
            if line and not line.startswith('#'):
                digest, relative = line.split('  ', 1)
                self.assertNotIn(relative, entries)
                entries[relative] = digest
        expected = {path.removeprefix(base): hashlib.sha256(data).hexdigest()
                    for path, data in contents.items() if path != name and path.startswith(base)}
        self.assertEqual(entries, expected)

    def test_default_replaces_stale_archive_manifests_and_is_reproducible(self):
        root_before = self.root_manifest.read_bytes()
        vendor_before = self.vendor_manifest.read_bytes()
        first = self.root / 'build/first.tar.gz'
        second = self.root / 'build/second.tar.gz'
        count = package.package_sources(first)
        package.package_sources(second)
        contents = self.read_archive(first)
        self.assertEqual(count, len(contents))
        self.assertEqual(first.read_bytes(), second.read_bytes())
        self.assert_manifest(contents, 'checks/SOURCE_SHA256SUMS')
        self.assert_manifest(contents, 'formalization/vendor/TauCeti/SOURCE_SHA256SUMS',
                             'formalization/vendor/TauCeti/')
        self.assertEqual(self.root_manifest.read_bytes(), root_before)
        self.assertEqual(self.vendor_manifest.read_bytes(), vendor_before)
        self.assertEqual(self.integrity_modes, [False, False, False, False])

    def test_default_generates_missing_manifests_only_inside_archive(self):
        self.root_manifest.unlink()
        self.vendor_manifest.unlink()
        output = self.root / 'build/current.tar.gz'
        package.package_sources(output)
        contents = self.read_archive(output)
        self.assert_manifest(contents, 'checks/SOURCE_SHA256SUMS')
        self.assert_manifest(contents, 'formalization/vendor/TauCeti/SOURCE_SHA256SUMS',
                             'formalization/vendor/TauCeti/')
        self.assertFalse(self.root_manifest.exists())
        self.assertFalse(self.vendor_manifest.exists())

    def test_frozen_preserves_valid_manifest_bytes_and_rejects_stale_ones(self):
        output = self.root / 'build/frozen.tar.gz'
        with self.assertRaisesRegex(RuntimeError, 'Malformed hash manifest'):
            package.package_sources(output, frozen=True)
        self.assertFalse(output.exists())
        contents = {path: path.read_bytes() for path in self.files()}
        self.vendor_manifest.write_bytes(package.manifest_bytes(contents, self.vendor,
                                                                 self.vendor_manifest))
        contents[self.vendor_manifest] = self.vendor_manifest.read_bytes()
        self.root_manifest.write_bytes(package.manifest_bytes(contents, self.root,
                                                               self.root_manifest))
        package.package_sources(output, frozen=True)
        archived = self.read_archive(output)
        self.assertEqual(archived['checks/SOURCE_SHA256SUMS'], self.root_manifest.read_bytes())
        self.assertEqual(archived['formalization/vendor/TauCeti/SOURCE_SHA256SUMS'],
                         self.vendor_manifest.read_bytes())
        self.assertEqual(self.integrity_modes, [True, True, True])

    def test_source_mutation_rejects_archive_and_cleans_temporary_output(self):
        output = self.root / 'build/source.tar.gz'
        original = package.write_archive

        def mutate_after_write(path, contents):
            original(path, contents)
            (self.root / 'README.md').write_text('Changed while packaging\n')

        with patch.object(package, 'write_archive', mutate_after_write):
            with self.assertRaisesRegex(RuntimeError, 'Sources changed while packaging'):
                package.package_sources(output)
        self.assertFalse(output.exists())
        self.assertEqual(list(output.parent.iterdir()), [])

    def test_frozen_archive_requires_manifest_coverage_of_documentation(self):
        contents = {path: path.read_bytes() for path in self.files()}
        self.vendor_manifest.write_bytes(package.manifest_bytes(contents, self.vendor,
                                                                 self.vendor_manifest))
        contents[self.vendor_manifest] = self.vendor_manifest.read_bytes()
        del contents[self.root / 'README.md']
        self.root_manifest.write_bytes(package.manifest_bytes(contents, self.root,
                                                               self.root_manifest))
        # Even if verification only requires proof/control coverage, packaging
        # must require a manifest entry for every byte that it distributes.
        def snapshot(modules, *, frozen=False):
            return {p.relative_to(self.root).as_posix(): verify.digest(p) for p in self.files()}

        with patch.object(verify, 'check_integrity', snapshot):
            with self.assertRaisesRegex(RuntimeError, 'omits required sources'):
                package.package_sources(self.root / 'build/incomplete.tar.gz', frozen=True)

    def test_symlinks_and_missing_licenses_are_rejected(self):
        readme = self.root / 'README.md'
        readme.unlink()
        readme.symlink_to(self.root / 'paper/main.pdf')
        with self.assertRaisesRegex(RuntimeError, 'symlink'):
            package.package_sources(self.root / 'build/symlink.tar.gz')
        readme.unlink()
        (self.root / 'docs/licenses/FormalPantheon-LICENSE').unlink()
        with self.assertRaisesRegex(RuntimeError, 'required license'):
            package.package_sources(self.root / 'build/missing-license.tar.gz')


if __name__ == '__main__':
    unittest.main()
