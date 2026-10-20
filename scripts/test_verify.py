#!/usr/bin/env python3
"""Regression checks for the verification trust boundary (no Lean build)."""

import tempfile
from contextlib import contextmanager
import shutil
import threading
import time
import unittest
from pathlib import Path
from unittest.mock import patch

import verify


@contextmanager
def checkout():
    """Small checkout with the real dependency pins and dummy Lean sources."""
    original = verify.ROOT
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        for name in ["lean-toolchain", *verify.PINNED_DEPENDENCY_FILES]:
            destination = root / "formalization" / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(original / "formalization" / name, destination)
        texts = {
            "formalization/Pell.lean": "import Pell.A\n",
            "formalization/Pell/A.lean": "theorem proof : True := .intro\n",
            "formalization/vendor/TauCeti/TauCeti/A.lean": "theorem vendorProof : True := .intro\n",
            "checks/PellAudit.lean": "import Pell\n",
            "checks/formalization.yaml": "source:\n  bundled: false\n  sha256: " + "a" * 64 + "\n",
            "README.md": "A development checkout.\n",
            "scripts/verify.py": "# verifier\n",
            "scripts/test_verify.py": "# tests\n",
            "scripts/package.py": "# packager\n",
            ".github/workflows/lean.yml": "# workflow\n",
        }
        for name, text in texts.items():
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        with patch.object(verify, "ROOT", root):
            yield root


def freeze_checkout(root):
    vendor = root / "formalization/vendor/TauCeti"
    for base, manifest in [(vendor, vendor / "SOURCE_SHA256SUMS"),
                           (root, root / "checks/SOURCE_SHA256SUMS")]:
        manifest.write_text("".join(f"{verify.digest(path)}  {path.relative_to(base)}\n"
            for path in sorted(verify.source_files())
            if path.is_relative_to(base) and path != manifest))


class VerificationBoundaryTests(unittest.TestCase):
    def test_current_sources_allow_edits_without_updating_release_manifests(self):
        with checkout() as root:
            freeze_checkout(root)
            verify.check_integrity(verify.authored_modules(), frozen=True)
            for name, text in [
                ("README.md", "Revised documentation.\n"),
                ("formalization/Pell/A.lean", "-- Revised comment\ntheorem proof : True := .intro\n"),
                ("formalization/Pell/A.lean", "theorem revised : True := .intro\n"),
                ("formalization/Pell/New.lean", "theorem added : True := .intro\n"),
                ("formalization/vendor/TauCeti/TauCeti/A.lean", "theorem revisedVendor : True := .intro\n"),
            ]:
                with self.subTest(name=name, text=text):
                    (root / name).write_text(text)
                    modules = verify.authored_modules()
                    verify.scan_and_order(modules)
                    snapshot = verify.check_integrity(modules)
                    self.assertEqual(snapshot[name], verify.digest(root / name))
                    with self.assertRaisesRegex(RuntimeError, "Hash mismatch|omits required"):
                        verify.check_integrity(modules, frozen=True)

    def test_current_snapshot_detects_edits_additions_and_deletions_during_build(self):
        for operation in ["edit", "add", "delete"]:
            with self.subTest(operation=operation), checkout() as root:
                before = verify.check_integrity(verify.authored_modules())
                if operation == "edit":
                    (root / "README.md").write_text("Edited while compiling.\n")
                elif operation == "add":
                    (root / "formalization/Pell/New.lean").write_text("theorem added : True := .intro\n")
                else:
                    (root / "README.md").unlink()
                after = verify.check_integrity(verify.authored_modules())
                with self.assertRaisesRegex(RuntimeError, "inputs changed"):
                    verify.assert_unchanged(before, after)

    def test_current_mode_still_rejects_proof_escapes(self):
        with checkout() as root:
            for token in ["sorry", "admit", "axiom", "native_decide", "trustCompiler", "sorryAx"]:
                with self.subTest(token=token):
                    (root / "formalization/Pell/A.lean").write_text(f"by {token}\n")
                    with self.assertRaisesRegex(RuntimeError, "Forbidden proof token"):
                        verify.scan_and_order(verify.authored_modules())

    def test_dependency_configs_remain_pinned_without_frozen_mode(self):
        with checkout() as root:
            for name in verify.PINNED_DEPENDENCY_FILES:
                path = root / "formalization" / name
                original = path.read_bytes()
                path.write_bytes(original + b"\n")
                with self.subTest(name=name):
                    with self.assertRaisesRegex(RuntimeError, "Dependency configuration changed"):
                        verify.check_integrity(verify.authored_modules())
                path.write_bytes(original)

    def test_private_manuscript_provenance_needs_no_tex_file(self):
        status = 'source:\n  bundled: false\n  sha256: ' + 'a' * 64 + '\n'
        verify.check_manuscript_metadata(status)
        for invalid in [status.replace('false', 'true'),
                        status.replace('a' * 64, 'a' * 63),
                        'source:\n  bundled: false\n',
                        'source:\n  sha256: ' + 'a' * 64 + '\n']:
            with self.subTest(status=invalid):
                with self.assertRaises(RuntimeError):
                    verify.check_manuscript_metadata(invalid)

    def test_parallel_scheduler_observes_dependencies_and_order(self):
        dependencies = {'A': set(), 'B': {'A'}, 'C': {'A'}, 'D': {'B', 'C'}, 'E': set()}
        done, lock = set(), threading.Lock()

        def worker(name):
            with lock:
                self.assertTrue(dependencies[name].issubset(done))
            time.sleep(0.001)
            with lock:
                done.add(name)
            return name

        order = list(dependencies)
        self.assertEqual(verify.execute_order(order, dependencies, 3, worker), order)

    def test_parallel_scheduler_does_not_run_failed_module_dependents(self):
        called = []

        def worker(name):
            called.append(name)
            raise RuntimeError('compile failed')

        with self.assertRaisesRegex(RuntimeError, 'compile failed'):
            verify.execute_order(['A', 'B'], {'A': set(), 'B': {'A'}}, 2, worker)
        self.assertEqual(called, ['A'])

    def test_nested_comments_strings_and_line_numbers(self):
        text = '-- sorry\n/- axiom /- native_decide -/ admit -/\n"sorry \\\" axiom"\nby sorry\n'
        code = verify.lean_code(text)
        self.assertEqual(code.count('\n'), text.count('\n'))
        self.assertNotIn('native_decide', code)
        self.assertEqual(code.split().count('sorry'), 1)

    def test_unterminated_comment_is_rejected(self):
        with self.assertRaises(RuntimeError):
            verify.lean_code('/- hidden sorry')

    def test_hash_manifest_must_cover_every_required_file(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / 'A.lean'
            source.write_text('theorem proof : True := .intro\n')
            manifest = root / 'SOURCE_SHA256SUMS'
            manifest.write_text('')
            with self.assertRaises(RuntimeError):
                verify.check_hash_manifest(manifest, root, {source})
            manifest.write_text(f'{verify.digest(source)}  A.lean\n')
            verify.check_hash_manifest(manifest, root, {source})
            source.write_text('axiom untrusted : False\n')
            with self.assertRaises(RuntimeError):
                verify.check_hash_manifest(manifest, root, {source})

    def test_control_files_are_required_and_manifest_protected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            paths = {root / name for name in ["scripts/verify.py", "scripts/test_verify.py",
                "scripts/package.py", ".github/workflows/lean.yml",
                "scripts/new_check.sh", ".github/workflows/new_check.yaml"]}
            for path in paths:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("release control source\n")
            with patch.object(verify, 'ROOT', root):
                self.assertEqual(verify.required_control_files(), paths)
                manifest = root / 'SOURCE_SHA256SUMS'
                unprotected = root / 'scripts/verify.py'
                manifest.write_text(''.join(f'{verify.digest(path)}  {path.relative_to(root)}\n'
                                            for path in sorted(paths - {unprotected})))
                with self.assertRaisesRegex(RuntimeError, 'omits required sources'):
                    verify.check_hash_manifest(manifest, root, verify.required_control_files())
                manifest.write_text(''.join(f'{verify.digest(path)}  {path.relative_to(root)}\n'
                                            for path in sorted(paths)))
                verify.check_hash_manifest(manifest, root, verify.required_control_files())
                unprotected.write_text('changed verifier\n')
                with self.assertRaisesRegex(RuntimeError, 'Hash mismatch'):
                    verify.check_hash_manifest(manifest, root, verify.required_control_files())
                unprotected.unlink()
                with self.assertRaisesRegex(RuntimeError, 'Missing required'):
                    verify.required_control_files()

    def test_audit_rejects_missing_duplicate_and_untrusted_axioms(self):
        expected = verify.REQUIRED_ENDPOINTS
        text = '\n'.join(f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
                         for name in sorted(expected))
        with patch.object(Path, 'read_text', return_value='\n'.join(
                f'#print axioms {name}' for name in sorted(expected))):
            self.assertEqual(set(verify.check_audit(text)), expected)
            for invalid in ['', text + '\n' + text.splitlines()[0],
                            text.replace('Quot.sound', 'sorryAx', 1),
                            text.replace('Quot.sound', 'Lean.ofReduceBool', 1),
                            text.replace('Quot.sound', 'Hidden.missingLemma', 1)]:
                with self.subTest(invalid=invalid[:100]):
                    with self.assertRaises(RuntimeError):
                        verify.check_audit(invalid)

    def test_audit_accepts_axiom_free_output(self):
        name = 'PellPaper.example'
        with patch.object(verify, 'REQUIRED_ENDPOINTS', {name}), \
                patch.object(Path, 'read_text', return_value=f'#print axioms {name}'):
            self.assertEqual(verify.check_audit(f"'{name}' does not depend on any axioms"),
                             {name: []})


if __name__ == '__main__':
    unittest.main()
