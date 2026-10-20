#!/usr/bin/env python3
"""Fresh Lean checks and a fail-closed, reproducible endpoint axiom audit.

Run from any directory. Direct mode needs preinstalled pinned dependency caches;
only external dependency artifacts are reused. Every Pell/TauCeti module gets a
new output directory, including modules that are not reachable from Pell.lean.
"""

from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
TOOLCHAIN = "leanprover/lean4:v4.33.1"
MATHLIB_REV = "0df444a360eaa60ab8c11dca51a86af692955474"
# Dependency changes require a deliberate pin update, independently of release hashes.
PINNED_DEPENDENCY_FILES = {
    "lakefile.toml": "101b2c435a655aca7f6556c3a2c955a67f1a21943cf05c86a9a0cf9ab2707d47",
    "lake-manifest.json": "1c77eaa5b996b6f3b45800da678052ff17b98d5fb0edf81c817de54f617c36d7",
    "vendor/TauCeti/lakefile.toml": "a6cd9909a52532a5a275e9bd73bf10fc510123ef76abdadc0a2c0eb29182aa7e",
    "vendor/TauCeti/lean-toolchain": "3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71",
    "vendor/TauCeti/lake-manifest.json": "1db9fc44525f567cdbde92bf4258e937e19bb385d590be256930c44a8cbcfc9d",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REQUIRED_ENDPOINTS = {
    "PellPaper.proper_form_classes_finite",
    "PellPaper.field_class_average",
    "PellPaper.odd_class_average",
    "PellPaper.uniform_exceptional",
    "PellPaper.pell_unit_growth_density",
    "PellPaper.fixed_power_density",
    "PellPaper.final_field_class_average",
    "PellPaper.final_odd_class_average",
    "PellPaper.final_uniform_exceptional",
    "PellPaper.final_pell_unit_growth_density",
    "PellPaper.final_fixed_power_density",
    "PellPaper.realQuadraticFieldOddClassNumber_eq_card_oddOrderClasses",
    "PellPaper.anisotropic_sharp_squareSieve",
    "PellPaper.uniform_exceptional_doubled_parameter",
    "PellPaper.anisotropic_product_squareSieve",
    "PellPaper.uniform_exceptional_E_doubled_parameter",
    "PellPaper.uniformExceptionalEstimate_doubled_parameter",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def package_root() -> Path:
    return ROOT / "formalization"


def source_files() -> set[Path]:
    """Discover distributable inputs independently of any frozen manifest."""
    excluded = {".git", ".lake", "build", "__pycache__", ".pytest_cache"}
    special = {"LICENSE", "NOTICE", "lean-toolchain", "SOURCE_SHA256SUMS",
               ".gitignore", ".gitattributes"}
    extensions = {".lean", ".md", ".toml", ".json", ".yaml", ".yml",
                  ".py", ".sh", ".svg", ".png", ".cff"}
    files = set()
    for directory, folders, filenames in os.walk(ROOT):
        folders[:] = [name for name in folders if name not in excluded
                      and not name.startswith("._")]
        for name in filenames:
            path = Path(directory) / name
            if not name.startswith("._") and (name in special or
                    name.endswith(("LICENSE", "NOTICE", "COPYING")) or
                    path.suffix in extensions or path == ROOT / "paper/main.pdf"):
                require(not path.is_symlink(), f"Source is a symlink: {path}")
                files.add(path)
    return files


def assert_unchanged(before: dict[str, str], after: dict[str, str]) -> None:
    changed = sorted(name for name in before.keys() | after.keys()
                     if before.get(name) != after.get(name))
    require(not changed, f"Verification inputs changed during the run: {changed[:10]}")


def lean_code(text: str) -> str:
    """Remove nested Lean comments and string literals, preserving line numbers.

    Character literals are deliberately retained: Lean uses primes in identifiers
    and the banned words cannot form a character literal. Unterminated comments
    or strings are rejected rather than silently hiding source from the scanner.
    """
    out = list(text)
    index = depth = 0
    string = False
    while index < len(text):
        pair = text[index:index + 2]
        if depth:
            if pair == "/-":
                depth += 1
            elif pair == "-/":
                depth -= 1
            else:
                out[index] = "\n" if text[index] == "\n" else " "
                index += 1
                continue
            out[index:index + 2] = "  "
            index += 2
        elif string:
            out[index] = "\n" if text[index] == "\n" else " "
            if text[index] == "\\":
                index += 1
                if index < len(text):
                    out[index] = "\n" if text[index] == "\n" else " "
            elif text[index] == '"':
                string = False
            index += 1
        elif pair == "/-":
            depth = 1
            out[index:index + 2] = "  "
            index += 2
        elif pair == "--":
            end = text.find("\n", index)
            end = len(text) if end == -1 else end
            out[index:end] = " " * (end - index)
            index = end
        elif text[index] == '"':
            string = True
            out[index] = " "
            index += 1
        else:
            index += 1
    require(not depth and not string, "Unterminated Lean comment/string in scanned source")
    return "".join(out)


def authored_modules() -> dict[str, tuple[Path, Path]]:
    modules = {}
    package = package_root()
    for base, folder in [(package, package / "Pell"),
                         (package / "vendor/TauCeti", package / "vendor/TauCeti/TauCeti")]:
        for path in sorted(folder.rglob("*.lean")):
            if path.name.startswith("._"):
                continue
            module = ".".join(path.relative_to(base).with_suffix("").parts)
            require(module not in modules, f"Duplicate authored module: {module}")
            modules[module] = (path, base)
    modules["Pell"] = (package / "Pell.lean", package)
    modules["PellAudit"] = (ROOT / "checks/PellAudit.lean", ROOT / "checks")
    return modules


def imports(code: str) -> list[str]:
    found = []
    for line in code.splitlines():
        match = re.match(r"\s*(?:public\s+|private\s+)?import\s+(.+?)\s*$", line)
        if match:
            found.extend(match.group(1).split())
    return found


def scan_and_order(modules: dict[str, tuple[Path, Path]]) -> list[str]:
    dependencies = {}
    for name, (path, _) in modules.items():
        code = lean_code(path.read_text())
        banned = re.search(r"\b(?:sorry|admit|axiom|sorryAx|native_decide|trustCompiler)\b", code)
        require(banned is None, f"Forbidden proof token in {path.relative_to(ROOT)}: "
                f"{banned.group() if banned else ''}")
        require(not re.search(r"\bset_option\s+warningAsError\s+false\b", code),
                f"Warnings disabled in {path.relative_to(ROOT)}")
        local = []
        for imported in imports(code):
            if imported == "Pell" or imported.startswith(("Pell.", "TauCeti.")):
                require(imported in modules, f"Missing local import: {name} imports {imported}")
                local.append(imported)
        dependencies[name] = local
    order, visiting, visited = [], set(), set()

    def visit(name: str) -> None:
        require(name not in visiting, f"Import cycle at {name}")
        if name in visited:
            return
        visiting.add(name)
        for other in sorted(dependencies[name]):
            visit(other)
        visiting.remove(name)
        visited.add(name)
        order.append(name)

    # Entrypoints last; this also places all unused authored files in the check.
    for name in sorted(set(modules) - {"Pell", "PellAudit"}):
        visit(name)
    for name in ["Pell", "PellAudit"]:
        visit(name)
    return order


def compile_dependencies(modules: dict[str, tuple[Path, Path]]) -> dict[str, set[str]]:
    dependencies = {name: set(imports(lean_code(path.read_text()))) & set(modules)
                    for name, (path, _) in modules.items()}
    # Entrypoints are release gates, checked only after every authored module.
    dependencies["Pell"].update(set(modules) - {"Pell", "PellAudit"})
    dependencies["PellAudit"].add("Pell")
    return dependencies


def execute_order(order, dependencies, jobs, worker):
    """Run ready modules concurrently, never starting before local imports finish.

    Exceptions stop scheduling and propagate after already-running checks exit.
    Results are returned in the deterministic topological order, irrespective of
    process completion order. No dependent of a failed module can be scheduled.
    """
    pending, complete, running = list(order), {}, {}
    with ThreadPoolExecutor(max_workers=jobs) as executor:
        while pending or running:
            for name in list(pending):
                if len(running) == jobs:
                    break
                if dependencies[name].issubset(complete):
                    pending.remove(name)
                    running[executor.submit(worker, name)] = name
            require(bool(running), "No ready module: incomplete/cyclic dependency graph")
            finished, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in finished:
                name = running.pop(future)
                complete[name] = future.result()
    return [complete[name] for name in order]


def check_hash_manifest(path: Path, base: Path, required: set[Path]) -> dict[str, str]:
    require(path.is_file(), f"Missing source hash manifest: {path}")
    seen = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", line)
        require(match is not None, f"Malformed hash manifest line in {path}: {line}")
        expected, relative = match.groups()
        target = base / relative
        require(not Path(relative).is_absolute() and ".." not in Path(relative).parts,
                f"Unsafe hash manifest path: {relative}")
        require(relative not in seen, f"Duplicate hash manifest path: {relative}")
        require(target.is_file() and digest(target) == expected, f"Hash mismatch: {target}")
        seen[relative] = expected
    missing = {str(p.relative_to(base)) for p in required} - set(seen)
    require(not missing, f"Hash manifest omits required sources: {sorted(missing)}")
    return seen


def required_control_files() -> set[Path]:
    """Include the verifier, release packager, tests, and CI in source integrity.

    Fixed entrypoints may not disappear silently; added checker scripts and
    workflows must also enter the frozen manifest before a release can pass.
    """
    files = {ROOT / name for name in ["scripts/verify.py", "scripts/test_verify.py",
        "scripts/package.py", ".github/workflows/lean.yml"]}
    files.update(path for path in (ROOT / "scripts").rglob("*")
                 if path.is_file() and path.suffix in {".py", ".sh"}
                 and not path.name.startswith("._"))
    files.update(path for path in (ROOT / ".github/workflows").rglob("*")
                 if path.is_file() and path.suffix in {".yaml", ".yml"}
                 and not path.name.startswith("._"))
    require(all(path.is_file() for path in files), "Missing required verification/release control file")
    return files


def check_manuscript_metadata(status: str) -> None:
    """Keep statement provenance without requiring distribution of private TeX."""
    require(re.search(r"(?m)^  bundled: false\s*$", status) is not None,
            "Manuscript source must remain private (bundled: false)")
    require(re.search(r"(?m)^  sha256: [\"']?[0-9a-f]{64}[\"']?\s*$", status) is not None,
            "Missing or malformed private manuscript fingerprint")


def check_integrity(modules: dict[str, tuple[Path, Path]], *, frozen: bool = False) -> dict[str, str]:
    package = package_root()
    require((package / "lean-toolchain").read_text().strip() == TOOLCHAIN,
            "Unexpected Lean toolchain pin")
    for name, expected in PINNED_DEPENDENCY_FILES.items():
        require(digest(package / name) == expected,
                f"Dependency configuration changed: formalization/{name}; update pins deliberately")
    authored = {path for path, _ in modules.values()}
    required = authored | required_control_files() | {package / "lean-toolchain",
        ROOT / "checks/formalization.yaml"} | {package / p for p in PINNED_DEPENDENCY_FILES}
    status = (ROOT / "checks/formalization.yaml").read_text()
    check_manuscript_metadata(status)
    files = source_files()
    require(required.issubset(files), "Missing required verification input")
    if frozen:
        hashes = check_hash_manifest(ROOT / "checks/SOURCE_SHA256SUMS", ROOT,
                                     files - {ROOT / "checks/SOURCE_SHA256SUMS"})
        require(not any(Path(name).suffix.lower() == ".tex" for name in hashes),
                "Source manifest must not distribute private TeX manuscript files")
        vendor = package / "vendor/TauCeti"
        check_hash_manifest(vendor / "SOURCE_SHA256SUMS", vendor,
                            {p for p in files if p.is_relative_to(vendor)
                             and p != vendor / "SOURCE_SHA256SUMS"})
    return {str(path.relative_to(ROOT)): digest(path) for path in sorted(files)}


def run(command: list[str], log: Path, *, cwd: Path | None = None,
        env: dict[str, str] | None = None) -> str:
    with log.open("w") as stream:
        result = subprocess.run(command, cwd=cwd or package_root(), env=env, stdout=stream,
                                stderr=subprocess.STDOUT, text=True)
    output = log.read_text(errors="replace")
    require(result.returncode == 0, f"Command failed ({result.returncode}); see {log}\n{output[-6000:]}")
    return output


def choose_git(explicit: str | None) -> str:
    candidates = [explicit] if explicit else [shutil.which("git"), str(Path.home() /
        ".cache/codex-runtimes/codex-primary-runtime/dependencies/bin/fallback/git")]
    for candidate in candidates:
        if candidate and Path(candidate).is_file():
            result = subprocess.run([candidate, "--version"], capture_output=True, text=True)
            if result.returncode == 0:
                return candidate
    raise RuntimeError("No working Git; use --git PATH (direct mode does not invoke Lake)")


def check_lean_version(version: str) -> None:
    require(re.search(r"\bversion 4\.33\.1(?:,|\))", version) is not None,
            f"Wrong Lean version: {version.strip()}")


def dependency_path(directory: Path, git: str, *, receipts: list[dict] | None = None) -> list[Path]:
    manifest = json.loads((package_root() / "lake-manifest.json").read_text())
    paths = []
    for package in manifest["packages"]:
        if package["type"] != "git":
            require(package["name"] == "TauCeti", f"Unexpected path dependency: {package}")
            continue
        location = directory / package["name"]
        result = subprocess.run([git, "-C", str(location), "rev-parse", "HEAD"],
                                capture_output=True, text=True)
        require(result.returncode == 0 and result.stdout.strip() == package["rev"],
                f"Dependency revision mismatch: {package['name']} (see {location})")
        result = subprocess.run([git, "-C", str(location), "diff", "--quiet", "HEAD", "--"],
                                capture_output=True, text=True)
        require(result.returncode == 0, f"Tracked dependency sources changed: {location}")
        artifacts = location / ".lake/build/lib/lean"
        if receipts is not None:
            receipts.append({"name": package["name"], "revision": package["rev"],
                             "tracked_sources_clean": True,
                             "compiled_cache_reused": artifacts.is_dir()})
        # Some locked dependencies (e.g. Cli) are build tools and need no import
        # artifacts. A genuinely missing transitive import fails Lean's check.
        if not artifacts.is_dir():
            require(package["name"] != "mathlib", f"Missing Mathlib artifacts: {artifacts}")
            continue
        require(not any((artifacts / name).exists() for name in ["Pell", "TauCeti"]),
                f"Authored namespace appears in dependency cache: {artifacts}")
        paths.append(artifacts.resolve())
    return paths


def check_audit(output: str) -> dict[str, list[str]]:
    code = lean_code((ROOT / "checks/PellAudit.lean").read_text())
    expected = re.findall(r"(?m)^\s*#print\s+axioms\s+([\w.]+)\s*$", code)
    require(len(expected) == len(set(expected)), "Duplicate #print axioms endpoint")
    require(REQUIRED_ENDPOINTS.issubset(expected), "PellAudit omits a mandatory endpoint")
    # Both Lean output forms are valid, including an axiom-free theorem.
    entries = {}
    pattern = r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    for match in re.finditer(pattern, output):
        name = match.group(1)
        require(name not in entries, f"Duplicate audit result: {name}")
        axioms = [a.strip() for a in (match.group(2) or "").split(",") if a.strip()]
        require(set(axioms).issubset(ALLOWED_AXIOMS), f"Unexpected axioms for {name}: {axioms}")
        entries[name] = axioms
    require(set(entries) == set(expected),
            f"Incomplete axiom audit; missing={sorted(set(expected) - set(entries))}, "
            f"unexpected={sorted(set(entries) - set(expected))}")
    return entries


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=["lake", "direct"], default="lake")
    parser.add_argument("--dependencies", type=Path, default=package_root() / ".lake/packages",
                        help="Pinned external Lake packages directory (direct mode)")
    parser.add_argument("--git", help="Working Git executable, e.g. a portable Git on macOS")
    parser.add_argument("--lean", default="lean", help="Lean executable (direct mode)")
    parser.add_argument("--jobs", type=int, default=1,
                        help="Concurrent direct compiler processes, respecting imports (default: 1)")
    parser.add_argument("--lean-threads", type=int, default=int(os.environ.get("LEAN_NUM_THREADS", "2")),
                        help="Threads per direct Lean process (default: LEAN_NUM_THREADS or 2)")
    parser.add_argument("--logs", type=Path, help="New log directory; defaults to build/verification/<timestamp>")
    parser.add_argument("--frozen", action="store_true",
                        help="Also require the checked-in release manifests to match")
    args = parser.parse_args()
    require(args.jobs > 0 and args.lean_threads > 0, "Compiler job/thread counts must be positive")
    started = time.monotonic()
    logs = args.logs or ROOT / "build/verification" / time.strftime("%Y%m%d-%H%M%S")
    logs.mkdir(parents=True, exist_ok=False)
    modules = authored_modules()
    order = scan_and_order(modules)
    hashes = check_integrity(modules, frozen=args.frozen)
    (logs / "source-hashes.json").write_text(json.dumps(hashes, indent=2) + "\n")
    snapshot = logs / "SOURCE_SHA256SUMS"
    snapshot.write_text("".join(f"{value}  {name}\n" for name, value in sorted(hashes.items())))
    git = choose_git(args.git)
    dependency_receipts = []
    if args.mode == "lake":
        version = run(["lake", "env", "lean", "--version"], logs / "lean-version.log")
        check_lean_version(version)
        # Delete only generated authored artifacts. Preserve external Mathlib caches.
        for location in [package_root() / ".lake/build", package_root() / "vendor/TauCeti/.lake/build"]:
            if location.exists():
                shutil.rmtree(location)
        run(["lake", "exe", "cache", "get"], logs / "cache.log")
        dependency_path(package_root() / ".lake/packages", git, receipts=dependency_receipts)
        run(["lake", "--wfail", "--no-cache", "--rehash", "build", "Pell"], logs / "lake-build.log")
        targets = [("@TauCeti/+" if name.startswith("TauCeti.") else "+") + name + ":olean"
                   for name in order if name != "PellAudit"]
        run(["lake", "--wfail", "--no-cache", "--rehash", "build", *targets],
            logs / "lake-all-modules.log")
        audit_output = run(["lake", "env", "lean", "-DwarningAsError=true", "-T0",
                            str(ROOT / "checks/PellAudit.lean")], logs / "audit.log")
    else:
        version = run([args.lean, "--version"], logs / "lean-version.log")
        check_lean_version(version)
        dependency_dirs = dependency_path(args.dependencies.resolve(), git, receipts=dependency_receipts)
        # A new directory guarantees no pre-existing project/vendor olean is reused.
        with tempfile.TemporaryDirectory(prefix="pell-fresh-lean-") as temporary:
            build = Path(temporary)
            env = os.environ.copy()
            env["LEAN_PATH"] = os.pathsep.join(map(str, [build, *dependency_dirs]))
            env.pop("LEAN_SRC_PATH", None)
            indexes = {name: index for index, name in enumerate(order, 1)}

            def compile_module(name):
                source, package_root = modules[name]
                target = build.joinpath(*name.split(".")).with_suffix(".olean")
                target.parent.mkdir(parents=True, exist_ok=True)
                module_start = time.monotonic()
                source_hash = digest(source)
                require(source_hash == hashes[str(source.relative_to(ROOT))],
                        f"Source changed before compiling {name}")
                print(f"[{indexes[name]}/{len(order)}] {name}", flush=True)
                output = run([args.lean, "-DwarningAsError=true", "-T0", "-R", str(package_root),
                              "-j", str(args.lean_threads), "-o", str(target), str(source)],
                             logs / f"{name}.log", env=env)
                require(target.is_file(), f"Lean did not produce {target}")
                require(digest(source) == source_hash, f"Source changed while compiling {name}")
                entry = {"module": name, "source_sha256": source_hash,
                         "olean_sha256": digest(target),
                         "seconds": round(time.monotonic() - module_start, 3)}
                # Flush completed-module evidence even if a later module fails.
                (logs / f"{name}.receipt.json").write_text(json.dumps(entry, indent=2) + "\n")
                return entry

            receipt = execute_order(order, compile_dependencies(modules), args.jobs, compile_module)
            audit_output = (logs / "PellAudit.log").read_text()
            (logs / "modules.json").write_text(json.dumps(receipt, indent=2) + "\n")
            (logs / "audit.log").write_text(audit_output)
    axioms = check_audit(audit_output)
    final_modules = authored_modules()
    require(set(final_modules) == set(modules), "Authored module set changed during verification")
    scan_and_order(final_modules)
    final_hashes = check_integrity(final_modules, frozen=args.frozen)
    if args.mode == "direct":
        for entry in receipt:
            require(digest(modules[entry["module"]][0]) == entry["source_sha256"],
                    f"Compiled source changed afterward: {entry['module']}")
    assert_unchanged(hashes, final_hashes)
    summary = {"status": "passed", "mode": args.mode, "toolchain": TOOLCHAIN,
               "compiler_version": version.strip(),
               "mathlib_commit": MATHLIB_REV, "dependencies": dependency_receipts,
               "authored_modules": len(modules),
               "source_policy": "frozen" if args.frozen else "current",
               "source_snapshot_sha256": digest(snapshot),
               "frozen_manifest_sha256": digest(ROOT / "checks/SOURCE_SHA256SUMS") if args.frozen else None,
               "direct_jobs": args.jobs if args.mode == "direct" else None,
               "direct_lean_threads": args.lean_threads if args.mode == "direct" else None,
               "axiom_audit": axioms, "seconds": round(time.monotonic() - started, 3)}
    (logs / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(f"PASS: {len(modules)} modules; endpoint axioms allowed; logs: {logs}", flush=True)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, ValueError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
