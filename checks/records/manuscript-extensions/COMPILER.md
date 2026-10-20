# Fresh manuscript-extension compiler receipt

Outcome: **passed**, all **854** local modules (770 Pell modules, 82 vendored
TauCeti modules, importing root and central audit). Warnings were errors.
All eight literal type challenges and twenty-two transitive-axiom reports
passed; every report contains exactly the three permitted standard axioms.
The actual proof/type route traversal found 3,862 project constants and no
old arbitrary-radicand endpoint dependency.

Compiler:

```text
Lean (version 4.33.1, arm64-apple-darwin24.6.0, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)
```

Command from the repository root:

```sh
python3 scripts/verify.py --mode direct --dependencies ../.lake/packages --jobs 3 --lean-threads 2 --logs build/verification/manuscript-extensions
```

Elapsed time: **946.539 seconds**. The verifier compiled all local
Pell and vendored proof objects into one new temporary directory; no old
project object was on its `LEAN_PATH`. It checked pinned external source
revisions and tracked-source cleanliness and reused their standard caches.
It used the installed portable Git because the system Git requires an Xcode
license. No external service was contacted to publish the result.

The source manifest was frozen before compilation and checked unchanged
afterward. Its SHA-256 is
`482377b5a6e21f166249597f102f8a6defddce2d4593d0e0c9841b89e0981db3`.
The exact manifest is preserved in this directory. After the successful run,
these compiler receipts were copied into the public evidence directory and
the repository-root manifest was extended to cover them. No compiled Lean
source, checker, toolchain, status or existing documentation changed after the
fresh run. The nine verification guardrail tests also passed before the run.

`modules.json` records source and object hashes for every module;
`source-hashes.json` records all 880 protected input files;
`summary.json` contains the machine-readable outcome and all axiom lists;
`AXIOM_AUDIT.md` preserves the actual central-audit output. Individual compiler
logs remain in the ignored build directory. The earlier publication receipts
remain unchanged.

The independent semantic review is
`../MANUSCRIPT_EXTENSIONS_REVIEW.md`. No human certification or replay by a
separately implemented proof kernel is claimed. External compiled caches
retain the documented artifact trust boundary.
