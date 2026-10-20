# Verification

## Recorded full build

[GitHub Actions run #9](https://github.com/s6yidiao-cloud/pell-lean/actions/runs/39291683619)
passed for source commit `52ace63b6294009c1a7633d7466302a1efc3e4be`.
It rebuilt all 857 local Lean modules: 773 Pell modules, 82 vendored TauCeti
modules, the importing root, and the central audit. All nine literal type
checks and 27 axiom reports passed, including seventeen mandatory endpoints.
Every report contained exactly `propext`, `Classical.choice`, and `Quot.sound`.
The verifier took 2233.681 seconds on Linux with Lean 4.33.1, one build job,
and two Lean threads.

The [full receipt](../checks/records/manuscript-primary-ci/summary.json) and
[compiler record](../checks/records/manuscript-primary-ci/COMPILER.md) preserve
that run. Its input manifest has SHA-256
`af22bfef63093774593ec7f16291452f6088bc641d22e79d7fbc2099fc94f467` and is
retained in [the receipt directory](../checks/records/manuscript-primary-ci/SOURCE_SHA256SUMS).

The current layout preserves all 857 Lean source files byte for byte from
that compiled snapshot. The directory structure, verifier, and source-packaging
workflow have since changed; the recorded run does not certify those changes.
Historical receipts retain their original paths and commands.

## Reproduction

Install elan, Git, and Python 3.10 or later, then run from the repository root:

```sh
cd formalization
lake exe cache get
cd ..
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/verify.py --mode direct
```

Lean is pinned in [`lean-toolchain`](../formalization/lean-toolchain) to
`leanprover/lean4:v4.33.1`; Mathlib is locked at
`0df444a360eaa60ab8c11dca51a86af692955474` in the
[Lake manifest](../formalization/lake-manifest.json). The verifier checks
external source revisions and tracked-source cleanliness, then compiles all
project and vendored TauCeti modules into a fresh temporary directory with
warnings as errors, including modules outside the main results' import closure.

By default, verification snapshots the current file contents and checks that
they stay unchanged during the run. It records those input hashes alongside
the compiler results. This permits normal source edits without manually
updating a checksum file. Use `--frozen` when reproducing a release whose
inputs must also match [`checks/SOURCE_SHA256SUMS`](../checks/SOURCE_SHA256SUMS).
To prepare a new frozen release, run `python3 scripts/freeze.py`, then verify
with `--frozen`. Historical manifests under `checks/records/` are never updated.

Dependencies are read from `formalization/.lake/packages` by default. To use a
separate pinned dependency cache and retain logs in a chosen location:

```sh
python3 scripts/verify.py --mode direct --dependencies ../.lake/packages --jobs 3 --lean-threads 2 --logs build/verification/current
```

Standard Lake verification is available with `--mode lake`. The
[GitHub Actions workflow](../.github/workflows/lean.yml) runs the guardrail
tests and fresh direct verification on relevant pushes. A hosted run is
successful only when its Actions result says so.
Documentation-only commits skip this workflow. Network setup is retried up to
three times; compilation and audit failures remain fatal.

## Audit and trust boundary

[`formalization/Pell.lean`](../formalization/Pell.lean) imports the proof
library. [`checks/PellAudit.lean`](../checks/PellAudit.lean) is a separate
verification entry point: it checks nine literal theorem types, prints core
definitions, and reports 27 transitive-axiom lists. Seventeen named endpoints
are mandatory. It also traverses the proofs and types of the five public main
results and their five implementation endpoints, requiring the manuscript
restoration and sieve and rejecting the removed square-part restoration route.

Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. Unfinished
proofs, custom axioms, and compiler-trusted proof escapes are rejected. The
[proof map](proof-map.md), [status file](../checks/formalization.yaml), and
[independent AI review](../checks/records/PRIMARY_MANUSCRIPT_REVIEW.md) record
the statement correspondence and dependency review.

Compiled external dependency caches are reused. Their source revisions are
checked; this does not independently replay their compiled proof objects.
Independent proof-kernel replay and independent human certification remain
unclaimed.

## Earlier successful builds

These unchanged receipts describe their own frozen snapshots.

| Snapshot | Modules | Literal types | Axiom reports | Elapsed time | Receipt |
| --- | ---: | ---: | ---: | ---: | --- |
| Publication baseline | 851 | 6 | 12 | 2412.712 s | [summary](../checks/records/summary.json) |
| Standalone manuscript extensions | 854 | 8 | 22 | 946.539 s | [summary](../checks/records/manuscript-extensions/summary.json) |

Both passed, with exactly the three permitted standard axioms in each report.
The extension build added the manuscript proofs as separate endpoints; run #9
checked their use in the main results. Each receipt directory contains source
and object hashes, actual theorem types, raw axiom output, and compiler details.
The baseline also contains semantic, trust, packaging, and guardrail reviews.

## Manuscript provenance

The source of record is the author's separately held `main_v4.tex`, SHA-256:

```text
4290745fdf5234d3f1ccc6ed24cfdc48efde043241939b726713485b700099af
```

The [manuscript PDF](../paper/main.pdf) is included. The numbered main results
are Theorems 1.1–1.3 and Corollary 1.4. The
[original semantic review](../checks/records/SEMANTIC_REVIEW.md) checks fields,
proper forms, finiteness, odd-order ideal classes, cutoffs, logarithmic scales,
uniform constants, and discriminant-dependent growth.
