# Verification record

The current proofs use the manuscript's `2θ` restoration and parameterized
square sieve in the main results. The class-number proof still uses a
fundamental-discriminant second moment followed by a conductor comparison;
see [README.md](README.md) for the precise difference from the manuscript.

## Current checks

The fresh full build passed in [GitHub Actions run #9](https://github.com/s6yidiao-cloud/pell-lean/actions/runs/39291683619)
for source commit `52ace63b6294009c1a7633d7466302a1efc3e4be`. It rebuilt all
857 local Lean modules: 773 Pell modules, 82 vendored TauCeti modules, the
importing root, and the central audit. All nine literal type checks and
27 axiom reports passed, including all seventeen mandatory endpoints; every
report contains exactly the three permitted standard axioms. The verifier
completed in 2233.681 seconds on Linux with Lean 4.33.1, one build job and
two Lean threads; the workflow took 40 minutes 29 seconds. The full receipt
is [`summary.json`](evidence/verification/manuscript-primary-ci/summary.json),
with commands and compiler details in
[`COMPILER.md`](evidence/verification/manuscript-primary-ci/COMPILER.md).

All 857 current Lean source hashes match that compiled snapshot. Subsequent
changes contain documentation and receipt followups only; the proofs and
verifier are unchanged. The frozen CI input manifest has SHA-256
`af22bfef63093774593ec7f16291452f6088bc641d22e79d7fbc2099fc94f467`
and is retained in
[`manuscript-primary-ci/SOURCE_SHA256SUMS`](evidence/verification/manuscript-primary-ci/SOURCE_SHA256SUMS).
The earlier focused strict compilation of all 67 affected modules also passed.

[`PellAudit.lean`](PellAudit.lean) checks nine literal theorem types and
27 transitive-axiom reports. Seventeen reports are mandatory endpoints of
the verifier. The permitted axioms are `propext`, `Classical.choice`, and
`Quot.sound`; unfinished proofs, custom axioms and compiler-trusted proof
escapes are rejected. The audit also traverses the actual proofs and types
of all five public main results and their five implementation endpoints.
Each must use the manuscript restoration and sieve, with no dependency on
the removed square-part restoration lemmas.

The independent semantic review of this replacement is recorded in
[`PRIMARY_MANUSCRIPT_REVIEW.md`](evidence/verification/PRIMARY_MANUSCRIPT_REVIEW.md).
The [proof map](FORMALIZATION_MAP.md) and [status file](formalization.yaml)
record the statements and their source correspondence.

## Reproduction

Install elan, Git and Python 3.10 or later, then run from the repository root:

```sh
lake exe cache get
python3 scripts/test_verify.py
python3 scripts/verify.py --mode direct --jobs 1
```

Lean is pinned to `leanprover/lean4:v4.33.1`; Mathlib is locked at
`0df444a360eaa60ab8c11dca51a86af692955474`. The verifier checks external
source revisions and tracked-source cleanliness. It rebuilds all project
and vendored TauCeti modules in a new temporary directory with warnings
as errors, including modules not imported by the main results. It checks
the source manifest before and after compilation.

A normal checkout uses its own `.lake/packages`. The local command for a
separate pinned dependency cache is:

```sh
python3 scripts/verify.py --mode direct --dependencies ../.lake/packages --jobs 3 --lean-threads 2 --logs build/verification/manuscript-primary
```

Standard Lake verification is available with `--mode lake`. GitHub Actions
runs the guardrail tests and a fresh direct build on each relevant push.
A hosted run is successful only when its Actions result says so.

External compiled dependency caches are reused. Matching source revisions
do not independently establish that arbitrary cached objects were built
from those sources. No independently implemented proof-kernel replay or
independent human certification is claimed.

## Earlier successful builds

These receipts describe their frozen snapshots, rather than the current
replacement proofs. They remain unchanged.

| Snapshot | Modules | Literal types | Axiom reports | Elapsed time | Receipts |
| --- | ---: | ---: | ---: | ---: | --- |
| Publication baseline | 851 | 6 | 12 | 2412.712 s | [`summary.json`](evidence/verification/summary.json) |
| Standalone manuscript extensions | 854 | 8 | 22 | 946.539 s | [`summary.json`](evidence/verification/manuscript-extensions/summary.json) |

Both builds passed. Every reported theorem depended on exactly the three
permitted standard axioms. The extension build added the manuscript proofs
as separate endpoints; the current revision replaces the main proof routes
with them.

Each receipt directory includes `modules.json` with source and object hashes,
`source-hashes.json` and `SOURCE_SHA256SUMS` for the frozen inputs,
`AXIOM_AUDIT.md` with actual theorem types and raw axiom output, and
`COMPILER.md` with the command and compiler details. The original baseline
also includes semantic, trust, packaging and guardrail reviews.

## Manuscript provenance

The source of record is the author's separately held `main_v4.tex`, SHA-256:

```text
4290745fdf5234d3f1ccc6ed24cfdc48efde043241939b726713485b700099af
```

The [PDF](paper/main.pdf) is included; the TeX source is kept separately.
The numbered main results are Theorems 1.1–1.3 and Corollary 1.4.
The original [semantic review](evidence/verification/SEMANTIC_REVIEW.md)
checks fields, proper forms, finiteness, odd-order ideal classes, cutoffs,
logarithmic scales, uniform constants and discriminant-dependent growth.
