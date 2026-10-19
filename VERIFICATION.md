# Verification record

**Passed.** The fresh isolated publication build compiled all **851** local
Lean modules: 767 Pell modules, 82 vendored TauCeti modules, `Pell.lean`, and
`PellAudit.lean`. Warnings were errors. All six literal endpoint-type
challenges compiled, and all twelve required transitive-axiom reports contain
exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Source and statement correspondence

The source of record is the author's separately held TeX manuscript, SHA-256:

```text
4290745fdf5234d3f1ccc6ed24cfdc48efde043241939b726713485b700099af
```

The manuscript is not distributed in the current repository. Its numbered
headline results are Theorems 1.1–1.3 and Corollary 1.4.

The public entry point is [`Pell/MainResults.lean`](Pell/MainResults.lean).
Its declarations have explicit source-shaped types, with no supplied
arithmetic or analytic premise. A separate AI reviewer inspected their
semantic closure, including actual fields and proper forms, finiteness,
odd-order ideal classes, strict cutoffs, exact logarithmic scales, uniform
constants and threshold, and discriminant-dependent growth. See
[`SEMANTIC_REVIEW.md`](evidence/verification/SEMANTIC_REVIEW.md) and the
[`paper-to-Lean map`](FORMALIZATION_MAP.md).

The proof uses a conductor comparison instead of the manuscript's all-order
L-value moment and a budgeted square-part restoration instead of its doubled
parameter argument. The sufficient product-hypothesis square sieve is proved;
the manuscript's sharper standalone lemma is not separately claimed. These
proof-route differences leave the headline conclusions unchanged.

## Fresh compiler and trust checks

The run took **40 minutes 13 seconds** (2412.712 seconds),
using 3 compiler processes with 2 Lean threads each.
Every Pell and vendored TauCeti proof object was newly compiled in one
temporary output directory. No old project or vendor object was on its
`LEAN_PATH`. Temporary proof objects were discarded after the gates passed.

Lean is pinned to `leanprover/lean4:v4.33.1`; Mathlib is locked at
`0df444a360eaa60ab8c11dca51a86af692955474`. All nine external Git source trees matched their
lockfile revisions and had no tracked changes. Their standard compiled caches
were reused. Matching source revisions do not independently establish that
arbitrary cached objects were built from those exact sources; those caches
remain the documented external artifact trust boundary.

The unfinished-proof/native-escape scan, complete local import-graph check,
source integrity checks before and after compilation, strict compiler checks,
all literal type challenges, all twelve axiom reports, and final unchanged
source checks passed. The verification guardrail regression tests also passed;
the exact output is in [`GUARDRAILS.md`](evidence/verification/GUARDRAILS.md).

The frozen manifest covers **875** source, manuscript, configuration,
status, verification, packaging, CI, documentation and provenance/license
files. Its SHA-256 is:

```text
d41eb07e74dcfb6bdfb5f322ed344ef488d30409888ec624679358e6f2baf062
```

This is the historical build manifest preserved in `evidence/verification/`.
After that run, the TeX source was removed from distribution, theorem numbers
were added to the README, and the checker and packager were adjusted to use
private-manuscript metadata without requiring a local TeX file. The current
repository-root manifest covers 874 files. All 851 Lean sources and dependency
pins remain byte-for-byte identical to the recorded build. The updated
verification guardrails and source-integrity checks were rerun successfully;
the historical compiler receipts have not been rewritten.

## Evidence and reproduction

Current evidence is in [`evidence/verification/`](evidence/verification/):

- [`summary.json`](evidence/verification/summary.json): passed outcome, actual
  compiler, dependency receipts, module count, elapsed time and all axiom lists;
- [`modules.json`](evidence/verification/modules.json): source/object hashes
  and compiler receipts for every local module;
- [`AXIOM_AUDIT.md`](evidence/verification/AXIOM_AUDIT.md): actual endpoint
  types, core definitions and raw transitive-axiom output;
- [`SOURCE_SHA256SUMS`](evidence/verification/SOURCE_SHA256SUMS) and
  [`source-hashes.json`](evidence/verification/source-hashes.json): the frozen
  manifest and source-integrity receipt used by the build;
- [`COMPILER.md`](evidence/verification/COMPILER.md),
  [`SEMANTIC_REVIEW.md`](evidence/verification/SEMANTIC_REVIEW.md), and
  [`TRUST_REVIEW.md`](evidence/verification/TRUST_REVIEW.md): command, scope,
  independent AI semantic review and trust-boundary review;
- [`PACKAGING_REVIEW.md`](evidence/verification/PACKAGING_REVIEW.md): source-only
  archive, extraction and reproducibility checks.

From a clean checkout after installing elan, Git and Python 3.10 or later:

```sh
lake exe cache get
python3 scripts/test_verify.py
python3 scripts/verify.py --mode direct --jobs 1
python3 scripts/package.py
```

The exact local command is recorded in `COMPILER.md`. A normal checkout uses
its own `.lake/packages` by default; `--dependencies PATH` selects an existing
pinned external cache. Standard Lake verification is also available with
`--mode lake`. Full local module logs remain under the ignored
`build/verification/publication/` directory.

No independent human certification or independently implemented proof-kernel
replay is claimed. Local verification receipts do not claim a hosted CI run.
