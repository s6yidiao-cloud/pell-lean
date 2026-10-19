# Pell: Lean formalization

This project formalizes the main results of
[**On the average of class numbers of indefinite binary quadratic forms**](paper/main.pdf).

| Manuscript result | Lean declaration in [`Pell/MainResults.lean`](Pell/MainResults.lean) |
| --- | --- |
| **Theorem 1.1** — Class-number averages | `PellPaper.field_class_average` |
| **Theorem 1.2** — Average number of odd-order ideal classes | `PellPaper.odd_class_average` |
| **Theorem 1.3** — Uniform exceptional-set bound for small Pell solutions | `PellPaper.uniform_exceptional` |
| **Corollary 1.4** — Logarithmic growth of the fundamental Pell solution | `PellPaper.pell_unit_growth_density` |
| **Corollary 1.4** — Growth beyond every fixed power | `PellPaper.fixed_power_density` |

## Build and verify

Install [elan](https://github.com/leanprover/elan), Python 3.10 or later, and Git.
Lean and Mathlib are pinned to `v4.33.1`; retain `lake-manifest.json`.
From this directory:

```sh
lake exe cache get
python3 scripts/test_verify.py
python3 scripts/verify.py --mode direct --jobs 1
```

The verifier creates new outputs for every Pell and vendored TauCeti module,
including modules outside the main import closure. It reuses only pinned
external dependency caches, checks their source revisions and tracked changes,
promotes warnings to errors, scans for unfinished proofs, checks six literal
endpoint types, and audits all twelve required endpoint axiom reports.
Source, checker, packager and CI hashes are checked before and after the build.
An initial build can take substantial time and memory.

The alternative standard Lake build is
`python3 scripts/verify.py --mode lake`. A normal checkout uses its own
`.lake/packages` by default; `--dependencies PATH` selects an existing pinned
external cache for direct mode. See [`VERIFICATION.md`](VERIFICATION.md) and
[`evidence/verification/`](evidence/verification/) for recorded checks,
commands, receipts, and environment limits.
CI is configured in [`.github/workflows/lean.yml`](.github/workflows/lean.yml).
GitHub Actions runs the same guardrail tests and fresh verification command.

## Scope and proof route

Start at [`Pell.lean`](Pell.lean) and [`Pell/MainResults.lean`](Pell/MainResults.lean).
The [`paper-to-Lean map`](FORMALIZATION_MAP.md) records the exact semantic
closure, proof route and scope differences. [`formalization.yaml`](formalization.yaml)
provides machine-readable provenance and status.

The proof starts from Mathlib's fundamental Pell solution, factors
`(t-1)(t+1)=Du²`, and uses determinant relations, dyadic boxes, quadratic
ideals, lattice counts, an elementary square sieve, and square-part restoration.
The included genus-theory proof closure is rebuilt from source; adapted
FormalPantheon and PrimeNumberTheoremAnd proofs are also included.
See [`THIRD_PARTY.md`](THIRD_PARTY.md) for attribution, pins and licenses.

The main results are formalized. Two intermediate arguments differ from the
manuscript. For the class-number average, Lean passes from fundamental
discriminants to all orders using a bound for class numbers in terms of the
conductor, in place of the manuscript's all-order L-value second-moment
estimate. To pass from squarefree to general radicands, Lean applies the
squarefree estimate at `θ+1/4`, sums over small square factors, and bounds the
contribution of large square factors separately; the manuscript uses parameter
`2θ`.

The square-sieve estimate proved in Lean assumes `M ≤ UV`, where `U,V` are the
dyadic box sizes and `M` controls the subdivision by slope. This estimate
suffices for the main theorems. The manuscript's sharper standalone square-sieve
lemma is not separately formalized.

Statement fidelity and trust have separate independent AI reviews. No
independent human certification or independent proof-kernel replay is claimed.
Mathlib and its pinned external dependencies use their standard compiled caches.

## Source bundle

This directory is the repository root. It contains Lean sources,
pinned configuration, result map, provenance, verification tools, evidence and
CI, together with the [manuscript PDF](paper/main.pdf). The TeX source is
excluded from Git and repository bundles.
Original-code licensing remains for the owner to choose;
upstream license notices are preserved.

Create the reproducible repository bundle locally with:

```sh
python3 scripts/package.py
```

It writes `build/pell-lean-source.tar.gz`, excluding caches, compiled artifacts,
logs, Git internals, and macOS metadata. All additional proof sources are inside
it.

When updating the repository, commit changed files and their matching entries
in the root `SOURCE_SHA256SUMS` together. Uploading them in separate commits
causes CI to reject the intermediate version with a hash mismatch. Keep the
historical manifests in `evidence/verification/` unchanged.
