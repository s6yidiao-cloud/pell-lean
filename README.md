# Pell: Lean formalization

This standalone project proves the three main theorems and both conclusions
of the Pell-unit corollary in **On the average of class numbers of indefinite
binary quadratic forms**, by Yijie Diao. The numbers below follow the
author's TeX manuscript, which is kept separately and is not distributed in
this repository.

| Manuscript result | Lean declaration in [`Pell/MainResults.lean`](Pell/MainResults.lean) |
| --- | --- |
| **Theorem 1.1** — Class-number averages | `PellPaper.field_class_average` |
| **Theorem 1.2** — Average number of odd-order ideal classes | `PellPaper.odd_class_average` |
| **Theorem 1.3** — Uniform exceptional-set bound for small Pell solutions | `PellPaper.uniform_exceptional` |
| **Corollary 1.4** — Logarithmic growth of the fundamental Pell solution | `PellPaper.pell_unit_growth_density` |
| **Corollary 1.4** — Growth beyond every fixed power | `PellPaper.fixed_power_density` |

The field/form average is bounded by
`C X^(3/2) sqrt(log log X)/(log X)^(3/2)` for every real `X ≥ 3`.
The odd-class average has denominator `(log X)^2`.
The exceptional-set theorem counts actual positive nonsquare integers `D < X`
with `ε_D ≤ D^θ`, uniformly for
`3 ≤ θ ≤ c sqrt(log X/log log X)`, with saving `c/θ²` and one absolute
threshold and implied constant. The corollary gives density-zero failures of
the stated `D`-dependent logarithmic growth and of every fixed-power bound.

Each endpoint is closed, with no supplied arithmetic or analytic premise.
The foundation is pinned Mathlib plus the additional proved Lean sources
included here. Only `propext`, `Classical.choice`, and `Quot.sound` are
allowed in the transitive endpoint axiom audit. No unproved Weil bound or
external numerical certificate is used.

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
The prepared workflow has not yet been credited with a hosted run.

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

This formalizes the main results. Two proved intermediate routes differ from
the manuscript: conductor class-number comparison replaces the all-order
L-value moment, and Lean uses `θ+1/4` restoration with a budgeted square-part
tail while the manuscript uses parameter `2θ`. The manuscript's sharper
standalone square-sieve lemma is not claimed as an independently formalized
result; the proof uses the product-hypothesis estimate sufficient for the main
theorems.

Statement fidelity and trust have separate independent AI reviews. No
independent human certification or independent proof-kernel replay is claimed.
Mathlib and its pinned external dependencies use their standard compiled caches.

## Repository access and source bundle

This is a private working repository. Access requires signing in to a GitHub
account authorized by the owner; private GitHub repositories do not offer a
shared passcode for anonymous visitors. Repository access should remain private
until the owner chooses otherwise.

This directory is the repository root. It contains Lean sources,
pinned configuration, result map, provenance, verification tools, evidence and
CI. The TeX manuscript is excluded from Git and source bundles.
Original-code licensing remains for the owner to choose;
upstream license notices are preserved.

Create the reproducible source-only bundle locally with:

```sh
python3 scripts/package.py
```

It writes `build/pell-lean-source.tar.gz`, excluding caches, compiled artifacts,
logs, Git internals, and macOS metadata. All additional proof sources are inside
it.
