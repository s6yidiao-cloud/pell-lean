# Pell: Lean formalization

Lean proofs of the main results in
[*On the average of class numbers of indefinite binary quadratic forms*](paper/main.pdf).

| Manuscript result | Lean declaration in [`Pell/MainResults.lean`](Pell/MainResults.lean) |
| --- | --- |
| **Theorem 1.1** — Class-number averages | `PellPaper.field_class_average` |
| **Theorem 1.2** — Average number of odd-order ideal classes | `PellPaper.odd_class_average` |
| **Theorem 1.3** — Uniform exceptional-set bound for small Pell solutions | `PellPaper.uniform_exceptional` |
| **Corollary 1.4** — Logarithmic growth of the fundamental Pell solution | `PellPaper.pell_unit_growth_density` |
| **Corollary 1.4** — Growth beyond every fixed power | `PellPaper.fixed_power_density` |

## Build

Install [elan](https://github.com/leanprover/elan), Python 3.10 or later, and Git.
The project uses Lean and Mathlib `v4.33.1`.
Keep `lean-toolchain` and `lake-manifest.json` unchanged.
From the repository root, run:

```sh
lake exe cache get
python3 scripts/test_verify.py
python3 scripts/verify.py --mode direct --jobs 1
```

The verifier rebuilds all 857 local Lean modules, treats warnings as errors,
and checks the theorem statements, axiom lists, and source hashes.
It uses Mathlib's compiled cache.
The same checks run in [GitHub Actions](.github/workflows/lean.yml).
See [VERIFICATION.md](VERIFICATION.md) for results and build options.

## Proofs

[Pell.lean](Pell.lean) imports the formalization.
The main theorem statements are in [Pell/MainResults.lean](Pell/MainResults.lean).
The [proof map](FORMALIZATION_MAP.md) lists the corresponding manuscript results
and explains the intermediate arguments.

[THIRD_PARTY.md](THIRD_PARTY.md) gives the sources and licenses for included
proofs adapted from other projects.
The [verification records](evidence/verification/) include the compiler and
independent AI review results; they do not constitute human certification.

## Source bundle

The repository includes the manuscript PDF; its TeX source is kept separately.
To create a reproducible archive of the sources, run:

```sh
python3 scripts/package.py
```

The archive is written to `build/pell-lean-source.tar.gz`.
It excludes caches, compiled files, Git metadata, and private TeX sources.

When changing a file covered by `SOURCE_SHA256SUMS`, update its checksum in the
same commit.
Keep the historical manifests under `evidence/verification/` unchanged.
