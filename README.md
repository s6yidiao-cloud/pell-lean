# Pell: Lean formalization

Lean proofs of the main results in
[*On the average of class numbers of indefinite binary quadratic forms*](paper/main.pdf).

| Manuscript result | Declaration in [`MainResults.lean`](formalization/Pell/MainResults.lean) |
| --- | --- |
| Theorem 1.1 — Class-number averages | `PellPaper.field_class_average` |
| Theorem 1.2 — Average number of odd-order ideal classes | `PellPaper.odd_class_average` |
| Theorem 1.3 — Uniform exceptional-set bound for small Pell solutions | `PellPaper.uniform_exceptional` |
| Corollary 1.4 — Logarithmic growth of the fundamental Pell solution | `PellPaper.pell_unit_growth_density` |
| Corollary 1.4 — Growth beyond every fixed power | `PellPaper.fixed_power_density` |

## Build and verify

Install [elan](https://github.com/leanprover/elan), Python 3.10 or later, and Git.
Lean and Mathlib are pinned to `v4.33.1`. From the repository root:

```sh
cd formalization
lake exe cache get
cd ..
python3 scripts/verify.py --mode direct
```

The verifier snapshots the current source files, rebuilds all 857 local Lean
modules with warnings as errors, and checks theorem types, allowed axioms, and
proof dependencies. Add `--frozen` to require the checked-in release manifest.
Documentation-only changes skip Lean CI. See
[verification](docs/verification.md) for the recorded build and options.

## Repository

- [`formalization/`](formalization/) contains the Lean project and vendored proofs.
  [`Pell.lean`](formalization/Pell.lean) is the library entry point: importing
  `Pell` makes the formalized results available.
- [`checks/`](checks/) contains the audit, machine-readable status, and build
  records. [`PellAudit.lean`](checks/PellAudit.lean) checks exact theorem types,
  reports transitive axioms, and verifies the required proof routes.
- [`docs/`](docs/) contains the [proof map](docs/proof-map.md),
  [verification details](docs/verification.md), and
  [third-party provenance](docs/third-party.md).
- [`paper/`](paper/) contains the manuscript PDF; the TeX source is held separately.
- [`scripts/`](scripts/) contains verification and source-packaging tools.

## Source bundle

```sh
python3 scripts/package.py
```

This writes `build/pell-lean-source.tar.gz` with a freshly generated source
manifest; routine documentation edits need no manual checksum updates.
Caches, compiled files, Git metadata, and private TeX sources are
excluded. Historical records under [`checks/records/`](checks/records/) retain
the exact contents of their recorded snapshots.

## License

The original Lean code is licensed under [Apache 2.0](LICENSE). Third-party
attributions and licenses are listed in [NOTICE](NOTICE) and
[third-party provenance](docs/third-party.md). The manuscript PDF is outside
the code license.
