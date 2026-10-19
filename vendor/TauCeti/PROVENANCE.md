# Vendored TauCeti quadratic genus theory

This directory contains the exact local import closure needed for the
ordinary quadratic class-group genus bound used by the Pell project.

- Upstream repository: <https://github.com/TauCetiProject/TauCeti>
- Vendored snapshot: `686d8bf2bd972c14c9d3e080024a7001addf0660`
- Snapshot date: 2026-09-14
- Theorem-introduction commit:
  `f50077caad86824f718a9a09db55e2af7b83c1a9`
- Upstream license: Apache License 2.0; see `LICENSE`.
- Local Lean toolchain and Mathlib target: `v4.33.1`, matching Pell.

The closure consists of the 82 TauCeti modules reachable from

```lean
TauCeti.NumberTheory.Multiquadratic.Quadratic.TwoRank
TauCeti.NumberTheory.NumberField.ClassGroupElementaryTwoQuotient
```

`SOURCE_SHA256SUMS` records every vendored Lean source after the compatibility
and attribution edits below.

## Compatibility edits for Mathlib v4.33.1

Upstream targets Lean `v4.34.0-rc2` and a newer Mathlib master. The selected
closure needs only these source-level compatibility edits on Pell's pin:

1. In `TauCeti/Algebra/Squarefree.lean`, a private compatibility copy of the
   later Mathlib theorem `exists_sq_mul_squarefree` is included and used once.
   Its proof is the 14-line upstream Mathlib proof introduced by
   `leanprover-community/mathlib4@50838443dcce6c0ebd2abd7c1c4fcf45661cfd16`.
2. Twenty-three uses of the post-pin names `ite_eq_left` and `ite_eq_right`
   are replaced by their v4.33.1 names `if_pos` and `if_neg`. They occur on
   18 source lines in these five files:
   - `TauCeti/NumberTheory/Multiquadratic/FundamentalDiscriminant/OfSquarefree.lean`
   - `TauCeti/NumberTheory/Multiquadratic/Legendre/EvenPrimeDiscriminant.lean`
   - `TauCeti/NumberTheory/Multiquadratic/Legendre/PrimeDiscriminant/Basic.lean`
   - `TauCeti/NumberTheory/Multiquadratic/Legendre/PrimeDiscriminant/Character.lean`
   - `TauCeti/NumberTheory/Multiquadratic/Quadratic/GenusCharacter/Basic.lean`

No mathematical statement or public TauCeti API was changed. The two target
modules build with warnings treated as errors on Pell's pin.

## Attribution and provenance audit (2026-10-13)

The 82 local Git blob hashes were compared with the complete official GitHub
tree at the snapshot commit above. Before restoring attribution notices, 76
files were byte-identical to upstream; the six remaining files were exactly
the compatibility files listed above. The five conditional-branch files were
also compared with the upstream text and differed only by the documented
`ite_eq_left`/`ite_eq_right` replacements. The squarefree proof is the proof
introduced in the named Mathlib commit, under its private compatibility name.

Each compatibility file now carries a prominent modification notice. The
Mathlib compatibility proof retains the source file's Aaron Anderson
copyright and author notices; [MATHLIB_LICENSE](MATHLIB_LICENSE) provides the
upstream Apache-2.0 license.

The following FLT adaptations now also retain the exact copyright and author
notices from `ImperialCollegeLondon/FLT@bc2fe8ff7396`:

- `TauCeti/FieldTheory/Galois/Basic.lean`;
- `TauCeti/LinearAlgebra/Dimension/IsQuadraticExtension.lean`;
- `TauCeti/RingTheory/Norm/Quadratic.lean`.

All three upstream files give `Copyright (c) 2026 Kevin Buzzard. All rights
reserved.` The first and third list `Authors: Kevin Buzzard, Claude`; the
dimension file lists `Authors: Michael Stoll, Claude`, which also corrects
the older prose attribution in that file. These are comment-only repairs.
The exact TauCeti snapshot's complete repository tree contains `LICENSE` and
no `NOTICE` file. Other upstream adaptation attributions remain in their
source docstrings.
