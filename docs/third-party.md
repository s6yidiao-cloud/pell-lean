# Third-party proof sources

Included and adapted proofs are compiled from Lean source. Their copyright,
author, and modification notices are preserved in the source headers.

| Source | Included code | Revision and license |
| --- | --- | --- |
| [TauCeti](https://github.com/TauCetiProject/TauCeti) | [`formalization/vendor/TauCeti`](../formalization/vendor/TauCeti/), 82 modules for quadratic genus theory | Snapshot `686d8bf2bd972c14c9d3e080024a7001addf0660`; [provenance and compatibility edits](../formalization/vendor/TauCeti/PROVENANCE.md); [Apache-2.0 license](../formalization/vendor/TauCeti/LICENSE). |
| [FormalPantheon](https://github.com/frenzymath/FormalPantheon) | `NonprincipalDirichletPolyaVinogradov`, `DirichletCharacterAbelContinuation`, `DirichletCharacterOrderedLValue`, `ReciprocalPrefixTailBound` in `formalization/Pell/` | Commit `ffbb65c21afc8a36ace67720f1b0df1c63d26bd1`; upstream paths and modifications in source headers; [Apache-2.0 license](licenses/FormalPantheon-LICENSE). |
| [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) | `formalization/Pell/WilsonSelbergShortUpperWeights.lean` | Commit `a5154676af9aa3095150ee410cdda80555aa0642`, upstream `PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/Selberg.lean`; Arend Mellendijk copyright, author credit, and adaptation notice retained; [Apache-2.0 license](licenses/PrimeNumberTheoremAnd-LICENSE). |
| [Mathlib](https://github.com/leanprover-community/mathlib4) | Lake dependency and a later compatibility lemma in TauCeti | Dependency commit `0df444a360eaa60ab8c11dca51a86af692955474`; compatibility proof revision in [TauCeti provenance](../formalization/vendor/TauCeti/PROVENANCE.md); [Apache-2.0 license](../formalization/vendor/TauCeti/MATHLIB_LICENSE). |

Three TauCeti files contain upstream FLT-derived proofs. Their exact upstream
copyright and author notices are retained; their provenance is recorded in the
vendor directory. All listed third-party code is Apache-2.0. See the root
[NOTICE](../NOTICE) for the attribution summary.

The original Pell Lean code is licensed under the root [Apache-2.0
license](../LICENSE). The manuscript PDF is outside the code license.
