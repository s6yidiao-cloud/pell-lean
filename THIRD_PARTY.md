# Third-party proof sources

These are proved Lean sources compiled from Mathlib, not external theorem
assumptions. Attribution and modification notices remain in source headers.

| Source | Included code | Revision and notice |
| --- | --- | --- |
| [TauCeti](https://github.com/TauCetiProject/TauCeti) | `vendor/TauCeti`, 82 modules for quadratic genus theory | Snapshot `686d8bf2bd972c14c9d3e080024a7001addf0660`; compatibility edits, restored upstream notices, hashes, and source details in `vendor/TauCeti/PROVENANCE.md`; license in `vendor/TauCeti/LICENSE`. |
| [FormalPantheon](https://github.com/frenzymath/FormalPantheon) | `NonprincipalDirichletPolyaVinogradov`, `DirichletCharacterAbelContinuation`, `DirichletCharacterOrderedLValue`, `ReciprocalPrefixTailBound` | Commit `ffbb65c21afc8a36ace67720f1b0df1c63d26bd1`; upstream paths and modification notices in source headers; license in `third_party/FormalPantheon-LICENSE`. |
| [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) | `WilsonSelbergShortUpperWeights` | Commit `a5154676af9aa3095150ee410cdda80555aa0642`, upstream `PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/Selberg.lean`; Arend Mellendijk copyright, author credit and adaptation notice retained; license in `third_party/PrimeNumberTheoremAnd-LICENSE`. |
| [Mathlib](https://github.com/leanprover-community/mathlib4) | Lake dependency and a later compatibility lemma in TauCeti | Dependency commit `0df444a360eaa60ab8c11dca51a86af692955474`; compatibility proof revision in TauCeti provenance; license in the dependency and `vendor/TauCeti/MATHLIB_LICENSE`. |

Three TauCeti files include upstream FLT-derived proofs. Their exact upstream
copyright and author notices are preserved in their headers; their provenance
is documented in the vendor directory. All listed third-party code is Apache
2.0. The previous package omitted `third_party/` despite source references to
its licenses; this release includes both complete license texts.

No additional license grant has been assigned to the original Pell source or
manuscript. The repository owner may choose those separately.
