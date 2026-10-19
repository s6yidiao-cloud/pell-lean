# Paper-to-Lean proof map

The source of record is the author's separately held TeX manuscript, SHA-256
`4290745fdf5234d3f1ccc6ed24cfdc48efde043241939b726713485b700099af`.
The manuscript source is not distributed in this repository. The source labels
and line ranges below identify that private snapshot; its headline results are
Theorems 1.1–1.3 and Corollary 1.4.

## Frozen headline statements

All entries have review tier **Critical** because statement fidelity, actual
arithmetic objects, finiteness, and uniform quantifiers determine whether the
formalization proves the requested mathematics. Separate AI semantic and trust
reviews inspected these interfaces. No independent human certification is
claimed. Compiler outcomes and the exact frozen source are recorded separately
in [`VERIFICATION.md`](VERIFICATION.md) and `evidence/verification/`.

| Source label and lines | Intended statement | Exact Lean declaration | Status and trust | Scope difference |
| --- | --- | --- | --- | --- |
| `T:field-class-average`, 134–141 | For every real `X ≥ 3`, the actual field class-number sum is at most the proper primitive form-class sum over all positive nonsquare `D ≡ 0,1 mod 4`, `D < X`; the latter is bounded by one constant times `X^(3/2) sqrt(log log X)/(log X)^(3/2)`. | `PellPaper.field_class_average`, `Pell/MainResults.lean` | Closed proof from `final_field_class_average.2`; accepted axioms only. | None in the displayed result. Finiteness of every form quotient is also proved separately. |
| `T:odd-class-average`, 197–203 | One constant bounds the sum of the numbers of odd-order ordinary ideal classes over the same fields by `X^(3/2) sqrt(log log X)/(log X)^2` for every real `X ≥ 3`. | `PellPaper.odd_class_average`, `Pell/MainResults.lean` | Closed proof from `final_odd_class_average`; accepted axioms only. | None; the odd-part representation has a proved literal interpretation. |
| `T:uniform-exceptional`, 243–251 | Absolute positive `c,C` and one threshold in `X` give `E_θ(X) ≤ C X^(1-c/θ²)`, uniformly for `3 ≤ θ ≤ c sqrt(log X/log log X)`. | `PellPaper.uniform_exceptional`, `Pell/MainResults.lean` | Closed proof from `final_uniform_exceptional`; accepted axioms only. | None: strict cutoff, same `c` in range and saving, and threshold before `∀ θ`. |
| `C:pell-unit-growth`, 256–263 | Density-zero failures of `log ε_D ≥ c (log D)^(3/2)/sqrt(log log D)` for an absolute positive `c`, and of `ε_D > D^θ` for each fixed `θ > 0`. | `PellPaper.pell_unit_growth_density`, `PellPaper.fixed_power_density`, `Pell/MainResults.lean` | Closed proofs from the corresponding `final_*` endpoints; accepted axioms only. | The first failure set uses `≤`, so its complement gives the stronger strict lower bound. Division by `X` gives the same density-one meaning among nonsquares, since squares have density zero. |

These are closed proofs rather than conditional interfaces. Intermediate
reductions retain explicit hypotheses in their theorem types; the final
endpoints discharge all required inputs. A module's presence does not imply
that every result it discusses is a completed source lemma.

## Semantic closure and non-vacuity

- `QuadraticOrderDiscriminants.lean`: positivity, nonsquareness, congruence
  `0` or `1` modulo `4`, and strict real cutoff.
- `QuadraticFormProperEquivalence.lean`: primitive integral forms
  `ax²+bxy+cy²`, discriminant `b²-4ac`, modulo `SL₂(ℤ)` substitutions.
- `RealQuadraticOrderClassAverage.lean`: `properOrderFormClassSum` counts
  these actual quotients. `proper_form_classes_finite` rules out the
  infinite-type zero-cardinality loophole at every order discriminant.
- `RealQuadraticFieldIsomorphismClasses.lean` and
  `RealQuadraticFieldClassSum.lean`: actual degree-two number fields admitting
  a real embedding, modulo rational algebra equivalence. Discriminants and
  class numbers are Mathlib's `NumberField.discr` and `NumberField.classNumber`.
  Classification by positive fundamental discriminants and exact sum
  transport are proved, not assumed.
- `RealQuadraticFieldOddClassSum.lean`: `ordCompl[2]` of the actual class
  number. `OddClassMeaning.lean` proves
  `realQuadraticFieldOddClassNumber_eq_card_oddOrderClasses`, identifying it
  with `Nat.card {c : ClassGroup (𝓞 F) // Odd (orderOf c)}`.
- `Definitions.lean`: `epsilon` is `x+y sqrt D`; the small-solution predicate
  uses Mathlib's positive fundamental solution. Existence and uniqueness are
  proved equivalent to a positive nonsquare radicand.
- `FinalPaperResults.lean`: `paperExceptionalSet` restores exactly `0 < D < X`
  from the closed-cutoff implementation API. `paperPellGrowthBadSet` uses the
  literal `D`-dependent logarithmic expression. `uniformQ θ ≤ θ` for `θ ≥ 3`
  transports the intermediate saving with one reduced positive constant.
- `classAverageScale` and `oddClassAverageScale`: the exact real powers and
  logarithms in the manuscript. Constants precede every cutoff; compact-range
  completion extends the bounds to all `X ≥ 3`.

`PellAudit.lean` checks six literal endpoint types and prints endpoint types,
core definitions, and twelve transitive-axiom lists. The semantic review checked
definitions, domains, constants, strict inequalities, density interpretation,
and hidden arithmetic premises. It did not independently re-prove all
compiler-checked algebra.

## Route through the source and proof

| Manuscript stage | Key Lean modules | Relationship |
| --- | --- | --- |
| §2, `s:pell-factorizations` | `Definitions`, `PellFactorization`, `DyadicFactorSeparation` | Mathlib fundamental solutions, Pell factorization, dyadic encoding. |
| §3, `s:square-sieve`, `s:lattice-counting` | `DyadicBalancedSquareSieveEnvelopeElementary`, `Main3LargeAnalyticRealTwoPlaceLatticeBallGrowth` and their imports | Elementary complete-character bound, square detector, lattice completion. |
| §4, `s:determinant-method` | `TwoLayerVanishing`, `IntegralDeterminantVanishing`, `GeneralBidegreeAuxiliaryRelation` | Determinant vanishing and exact auxiliary relations. |
| §5, `s:balanced` | `Main3BalancedFinalElementary` | Balanced dyadic estimate. |
| §6–7, `s:quadratic-preliminaries`, `s:unbalanced` | `ShiftedSquareReduction`, `Main3LargeAnalyticTargetFibreIdealCount`, `Main3LargeAnalyticElementaryLowerEvidence` | Shifted-square fibres, quadratic ideals and unit orbits, lattice geometry, unbalanced aggregation. |
| §8, `s:uniform-exceptional` | `UniformSquarePartRestoration`, `Main3ElementaryFinalAssembly`, `FinalPaperResults`, `MainResults` | Square-part restoration, saving `1/6400` relative to the intermediate degree, strict cutoff, shared constant. |
| §8, `s:class-number-proof` | `QuadraticSelectedLValueSecondMoment`, `QuadraticOrderConductorClassBound`, `FinalClassAverages`, `MainResults` | Fundamental L-value moment and conductor class-number comparison, then all-order average. |
| §8, `s:odd-class-proof` | `CorollaryOddClassTauCetiGenus`, `WilsonHalfDimensionalSelbergPowerMass`, `WilsonWeightedRectangleProved`, `OddClassMeaning`, `MainResults` | Proved genus divisibility and finite weighted sieve, then the odd class sum. |

The class-average implementation differs from `L:order-second-moment`: the
manuscript extends the L-value second moment to all orders, whereas Lean
transfers the fundamental-discriminant class bound by a conductor class-number
comparison. This is an alternative proved route to the same headline, not a
formalization of that particular all-order L-value lemma.

The squarefree-to-general transfer also uses an alternative route: Lean uses
`θ+1/4` restoration with a budgeted square-part tail, while the manuscript uses
parameter `2θ`. The implementation retains the proved product-hypothesis square
sieve sufficient for the applications, rather than separately formalizing the
manuscript's sharper standalone square-sieve lemma. Intermediate constants
need not match because the headline asserts an unspecified absolute positive
constant. No line-by-line formalization of every intermediate lemma is claimed.

## Foundation, review, and evidence

The foundation is pinned Mathlib with all additional proved Lean source
included. Vendored TauCeti genus theory and adapted third-party files are
compiled from source; see [`THIRD_PARTY.md`](THIRD_PARTY.md). There are no
external arithmetic axioms or numerical certificates in the headline route.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted; `sorryAx`
and `Lean.trustCompiler` are rejected.

The critical semantic review was performed by a separate AI agent from the
one preparing the public aliases. Another agent audited trust and dependencies.
Human review and independent proof-kernel replay remain unclaimed. Exact
commands, hashes, compiler outcomes, external-cache limits, and review evidence
are recorded in `VERIFICATION.md`, `evidence/verification/`, and the
machine-readable status sidecar.
