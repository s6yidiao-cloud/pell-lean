# Paper-to-Lean proof map

The [manuscript PDF](../paper/main.pdf) is included. The TeX source is held
separately and is not distributed; its SHA-256 is
`4290745fdf5234d3f1ccc6ed24cfdc48efde043241939b726713485b700099af`.
The source labels
and line ranges below identify that private snapshot; its headline results are
Theorems 1.1–1.3 and Corollary 1.4.

## Frozen headline statements

All entries have review tier **Critical** because statement fidelity, actual
arithmetic objects, finiteness, and uniform quantifiers determine whether the
formalization proves the requested mathematics. Separate AI semantic and trust
reviews inspected these interfaces. No independent human certification is
claimed. Compiler outcomes and the exact frozen source are recorded separately
in [verification](verification.md) and `checks/records/`.

| Source label and lines | Intended statement | Exact Lean declaration | Status and trust | Scope difference |
| --- | --- | --- | --- | --- |
| `T:field-class-average`, 134–141 | For every real `X ≥ 3`, the actual field class-number sum is at most the proper primitive form-class sum over all positive nonsquare `D ≡ 0,1 mod 4`, `D < X`; the latter is bounded by one constant times `X^(3/2) sqrt(log log X)/(log X)^(3/2)`. | `PellPaper.field_class_average`, `formalization/Pell/MainResults.lean` | Closed proof from `final_field_class_average.2`; accepted axioms only. | None in the displayed result. Finiteness of every form quotient is also proved separately. |
| `T:odd-class-average`, 197–203 | One constant bounds the sum of the numbers of odd-order ordinary ideal classes over the same fields by `X^(3/2) sqrt(log log X)/(log X)^2` for every real `X ≥ 3`. | `PellPaper.odd_class_average`, `formalization/Pell/MainResults.lean` | Closed proof from `final_odd_class_average`; accepted axioms only. | None; the odd-part representation has a proved literal interpretation. |
| `T:uniform-exceptional`, 243–251 | Absolute positive `c,C` and one threshold in `X` give `E_θ(X) ≤ C X^(1-c/θ²)`, uniformly for `3 ≤ θ ≤ c sqrt(log X/log log X)`. | `PellPaper.uniform_exceptional`, `formalization/Pell/MainResults.lean` | Closed proof from `final_uniform_exceptional`; accepted axioms only. | None: strict cutoff, same `c` in range and saving, and threshold before `∀ θ`. |
| `C:pell-unit-growth`, 256–263 | Density-zero failures of `log ε_D ≥ c (log D)^(3/2)/sqrt(log log D)` for an absolute positive `c`, and of `ε_D > D^θ` for each fixed `θ > 0`. | `PellPaper.pell_unit_growth_density`, `PellPaper.fixed_power_density`, `formalization/Pell/MainResults.lean` | Closed proofs from the corresponding `final_*` endpoints; accepted axioms only. | The first failure set uses `≤`, so its complement gives the stronger strict lower bound. Division by `X` gives the same density-one meaning among nonsquares, since squares have density zero. |

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
- `PaperExceptionalDefinitions.lean`: `paperExceptionalSet` restores exactly
  `0 < D < X` from the closed-cutoff implementation API.
  `FinalPaperResults.lean` defines `paperPellGrowthBadSet` with the literal
  `D`-dependent logarithmic expression. The doubled-parameter estimate gives
  the strict exceptional count with the same constant in its range and saving;
  its degree-notation adapter also supplies the class-average estimates.
- `classAverageScale` and `oddClassAverageScale`: the exact real powers and
  logarithms in the manuscript. Constants precede every cutoff; compact-range
  completion extends the bounds to all `X ≥ 3`.

[`checks/PellAudit.lean`](../checks/PellAudit.lean) checks nine literal endpoint types and prints endpoint types,
core definitions, and twenty-seven transitive-axiom lists. The verifier requires
seventeen named endpoints. The semantic review checked
definitions, domains, constants, strict inequalities, density interpretation,
and hidden arithmetic premises. It did not independently re-prove all
compiler-checked algebra.

## Route through the source and proof

| Manuscript stage | Key Lean modules | Relationship |
| --- | --- | --- |
| §2, `s:pell-factorizations` | `Definitions`, `PellFactorization`, `DyadicFactorSeparation` | Mathlib fundamental solutions, Pell factorization, dyadic encoding. |
| §3, `s:square-sieve`, `s:lattice-counting` | `AnisotropicSharpSquareSieve`, `IntrinsicOddHomogeneousPolynomialSquareSieveElementary`, `DyadicResidualFullCellSquareSieveElementary`, `Main3LargeAnalyticRealTwoPlaceLatticeBallGrowth` and their imports | Manuscript square sieve for arbitrary odd homogeneous forms, its sharp and product corollaries, and lattice completion. Both balanced and unbalanced producers use the common parameterized rectangle theorem. |
| §4, `s:determinant-method` | `TwoLayerVanishing`, `IntegralDeterminantVanishing`, `GeneralBidegreeAuxiliaryRelation` | Determinant vanishing and exact auxiliary relations. |
| §5, `s:balanced` | `Main3BalancedFinalElementary` | Balanced dyadic estimate. |
| §6–7, `s:quadratic-preliminaries`, `s:unbalanced` | `ShiftedSquareReduction`, `Main3LargeAnalyticTargetFibreIdealCount`, `Main3LargeAnalyticElementaryLowerEvidence` | Shifted-square fibres, quadratic ideals and unit orbits, lattice geometry, unbalanced aggregation. |
| §8, `s:uniform-exceptional` | `Main3ElementarySquarefreeEstimate`, `UniformDoubledParameterRestoration`, `UniformDoubledParameterEstimate`, `PaperExceptionalDefinitions`, `Main3ElementaryFinalAssembly`, `FinalPaperResults`, `MainResults` | Actual squarefree-kernel split at `√X`, transfer to `2θ`, weighted dyadic summation, and strict cutoff. The strict endpoint uses shared `c = 1/3200`; the degree-notation adapter gives saving `1/6400` for the class averages. |
| §8, `s:class-number-proof` | `QuadraticSelectedLValueSecondMoment`, `QuadraticOrderConductorClassBound`, `FinalClassAverages`, `MainResults` | Fundamental L-value moment and conductor class-number comparison, then all-order average. |
| §8, `s:odd-class-proof` | `CorollaryOddClassTauCetiGenus`, `WilsonHalfDimensionalSelbergPowerMass`, `WilsonWeightedRectangleProved`, `OddClassMeaning`, `MainResults` | Proved genus divisibility and finite weighted sieve, then the odd class sum. |

The class-average implementation differs from `L:order-second-moment`: the
manuscript extends the L-value second moment to all orders, whereas Lean
transfers the fundamental-discriminant class bound by a conductor class-number
comparison. This is an alternative proved route to the same headline, not a
formalization of that particular all-order L-value lemma.

The primary squarefree-to-general proof follows the manuscript's `2θ` route:
it splits at the actual squarefree kernel `√X`, bounds low kernels by
`2X^(3/4)`, and sums weighted high-kernel dyadic blocks uniformly. The strong
inclusive-count theorem `uniform_exceptional_E_doubled_parameter` gives saving
`1/(1600θ²)`. Its strict-cutoff consequence
`uniform_exceptional_doubled_parameter` uses `c = 1/3200` in both the growing
range and saving. `uniformExceptionalEstimate_doubled_parameter` adapts the
same proof to the degree notation used by the class averages. All headline
and `final_*` endpoints use this route, including the class-average and
density corollaries. The obsolete budgeted restoration proof bodies have
been removed; `UniformSquarePartRestoration.lean` contains only a compatibility
import of the new estimate.

`anisotropic_sharp_squareSieve` now proves the sharper standalone
`L:anisotropic-square`: the bound is `K log²(2S₂) S₁ √S₂` with absolute
constants and assumption `√S₂ ≥ C log W`. No product restriction `M ≤ UV`
occurs. The exact value height is `2 + max |f|`, and the form may have
arbitrary odd homogeneous degree and repeated factors. The displayed real
interval interface uses closed endpoints; a more general integer rectangle
interface is also proved. Intermediate existential constants need not match
particular manuscript witnesses.

`anisotropic_product_squareSieve` proves `C:anisotropic-square` under
`C log W ≤ (S₁S₂)^(1/4)`, with bound
`K log²(2S₁S₂) S₁^(5/4) S₂^(1/4)`. Both standalone results and the balanced
and unbalanced main-theorem estimates come from
`eventually_oddHomogeneous_rectangle_squareSieve`. The main producers no
longer require a factorization or bad-prime certificate to invoke this
square-sieve theorem. Their geometric area and perimeter bounds remain
explicit hypotheses of the reduced-coordinate adapter.

## Foundation, review, and evidence

The foundation is pinned Mathlib with all additional proved Lean source
included. Vendored TauCeti genus theory and adapted third-party files are
compiled from source; see [third-party provenance](third-party.md). There are no
external arithmetic axioms or numerical certificates in the headline route.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted; `sorryAx`
and `Lean.trustCompiler` are rejected.

The critical semantic review was performed by a separate AI agent from the
one preparing the public aliases. Another agent audited trust and dependencies.
Human review and independent proof-kernel replay remain unclaimed. Exact
commands, hashes, compiler outcomes, external-cache limits, and review evidence
are recorded in [verification](verification.md), `checks/records/`, and the
[machine-readable status](../checks/formalization.yaml).

The source graph contains 857 local Lean modules and is acyclic.
The [recorded GitHub Actions build](https://github.com/s6yidiao-cloud/pell-lean-archive/actions/runs/39291683619)
passed for commit `52ace63b6294009c1a7633d7466302a1efc3e4be`: all 857 modules,
nine literal types, 27 axiom reports and seventeen mandatory endpoints.
The [receipt](../checks/records/manuscript-primary-ci/summary.json) records the
2233.681-second verifier run. Current Lean source contents match that snapshot;
the repository layout, verifier, and packaging workflow have since changed.
The recorded build applies to its original snapshot. The primary-route
statements and dependencies also passed
[independent AI review](../checks/records/PRIMARY_MANUSCRIPT_REVIEW.md).
All receipts remain unchanged, including their original paths and commands.

## Manuscript intermediate arguments in the primary route

Source of record: private `main_v4.tex`, SHA-256
`4290745fdf5234d3f1ccc6ed24cfdc48efde043241939b726713485b700099af`.
The manuscript is unchanged. Both targets were frozen and independently
ratified before proof generation. Review tier: **Critical**, for uniform
constants in the polynomial/degree and in the growing parameter respectively.

| Source | Exact declarations and semantic closure | Status and trust |
| --- | --- | --- |
| `L:anisotropic-square`, lines 504–589 | `anisotropic_sharp_squareSieve_rectangle`, `anisotropic_sharp_squareSieve_intervals`, `anisotropic_sharp_squareSieve` in `formalization/Pell/AnisotropicSharpSquareSieve.lean`. Arbitrary integral homogeneous forms of odd degree; `1 ≤ S₂ ≤ S₁`; constants precede all form, degree and interval data; square count excludes zero. The final endpoint uses closed real intervals and literal `homogeneousRectangleValueHeight = 2 + sup |f|`. Zero forms are included as a strengthening. | Proved; only `propext`, `Classical.choice`, `Quot.sound`. No factorization, discriminant, coefficient or degree-dependent assumption. |
| `C:anisotropic-square` | `anisotropic_product_squareSieve_rectangle`, `anisotropic_product_squareSieve_intervals`, `anisotropic_product_squareSieve` in `formalization/Pell/AnisotropicSharpSquareSieve.lean`. The same odd homogeneous forms and absolute constants, with product-height hypothesis and bound `K log²(2S₁S₂) S₁^(5/4) S₂^(1/4)`. The literal endpoint uses the exact value height. | Proved from the sharp rectangle lemma by enlarging a side budget while keeping the actual finite window and its value-height bound fixed. |
| Proof of `T:uniform-exceptional`, lines 2451–2492 | `smallFundamentalSolution_doubled_of_sqrt_le`, `doubledParameterLowCover_card_le`, `exceptionalSet_subset_doubledParameter_cover` in `formalization/Pell/UniformDoubledParameterRestoration.lean`; `E_le_doubledParameter_geometric`, `uniform_exceptional_E_doubled_parameter`, `uniformExceptionalEstimate_doubled_parameter`, `uniform_exceptional_doubled_parameter` in `formalization/Pell/UniformDoubledParameterEstimate.lean`. Actual Pell small-solution predicate, unique square-part decomposition, low kernels counted by `2X^(3/4)`, actual high kernels transferred to `2θ`, and weighted geometric summation; final strict count uses literal `θ²` with shared `c = 1/3200`. | Proved; only the three standard axioms above. Ordinary dyadic scales replace the manuscript's shifted real grid; the crossing block has scale at least `√X/2`, and the actual high-kernel cutoff is used before dropping the filter. All public headline proof closures use this route. |

The squarefree bound is applied to the actual count at `2θ` by monotonicity
from the proved estimate at `2θ+1/4`. All squarefree inputs are discharged.
The elementary logarithmic comparison is isolated in
`UniformDoubledParameterScale.lean`; it introduces no counting premise.
`Main3ElementarySquarefreeEstimate.lean` contains the proved squarefree stage,
so the new assembly has no dependency cycle through the final endpoints.
The reciprocal-square-root finite sum used in the low-kernel bound is proved
locally without importing the class-average route.

Independent statement review and file hashes are in
[`MANUSCRIPT_EXTENSIONS_REVIEW.md`](../checks/records/MANUSCRIPT_EXTENSIONS_REVIEW.md).
The original extension review recorded a traversal of 3,862 project constants
with no use of the earlier arbitrary-radicand endpoints. That count and the
original extension-check receipts describe their historical snapshot. The
expanded central audit now also checks the product corollary, the strong
inclusive-count theorem and its degree adapter, and rejects obsolete proof
routes in the headline dependencies. The verification record distinguishes
those historical receipts from the current primary-route checks. No human
certification or separate proof-kernel replay is claimed.
