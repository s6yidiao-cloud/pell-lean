# Semantic review of the main results

Review tier: **critical**. Reviewer: separate `publication_review` AI agent,
independent of the author of `Pell/MainResults.lean`. This is a statement and
selected-dependency review, not independent human certification or an
independently implemented proof-kernel replay.

## Frozen source and public declarations

The source reviewed is `paper/main.tex`, SHA-256
`4290745fdf5234d3f1ccc6ed24cfdc48efde043241939b726713485b700099af`.
The public entry point is `Pell/MainResults.lean`, SHA-256
`0885aafb2fc3d925e030b33ff04522b8e57000628174800e23fc6995d1845483`. The central `PellAudit.lean` has SHA-256
`f5118cb7ecb0628cc0187b4db1bd756596fa898c18e4972d155e2a98bf5fdc9f`.

| Source result | Declaration | Semantic outcome |
| --- | --- | --- |
| `T:field-class-average` | `PellPaper.field_class_average` | Approved: actual fields, all positive nonsquare order discriminants, strict cutoff, exact logarithmic scale, one constant for every real `X ≥ 3`. |
| Form-class finiteness supporting that theorem | `PellPaper.proper_form_classes_finite` | Approved: every positive nonsquare order discriminant gives a finite actual proper-form quotient. |
| `T:odd-class-average` | `PellPaper.odd_class_average` | Approved: actual ordinary ideal classes of odd order and the exact displayed scale. |
| `T:uniform-exceptional` | `PellPaper.uniform_exceptional` | Approved: same positive saving/range constant; positive implied constant and one threshold before every admissible real exponent. |
| `C:pell-unit-growth`, logarithmic conclusion | `PellPaper.pell_unit_growth_density` | Approved: genuinely discriminant-dependent growth failure set has count divided by `X` tending to zero. |
| `C:pell-unit-growth`, fixed-power conclusion | `PellPaper.fixed_power_density` | Approved: every fixed positive real exponent has density-zero exceptions. |

All six public declaration types are explicit. None takes an arithmetic bound,
analytic estimate, conjecture, certificate or classification assertion as an
argument. The finiteness endpoint takes only its intended discriminant and
membership condition; the fixed-power endpoint takes only its exponent and
positivity condition.

## Semantic closure checked

- `PositiveQuadraticOrderDiscriminant D` means `0 < D`, nonsquareness, and
  congruence to zero or one modulo four. `orderDiscriminantsBelow` uses a
  proved strict real cutoff. Primitive integral forms are actual integer
  triples with discriminant `b²-4ac`, modulo determinant-one integer
  substitutions. The separate finiteness theorem prevents `Nat.card` on an
  infinite quotient from silently vanishing.
- Real quadratic fields have rational degree two and a real embedding, up to
  rational algebra equivalence without a marked embedding. Their discriminants
  and class numbers are Mathlib's actual `NumberField.discr` and
  `NumberField.classNumber`. The fundamental-discriminant classification and
  sum transport are proved internally, so the public sum does not count a
  surrogate invariant or a restricted subfamily.
- The odd-class sum uses `ordCompl[2]` of the actual ordinary class number.
  `realQuadraticFieldOddClassNumber_eq_card_oddOrderClasses` proves that this
  is `Nat.card {c : ClassGroup (𝓞 F) // Odd (orderOf c)}`. Finiteness of actual
  number-field class groups supplies the intended finite-group meaning.
- `classAverageScale` is exactly
  `X^(3/2) sqrt(log(log X))/(log X)^(3/2)`; `oddClassAverageScale` has
  denominator `(log X)^2`. The same positive constant works for every real
  `X ≥ 3`, including the compact initial range.
- `epsilon a` is the actual `x + y sqrt D` of Mathlib's positive fundamental
  Pell solution. Existence and uniqueness are related internally to positive
  nonsquare radicands. `mem_paperExceptionalSet` gives precisely `0 < D`,
  `D < X` and smallness of that fundamental solution.
- In `uniform_exceptional`, positive `c,C` precede `∀ᶠ X`, which precedes
  `∀ θ`. The same `c` occurs in the saving `c/θ²` and the growing range
  `θ ≤ c sqrt(log X/log log X)`. There is no exponent-dependent threshold or
  implied constant hidden behind those quantifiers.
- `paperPellGrowthBadSet` uses strict `D < X` and the literal expression
  `(log D)^(3/2)/sqrt(log(log D))`. Its failure inequality is `≤`, so its
  complement gives the sufficient strict lower bound. Dividing exception
  counts by `X` expresses density zero; the usual density-one interpretation
  among nonsquares also uses that squares have density zero. That elementary
  normalization bridge is not separately named among the six public endpoints.

## Selected critical input discharges

The all-order class-average endpoint uses the closed
`realQuadraticOrderClassAverageAssertion`. Its conditional large-block assembly
is supplied `main3LargeAnalyticBlockSumEstimateElementaryInput_proved`, which
unfolds the interface and uses the internally proved elementary pointwise
large-block estimate. Positivity and the placement of uniform thresholds and
constants remain part of those interface types. The final caller does not
leave that input as an argument or replace it with a named assumption.

The odd-class endpoint uses the closed
`realQuadraticFieldOddClassAverageAssertion_proved`. Its Wilson rectangle
interface is supplied by `main4WilsonWeightedRectangleEstimate_proved`, built
from finite Selberg weights, moment bounds and scale algebra. The required
Friedlander–Iwaniec rectangle estimate is also supplied by its proved endpoint.
These implementation identifiers are internal APIs; the public declarations
above have neutral mathematical names.

`FinalPaperResults` derives the exceptional-set and growth statements from the
proved elementary assembly and restores the literal strict cutoff. The final
route does not require an unproved Weil bound or an external numerical
certificate. Earlier conditional APIs can remain useful theorem schemas; their
existence does not make the closed public endpoints conditional.

## Disclosed proof-route scope

The headline conclusions are approved. This is not a claim that every source
lemma or proof sentence has been translated directly.

- Lean proves the all-order average through a conductor class-number
  comparison; the manuscript extends the L-value moment to all orders.
- Lean uses squarefree estimates at parameter `θ+1/4` together with a budgeted
  square-part tail. The manuscript uses parameter `2θ` and a different split.
  Both routes yield the same headline bound with an unspecified positive
  absolute constant.
- The elementary product-hypothesis square-sieve estimate suffices for the
  headline route. The sharper standalone square-sieve lemma in the manuscript
  is not separately claimed as a formalized result.

## Audit and validation boundary

`PellAudit.lean` prints the six public and six implementation/meaning endpoints,
core definitions and transitive axiom lists. Its six literal type challenges
expand both class-average scales and the strict exceptional cutoff. They would
fail elaboration if a public endpoint acquired an additional premise or the
checked normalization changed. The source/import scan covers all 851 local
Lean modules and passed during this review.

The parent integration run is responsible for the fresh strict compiler build,
source integrity gates and the complete transitive axiom audit, with only
`propext`, `Classical.choice` and `Quot.sound` allowed. This semantic review does
not substitute for those compiler receipts. Pinned external Mathlib/dependency
proof caches remain the documented external artifact trust boundary.

No hidden mathematical premise, weakened headline, changed arithmetic family,
wrong cutoff, vacuous count or nonuniform quantifier was found in the inspected
semantic closure and selected critical discharges.
