import Pell.FinalClassAverages
import Pell.FinalPaperResults
import Pell.OddClassMeaning

/-!
# Main results of `paper/main.tex`

These declarations expose the three theorems and both conclusions of the
Pell-unit corollary with explicit source-shaped types. The imported
implementation endpoints provide closed proofs with no supplied arithmetic
or analytic premise. See `FORMALIZATION_MAP.md` for the semantic closure and
the differences between the manuscript's proof and the Lean proof route.
-/

open Filter
open scoped Topology

namespace PellPaper

/-- Finiteness ensures that the proper-form `Nat.card` summands count classes
rather than vanishing on an infinite quotient. -/
theorem proper_form_classes_finite (D : ℕ)
    (hD : PositiveQuadraticOrderDiscriminant D) :
    Finite (IntegralBinaryQuadraticForm.ProperFormClass (D : ℤ)) :=
  final_field_class_average.1 D hD

/-- `main.tex`, Theorem `T:field-class-average`: actual field classes and
all positive nonsquare order discriminants, with strict cutoff and one
constant valid for every real `X ≥ 3`. -/
theorem field_class_average :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
      realQuadraticFieldClassSum X ≤ properOrderFormClassSum X ∧
        properOrderFormClassSum X ≤ C * classAverageScale X :=
  final_field_class_average.2

/-- `main.tex`, Theorem `T:odd-class-average`. `OddClassMeaning` identifies
the summand with the number of odd-order elements of the actual class group. -/
theorem odd_class_average :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
      realQuadraticFieldOddClassSum X ≤ C * oddClassAverageScale X :=
  final_odd_class_average

/-- `main.tex`, Theorem `T:uniform-exceptional`: the same positive `c`
controls the range and saving; the implied constant and threshold precede
the quantifier over `θ`. -/
theorem uniform_exceptional :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ X : ℝ in atTop, ∀ θ : ℝ,
        3 ≤ θ →
        θ ≤ c * Real.sqrt (Real.log X / Real.log (Real.log X)) →
        (paperExceptionalCount θ X : ℝ) ≤ C * X ^ (1 - c / θ ^ 2) :=
  final_uniform_exceptional

/-- `main.tex`, Corollary `C:pell-unit-growth`: density-zero failures of
the displayed `D`-dependent logarithmic lower bound. -/
theorem pell_unit_growth_density :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun X : ℝ => ((paperPellGrowthBadSet c X).card : ℝ) / X)
        atTop (𝓝 0) :=
  final_pell_unit_growth_density

/-- The fixed-power conclusion in Corollary `C:pell-unit-growth`. -/
theorem fixed_power_density (θ : ℝ) (hθ : 0 < θ) :
    Tendsto (fun X : ℝ => (paperExceptionalCount θ X : ℝ) / X)
      atTop (𝓝 0) :=
  final_fixed_power_density θ hθ

end PellPaper
