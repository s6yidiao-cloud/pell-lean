import Pell.GenuineQuadraticSelectedLValuePointwise
import Pell.MaximalOrderFundamentalUnitRegulatorLower
import Pell.ClassEventualCompletion

/-!
# The actual discriminant-indexed class average from two analytic inputs

The genuine field/form model, its pointwise class-number formula bound,
the positive normalized regulator, the Pell cutoff transfer, the first
moment, the canonical moving cutoff, and the finite initial range are
discharged by proved arithmetic and finite/analytic reductions.

The conclusion remains conditional on two substantive unproved inputs:
the uniform Pell exceptional-set estimate and an eventual linear second
moment for the actual selected L-values. This is not a proof of either
headline theorem, nor a classification of all real quadratic fields.
-/

namespace PellPaper

open Filter

noncomputable section

/-- Only the uniform exceptional estimate and actual selected-L second
moment remain as inputs to the genuine discriminant-indexed average route.
The factor four in the pointwise bound costs exactly sixteen in the moment. -/
theorem genuineFieldClassAverageAssertion_of_uniformExceptional_selectedSecondMoment
    (Cmoment cSave : ℝ) (hCmoment : 0 ≤ Cmoment)
    (hUniform : UniformExceptionalEstimate cSave)
    (hsecond : ∀ᶠ X : ℝ in atTop,
      (∑ D ∈ fundamentalDiscriminantsBelow X, (selectedKroneckerLValue D) ^ 2) ≤
        Cmoment * X) :
    FieldClassAverageAssertion genuineQuadraticAlgebraClassNumberModel := by
  apply fieldClassAverageAssertion_of_uniformExceptional_canonicalCutoff
    genuineQuadraticAlgebraClassNumberModel (fun D => 4 * selectedKroneckerLValue D)
    maximalOrderFundamentalUnitRegulator (16 * Cmoment) (1 / 12 : ℝ) cSave
    (by positivity) (by norm_num)
  · intro D _hD
    exact mul_nonneg (by norm_num) (selectedKroneckerLValue_nonneg D)
  · intro D hD
    exact (one_div_twelve_lt_maximalOrderFundamentalUnitRegulator hD).le
  · intro X t D hDX hreg
    exact smallFundamentalSolution_regulatorPellExponent_of_maximalOrderFundamentalUnitRegulator_lt
      (mem_fundamentalDiscriminantsBelow.mp hDX).1 t hreg
  · exact hUniform
  · exact genuineQuadraticAlgebraClassNumberModel_pointwise_selectedLValue_normalizedRegulator
  · filter_upwards [hsecond] with X hX
    calc
      (∑ D ∈ fundamentalDiscriminantsBelow X, (4 * selectedKroneckerLValue D) ^ 2) =
          16 * ∑ D ∈ fundamentalDiscriminantsBelow X, (selectedKroneckerLValue D) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro D _hD
        ring
      _ ≤ 16 * (Cmoment * X) := mul_le_mul_of_nonneg_left hX (by norm_num)
      _ = (16 * Cmoment) * X := by ring

end
end PellPaper
