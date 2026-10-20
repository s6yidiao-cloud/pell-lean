import Pell.RealQuadraticFieldClassSum
import Pell.GenuineQuadraticClassAverageConditional

/-!
# The class-average target for actual field isomorphism classes

Both sums are literal: the left sums actual ideal class numbers over actual
real quadratic field classes with discriminant below X, and the middle sums
cardinalities of proper primitive indefinite form classes. The exact
equivalence with the genuine model is proved, not assumed.

The analytic conclusion remains conditional on the selected-character
second moment and the uniform Pell exceptional estimate.
-/

namespace PellPaper

open Filter

noncomputable section

/-- The field/form average assertion with actual, rather than model-supplied,
class numbers and field classes. The cutoff is strict and the constant is
uniform over all real X at least three. -/
def RealQuadraticFieldClassAverageAssertion : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
    realQuadraticFieldClassSum X ≤
      (∑ D ∈ fundamentalDiscriminantsBelow X,
        (Nat.card (IntegralBinaryQuadraticForm.ProperFormClass (D : ℤ)) : ℝ)) ∧
    (∑ D ∈ fundamentalDiscriminantsBelow X,
      (Nat.card (IntegralBinaryQuadraticForm.ProperFormClass (D : ℤ)) : ℝ)) ≤
        C * classAverageScale X

/-- The genuine model's assertion is exactly the literal field/form target. -/
theorem realQuadraticFieldClassAverageAssertion_iff_genuine :
    RealQuadraticFieldClassAverageAssertion ↔
      FieldClassAverageAssertion genuineQuadraticAlgebraClassNumberModel := by
  unfold RealQuadraticFieldClassAverageAssertion FieldClassAverageAssertion
  simp only [realQuadraticFieldClassSum_eq_genuine_ordinaryClassSum,
    ← genuineQuadraticAlgebraClassNumberModel_formClassSum_eq]

/-- A conditional endpoint for the literal field-class average. Both
analytic premises remain unproved; no arithmetic or family realization
premise is supplied here. -/
theorem realQuadraticFieldClassAverageAssertion_of_uniformExceptional_selectedSecondMoment
    (Cmoment cSave : ℝ) (hCmoment : 0 ≤ Cmoment)
    (hUniform : UniformExceptionalEstimate cSave)
    (hsecond : ∀ᶠ X : ℝ in atTop,
      (∑ D ∈ fundamentalDiscriminantsBelow X, (selectedKroneckerLValue D) ^ 2) ≤
        Cmoment * X) :
    RealQuadraticFieldClassAverageAssertion :=
  realQuadraticFieldClassAverageAssertion_iff_genuine.mpr
    (genuineFieldClassAverageAssertion_of_uniformExceptional_selectedSecondMoment
      Cmoment cSave hCmoment hUniform hsecond)

end
end PellPaper

