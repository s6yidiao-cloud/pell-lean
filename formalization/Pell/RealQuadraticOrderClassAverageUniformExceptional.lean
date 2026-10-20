import Pell.QuadraticOrderConductorClassBound
import Pell.RealQuadraticOrderClassAverageConductor

/-!
# All-order class averages from the uniform exceptional estimate

The conductor class-number comparison is now supplied by a proved theorem.
Only the uniform exceptional estimate remains an explicit analytic premise.
-/

namespace PellPaper

/-- The literal fundamental-family average implies the all-order average;
the complete conductor comparison is proved internally. -/
theorem realQuadraticOrderClassAverageAssertion_of_fundamental
    (hfundamental : RealQuadraticFieldClassAverageAssertion) :
    RealQuadraticOrderClassAverageAssertion := by
  apply realQuadraticOrderClassAverageAssertion_of_conductorBound 2 (by norm_num)
  · intro D₀ f hD₀ hf
    exact IntegralBinaryQuadraticForm.properFormClass_card_mul_sq_le_two_mul_divisorSum_real
      D₀ f hD₀ hf
  · exact hfundamental

/-- The expanded headline follows from the uniform Pell exceptional estimate
alone. This theorem does not prove that remaining estimate. -/
theorem realQuadraticOrderClassAverageAssertion_of_uniformExceptional
    (cSave : ℝ) (hUniform : UniformExceptionalEstimate cSave) :
    RealQuadraticOrderClassAverageAssertion :=
  realQuadraticOrderClassAverageAssertion_of_fundamental
    (realQuadraticFieldClassAverageAssertion_of_uniformExceptional cSave hUniform)

end PellPaper
