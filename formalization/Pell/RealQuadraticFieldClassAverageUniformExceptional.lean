import Pell.QuadraticSelectedLValueSecondMoment
import Pell.RealQuadraticFieldClassAverageConditional

/-!
# The literal field-class average from the uniform exceptional estimate

The selected-character second moment is now supplied by a proved theorem.
The only remaining premise here is the actual `UniformExceptionalEstimate`;
this file does not prove that premise or an unconditional field-class average.
-/

namespace PellPaper

/-- The actual field/form class-average assertion follows from the uniform
Pell exceptional estimate alone. The selected L-value moment is proved. -/
theorem realQuadraticFieldClassAverageAssertion_of_uniformExceptional
    (cSave : ℝ) (hUniform : UniformExceptionalEstimate cSave) :
    RealQuadraticFieldClassAverageAssertion :=
  realQuadraticFieldClassAverageAssertion_of_uniformExceptional_selectedSecondMoment
    520 cSave (by norm_num) hUniform eventually_sum_selectedKroneckerLValue_sq_le

end PellPaper
