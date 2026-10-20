import Pell.Main3ElementarySquarefreeEstimate
import Pell.UniformDoubledParameterEstimate
import Pell.RealQuadraticOrderClassAverageUniformExceptional

/-!
# Main theorem assembly

The squarefree dyadic estimate is passed to the manuscript's doubled-parameter
restoration. The resulting exceptional-set estimate supplies the
class-number average and the odd-class arguments.
-/

namespace PellPaper

/-- Compatibility with the degree-parameter interface used by the
class-number and odd-class estimates. Its proof uses the doubled-parameter
squarefree-kernel split. -/
theorem uniformExceptionalEstimate_one_div_6400_elementary_proved :
    UniformExceptionalEstimate ((1 : ℝ) / 6400) :=
  uniformExceptionalEstimate_doubled_parameter

/-- The all-order class-average assertion follows from the doubled-parameter
exceptional-set bound and the proved conductor comparison. -/
theorem realQuadraticOrderClassAverageAssertion :
    RealQuadraticOrderClassAverageAssertion :=
  realQuadraticOrderClassAverageAssertion_of_uniformExceptional
    ((1 : ℝ) / 6400) uniformExceptionalEstimate_doubled_parameter

end PellPaper
