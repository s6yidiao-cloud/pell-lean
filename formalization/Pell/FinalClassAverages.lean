import Pell.Main3ElementaryFinalAssembly
import Pell.WilsonWeightedRectangleProved

/-!
# Class-number averages in `paper/main.tex`

These short endpoints expose the two class-average targets of the final paper.
The first sums proper forms over all positive nonsquare order discriminants;
the second is the actual real-quadratic-field odd-part average. Their proof
developments are in the imported modules.
-/

namespace PellPaper

/-- `paper/main.tex`, Theorem `T:field-class-average`, with the field sum and all
positive nonsquare order discriminants under a strict real cutoff. -/
theorem final_field_class_average :
    RealQuadraticOrderClassAverageAssertion :=
  realQuadraticOrderClassAverageAssertion

/-- The fundamental-discriminant subfamily consequence. -/
theorem final_field_class_average_fundamental :
    RealQuadraticFieldClassAverageAssertion :=
  RealQuadraticOrderClassAverageAssertion.to_fundamental
    final_field_class_average

/-- `paper/main.tex`, Theorem `T:odd-class-average`, for actual real quadratic fields
and the odd part of their ordinary ideal class numbers. -/
theorem final_odd_class_average :
    RealQuadraticFieldOddClassAverageAssertion :=
  realQuadraticFieldOddClassAverageAssertion_proved

end PellPaper
