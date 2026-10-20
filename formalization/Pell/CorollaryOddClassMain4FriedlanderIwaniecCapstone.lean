import Pell.CorollaryOddClassMain4FriedlanderIwaniecProved
import Pell.CorollaryOddClassMain4WilsonSummedScales

/-!
# Main4 capstone after discharging the FI rectangle input

The Friedlander--Iwaniec rectangle estimate is now proved inside the project,
so the expanded Main4 route needs only Wilson's published weighted rectangle
estimate as an external analytic premise.
-/

namespace PellPaper

noncomputable section

theorem main4WilsonFinitePolynomialMomentAwayFromEight_of_wilsonRectangle
    (hWilson : Main4WilsonWeightedRectangleEstimate) :
    Main4WilsonFinitePolynomialMomentAwayFromEight :=
  main4WilsonFinitePolynomialMomentAwayFromEight_of_rectangleEstimates
    hWilson main4FriedlanderIwaniecRectangleEstimate_proved

/-- The exact Corollary 1.2 assertion from Wilson's weighted rectangle theorem;
the Friedlander--Iwaniec half of the Main4 argument has no remaining premise. -/
theorem realQuadraticFieldOddClassAverageAssertion_of_wilsonRectangle
    (hWilson : Main4WilsonWeightedRectangleEstimate) :
    RealQuadraticFieldOddClassAverageAssertion :=
  realQuadraticFieldOddClassAverageAssertion_of_rectangleEstimates
    hWilson main4FriedlanderIwaniecRectangleEstimate_proved

end

end PellPaper
