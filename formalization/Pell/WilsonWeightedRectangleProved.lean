import Pell.WilsonHalfDimensionalSelbergPowerMass
import Pell.WilsonSelbergMomentScaleAlgebra
import Pell.CorollaryOddClassMain4FriedlanderIwaniecCapstone

/-!
# Unconditional odd class-average proof via Wilson's weighted rectangle estimate

The finite half-dimensional Selberg neutralizer, the square/nonsquare moment
assembly, and the final scale algebra together prove the exact weighted
rectangle estimate used in the manuscript.  The existing deterministic class-average
pipeline then yields `T:odd-class-average` of `paper/main.tex` with no remaining external analytic
premise.
-/

namespace PellPaper

noncomputable section

/-- Wilson's reciprocal-divisor weighted rectangle estimate at the explicit
constant `400`. -/
theorem main4WilsonWeightedRectangleEstimateWith_fourHundred :
    Main4WilsonWeightedRectangleEstimateWith 400 := by
  intro M N hM hN a b ha hb
  let P := primorial (main4WilsonSelbergPowerCutoff M + 1)
  let muPlus := main4SelbergMuPlus (main4WilsonPowerSelbergSieve M)
  let B := main4WilsonNeutralizerTotalMass P M muPlus
  let E := main4WilsonNeutralizerCoefficientMass P muPlus
  have hR : 1 ≤ main4WilsonSelbergPowerCutoff M :=
    one_le_main4WilsonSelbergPowerCutoff (by omega)
  have hUpper : BoundingSieve.IsUpperMoebius muPlus := by
    exact main4SelbergMuPlus_isUpperMoebius
      (main4WilsonPowerSelbergSieve M)
  have hB0 : 0 ≤ B := by
    exact main4WilsonNeutralizerTotalMass_nonneg P M
      (by
        dsimp [P]
        exact squarefree_primorial _)
      muPlus hUpper
  have hE0 : 0 ≤ E :=
    main4WilsonNeutralizerCoefficientMass_nonneg P muPlus
  have hmassScale0 :
      0 ≤ (M : ℝ) / Real.sqrt (Real.log (M : ℝ)) :=
    div_nonneg (Nat.cast_nonneg M) (Real.sqrt_nonneg _)
  have hB79 :
      B ≤ 79 * ((M : ℝ) / Real.sqrt (Real.log (M : ℝ))) := by
    simpa [B, P, muPlus] using
      main4WilsonPowerSelbergTotalMass_le hM
  have hB80 :
      B ≤ 80 * ((M : ℝ) / Real.sqrt (Real.log (M : ℝ))) := by
    exact hB79.trans
      (mul_le_mul_of_nonneg_right (by norm_num) hmassScale0)
  have hE64 : E ≤ 64 * (M : ℝ) ^ (3 / 50 : ℝ) := by
    simpa [E, P, muPlus] using
      main4WilsonPowerSelbergCoefficientMass_le hM
  apply
    abs_le_four_hundred_mul_main4WilsonWeightedRectangleScale_of_moment_bounds
      hM hN hB0 hB0 hE0 hB80 hB80 hE64
  simpa [B, E, P, muPlus] using
    abs_main4OrdinaryJacobiRectangle_reciprocalDivisor_sq_le_powerSelberg
      a b hM ha hb

/-- The exact existential source-shaped Wilson estimate is now inhabited. -/
theorem main4WilsonWeightedRectangleEstimate_proved :
    Main4WilsonWeightedRectangleEstimate := by
  exact ⟨400, by norm_num,
    main4WilsonWeightedRectangleEstimateWith_fourHundred⟩

/-- `T:odd-class-average` in its genuine real-quadratic-field formulation. -/
theorem realQuadraticFieldOddClassAverageAssertion_proved :
    RealQuadraticFieldOddClassAverageAssertion := by
  exact realQuadraticFieldOddClassAverageAssertion_of_wilsonRectangle
    main4WilsonWeightedRectangleEstimate_proved

end

end PellPaper
