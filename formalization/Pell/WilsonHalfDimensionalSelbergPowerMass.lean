import Pell.WilsonHalfDimensionalSelbergMass
import Pell.WilsonSelbergPowerCutoff
import Pell.WilsonNeutralizerWeightedMass
import Pell.WilsonSelbergMomentFiniteAssembly

/-!
# Wilson's half-dimensional Selberg mass at the fixed power cutoff

This module specializes the finite half-dimensional sieve to
`R = floor(M^(1/100))`.  It supplies the two numerical inputs used by the
last scale calculation: total neutralizer mass at most
`79 M / sqrt(log M)` and absolute coefficient mass at most `64 M^(3/50)`.
-/

namespace PellPaper

noncomputable section

/-- The concrete half-dimensional sieve chosen at denominator scale `M`. -/
def main4WilsonPowerSelbergSieve (M : ℕ) : SelbergSieve :=
  main4WilsonHalfSelbergSieve (main4WilsonSelbergPowerCutoff M)

/-- Its total neutralizer mass has the required half-dimensional logarithmic
saving, with a deliberately loose explicit constant. -/
theorem main4WilsonPowerSelbergTotalMass_le
    {M : ℕ} (hM : 2 ≤ M) :
    main4WilsonNeutralizerTotalMass
        (primorial (main4WilsonSelbergPowerCutoff M + 1)) M
        (main4SelbergMuPlus (main4WilsonPowerSelbergSieve M)) ≤
      79 * ((M : ℝ) / Real.sqrt (Real.log (M : ℝ))) := by
  let R := main4WilsonSelbergPowerCutoff M
  apply main4WilsonSelbergPowerCutoff_total_le hM
  · simpa [R] using
      sqrt_half_log_add_two_le_main4SelbergBoundingSum_half R
  · simpa [R, main4WilsonPowerSelbergSieve, div_eq_mul_inv] using
      main4WilsonNeutralizerTotalMass_halfSelberg_le_inv_add_cube R M

/-- The absolute mass of the Selberg upper coefficients remains a tiny
power of `M`. -/
theorem main4WilsonPowerSelbergCoefficientMass_le
    {M : ℕ} (hM : 2 ≤ M) :
    main4WilsonNeutralizerCoefficientMass
        (primorial (main4WilsonSelbergPowerCutoff M + 1))
        (main4SelbergMuPlus (main4WilsonPowerSelbergSieve M)) ≤
      64 * (M : ℝ) ^ (3 / 50 : ℝ) := by
  let R := main4WilsonSelbergPowerCutoff M
  let s := main4WilsonHalfSelbergSieve R
  calc
    main4WilsonNeutralizerCoefficientMass
        (primorial (R + 1)) (main4SelbergMuPlus s) ≤
        ((((R + 1) ^ 2 : ℕ) : ℝ) ^ 3) := by
      apply main4WilsonNeutralizerCoefficientMass_selberg_le_cube
        s ((R + 1) ^ 2)
      exact main4WilsonHalfSelbergSieve_level R
    _ ≤ 64 * (M : ℝ) ^ (3 / 50 : ℝ) := by
      simpa [R] using
        main4WilsonSelbergPowerCutoff_level_cube_le (M := M) (by omega)

/-- The original first Cauchy factor is bounded by the same power-Selberg
total mass. -/
theorem wilsonWeightedMass_reciprocalDivisor_le_powerSelbergTotalMass
    (b : ℕ → ℝ) {M : ℕ} (hb : ∀ m : ℕ, |b m| ≤ 1) :
    wilsonWeightedMass b main4WilsonReciprocalDivisorWeight M ≤
      main4WilsonNeutralizerTotalMass
        (primorial (main4WilsonSelbergPowerCutoff M + 1)) M
        (main4SelbergMuPlus (main4WilsonPowerSelbergSieve M)) := by
  let R := main4WilsonSelbergPowerCutoff M
  let s := main4WilsonHalfSelbergSieve R
  exact wilsonWeightedMass_reciprocalDivisor_le_neutralizerTotalMass
    b (primorial (R + 1)) M (main4SelbergMuPlus s)
      (squarefree_primorial (R + 1))
      (main4SelbergMuPlus_isUpperMoebius s) hb

/-- Fully specialized finite moment inequality before the final elementary
scale comparison. -/
theorem abs_main4OrdinaryJacobiRectangle_reciprocalDivisor_sq_le_powerSelberg
    (a b : ℕ → ℝ) {M N : ℕ} (hM : 2 ≤ M)
    (ha : main4OddSupportedUnitBound a)
    (hb : main4OddSupportedUnitBound b) :
    |main4OrdinaryJacobiRectangle a
        (fun m ↦ b m * main4WilsonReciprocalDivisorWeight m) M N| ^ 2 ≤
      let B :=
        main4WilsonNeutralizerTotalMass
          (primorial (main4WilsonSelbergPowerCutoff M + 1)) M
          (main4SelbergMuPlus (main4WilsonPowerSelbergSieve M))
      B *
        (B * ((N : ℝ) * (1 + Real.log (N : ℝ))) +
          (N : ℝ) ^ 2 *
            (main4WilsonNeutralizerCoefficientMass
                (primorial (main4WilsonSelbergPowerCutoff M + 1))
                (main4SelbergMuPlus (main4WilsonPowerSelbergSieve M)) *
              (4 * (N : ℝ) *
                (1 + Real.log ((2 * (N : ℝ)) ^ 2))))) := by
  let R := main4WilsonSelbergPowerCutoff M
  let s := main4WilsonHalfSelbergSieve R
  let B := main4WilsonNeutralizerTotalMass
    (primorial (R + 1)) M (main4SelbergMuPlus s)
  have hR : 1 ≤ R := one_le_main4WilsonSelbergPowerCutoff (by omega)
  exact
    abs_main4OrdinaryJacobiRectangle_reciprocalDivisor_sq_le_of_primorialNeutralizer
      a b (R + 1) M N (main4SelbergMuPlus s) B B
        (by omega) (main4SelbergMuPlus_isUpperMoebius s) ha hb
        (wilsonWeightedMass_reciprocalDivisor_le_powerSelbergTotalMass
          b hb.2) le_rfl

end

end PellPaper
