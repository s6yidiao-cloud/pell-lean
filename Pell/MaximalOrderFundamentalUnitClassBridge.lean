import Pell.MaximalOrderFundamentalUnitRegulator
import Pell.PellOrderRegulatorUniformPipeline

/-!
# Pointwise class-side transport from the selected maximal-order regulator

The actual class-number formula in the manuscript naturally has the
maximal-order regulator in its denominator.  The preceding unit comparison
gives `pellOrderRegulator ≤ 6 * maximalOrderFundamentalUnitRegulator`.
This file records the resulting elementary denominator transport: a
nonnegative numerator divided by the selected maximal-order regulator is at
most six times the same numerator divided by the Pell-order regulator.

It does not supply the class-number formula or any `L`-value bound; a
pointwise class-number inequality remains an explicit input.
-/

namespace PellPaper

noncomputable section

/-- The selected maximal-order regulator is positive on its intended
positive-fundamental-discriminant family. -/
theorem maximalOrderFundamentalUnitRegulator_pos
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D) :
    0 < maximalOrderFundamentalUnitRegulator D := by
  rw [maximalOrderFundamentalUnitRegulator_eq_log_of_positiveFundamentalDiscriminant hD]
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  exact div_pos
    (Real.log_pos (concreteFundamentalUnitRealModel D hD).eta_one_lt)
    (Real.log_pos (by exact_mod_cast hD.1))

/-- The factor-six regulator comparison transports a nonnegative numerator
from the selected maximal-order denominator to the Pell-order denominator. -/
theorem div_maximalOrderFundamentalUnitRegulator_le_six_mul_div_pellOrderRegulator
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D) {L : ℝ} (hL : 0 ≤ L) :
    L / maximalOrderFundamentalUnitRegulator D ≤ 6 * L / pellOrderRegulator D := by
  have hp : 0 < pellOrderRegulator D := by
    linarith [one_half_lt_pellOrderRegulator hD]
  have hcomp := pellOrderRegulator_le_six_mul_maximalOrderFundamentalUnitRegulator hD
  have hscale : pellOrderRegulator D / 6 ≤ maximalOrderFundamentalUnitRegulator D := by
    nlinarith
  calc
    L / maximalOrderFundamentalUnitRegulator D ≤ L / (pellOrderRegulator D / 6) :=
      div_le_div_of_nonneg_left hL (div_pos hp (by norm_num)) hscale
    _ = 6 * L / pellOrderRegulator D := by
      field_simp

/-- A supplied pointwise class-number estimate with the selected
maximal-order regulator implies the corresponding factor-six estimate with
the concrete Pell-order regulator. -/
theorem formClassNumber_bound_of_maximalOrderFundamentalUnitRegulator_bound
    (M : ClassNumberModel) (L : ℕ → ℝ) (q : ℝ) {D : ℕ}
    (hD : PositiveFundamentalDiscriminant D) (hq : 0 ≤ q)
    (hL : 0 ≤ L D)
    (hbound : (M.formClassNumber D : ℝ) ≤
      q * (L D / maximalOrderFundamentalUnitRegulator D)) :
    (M.formClassNumber D : ℝ) ≤
      q * (6 * L D / pellOrderRegulator D) := by
  exact hbound.trans
    (mul_le_mul_of_nonneg_left
      (div_maximalOrderFundamentalUnitRegulator_le_six_mul_div_pellOrderRegulator hD hL)
      hq)

end

end PellPaper
