import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Cubic dominance in the sheared determinant exponent

After the determinant estimate in `L:sheared`, the manuscript chooses the
fixed degree `B` large enough that the negative `B^3 log Y` term dominates
the `O(B^2 log Y)` error.  This file formalizes that elementary numerical
step for an explicitly supplied nonnegative quadratic-error coefficient.

It does not provide the determinant estimate or its error coefficient.
-/

namespace PellPaper

/-- A positive cubic coefficient eventually dominates a nonnegative quadratic
coefficient on natural degrees. -/
theorem exists_natural_cubic_dominates_quadratic
    {c C : ℝ} (hc : 0 < c) (_hC : 0 ≤ C) :
    ∃ B0 : ℕ, ∀ B : ℕ, B0 ≤ B →
      C * (B : ℝ) ^ 2 ≤ (c / 2) * (B : ℝ) ^ 3 := by
  obtain ⟨B0, hB0⟩ := exists_nat_gt (2 * C / c)
  refine ⟨B0, ?_⟩
  intro B hB
  have hB0B : (B0 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hBlinear : 2 * C / c < (B : ℝ) := hB0.trans_le hB0B
  have hlinear : C ≤ (c / 2) * (B : ℝ) := by
    have h := (div_lt_iff₀ hc).mp hBlinear
    nlinarith
  have hsq : 0 ≤ (B : ℝ) ^ 2 := sq_nonneg _
  calc
    C * (B : ℝ) ^ 2 ≤ ((c / 2) * (B : ℝ)) * (B : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hlinear hsq
    _ = (c / 2) * (B : ℝ) ^ 3 := by ring

/-- Once the cubic term has absorbed the quadratic error, the resulting
logarithmic determinant exponent is strictly negative for positive degree
and `Y > 1`. -/
theorem sheared_cubic_quadratic_log_exponent_neg
    {c C B Y : ℝ} (hc : 0 < c) (_hC : 0 ≤ C) (hB : 0 < B) (hY : 1 < Y)
    (hdominates : C * B ^ 2 ≤ (c / 2) * B ^ 3) :
    -c * B ^ 3 * Real.log Y + C * B ^ 2 * Real.log Y < 0 := by
  have hlog : 0 < Real.log Y := Real.log_pos hY
  have hmul := mul_le_mul_of_nonneg_right hdominates hlog.le
  have hcubic : 0 < (c / 2) * B ^ 3 * Real.log Y := by positivity
  nlinarith

/-- The corresponding exponential upper bound is strictly below one.  This
is the real-valued form used before the integral determinant is forced to
vanish. -/
theorem exp_sheared_cubic_quadratic_log_exponent_lt_one
    {c C B Y : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hB : 0 < B) (hY : 1 < Y)
    (hdominates : C * B ^ 2 ≤ (c / 2) * B ^ 3) :
    Real.exp (-c * B ^ 3 * Real.log Y + C * B ^ 2 * Real.log Y) < 1 :=
  Real.exp_lt_one_iff.mpr
    (sheared_cubic_quadratic_log_exponent_neg hc hC hB hY hdominates)

end PellPaper
