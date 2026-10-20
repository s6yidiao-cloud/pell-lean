import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Logarithmic absorption for the main4 Wilson error scales

This Mathlib-only module absorbs the two lower-order powers that arise after
summing the low and high Abel ranges.  The analytic input is the standard
Mathlib fact that every fixed real power of `log X` is little-oh of every
positive real power of `X`.
-/

namespace PellPaper

open Asymptotics Filter

/-- Every fixed real logarithmic power is eventually bounded by a fixed
positive power of the ambient real variable. -/
private theorem eventually_log_rpow_le_rpow (a b : ℝ) (hb : 0 < b) :
    ∀ᶠ X : ℝ in atTop,
      (Real.log X) ^ a ≤ X ^ b := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop a hb).def one_pos
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with X hX hXone
  have hXpos : 0 < X := zero_lt_one.trans hXone
  have hlogpos : 0 < Real.log X := Real.log_pos hXone
  change ‖(Real.log X) ^ a‖ ≤ (1 : ℝ) * ‖X ^ b‖ at hX
  simpa only [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hlogpos.le a),
      abs_of_nonneg (Real.rpow_nonneg hXpos.le b), one_mul] using hX

/-- The `X^(11/12) (log X)^(7/6)` error is eventually absorbed by the
natural scale `X / sqrt (log X)`. -/
theorem eventually_main4Wilson_error_one_le_naturalScale :
    ∀ᶠ X : ℝ in atTop,
      X ^ (11 / 12 : ℝ) * (Real.log X) ^ (7 / 6 : ℝ) ≤
        X / Real.sqrt (Real.log X) := by
  have hsmall := eventually_log_rpow_le_rpow
    (5 / 3 : ℝ) (1 / 12 : ℝ) (by norm_num)
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with X hlogPower hX
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hlogpos : 0 < Real.log X := Real.log_pos hX
  have hsqrtpos : 0 < Real.sqrt (Real.log X) := Real.sqrt_pos.2 hlogpos
  apply (le_div_iff₀ hsqrtpos).2
  calc
    (X ^ (11 / 12 : ℝ) * (Real.log X) ^ (7 / 6 : ℝ)) *
          Real.sqrt (Real.log X) =
        X ^ (11 / 12 : ℝ) *
          ((Real.log X) ^ (7 / 6 : ℝ) * (Real.log X) ^ (1 / 2 : ℝ)) := by
            rw [Real.sqrt_eq_rpow]
            ring
    _ = X ^ (11 / 12 : ℝ) * (Real.log X) ^ (5 / 3 : ℝ) := by
      rw [← Real.rpow_add hlogpos]
      norm_num
    _ ≤ X ^ (11 / 12 : ℝ) * X ^ (1 / 12 : ℝ) :=
      mul_le_mul_of_nonneg_left hlogPower (Real.rpow_nonneg hXpos.le _)
    _ = X := by
      rw [← Real.rpow_add hXpos]
      norm_num

/-- The `X^(5/6) (log X)^(13/6)` error is eventually absorbed by the
natural scale `X / sqrt (log X)`. -/
theorem eventually_main4Wilson_error_two_le_naturalScale :
    ∀ᶠ X : ℝ in atTop,
      X ^ (5 / 6 : ℝ) * (Real.log X) ^ (13 / 6 : ℝ) ≤
        X / Real.sqrt (Real.log X) := by
  have hsmall := eventually_log_rpow_le_rpow
    (8 / 3 : ℝ) (1 / 6 : ℝ) (by norm_num)
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with X hlogPower hX
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hlogpos : 0 < Real.log X := Real.log_pos hX
  have hsqrtpos : 0 < Real.sqrt (Real.log X) := Real.sqrt_pos.2 hlogpos
  apply (le_div_iff₀ hsqrtpos).2
  calc
    (X ^ (5 / 6 : ℝ) * (Real.log X) ^ (13 / 6 : ℝ)) *
          Real.sqrt (Real.log X) =
        X ^ (5 / 6 : ℝ) *
          ((Real.log X) ^ (13 / 6 : ℝ) * (Real.log X) ^ (1 / 2 : ℝ)) := by
            rw [Real.sqrt_eq_rpow]
            ring
    _ = X ^ (5 / 6 : ℝ) * (Real.log X) ^ (8 / 3 : ℝ) := by
      rw [← Real.rpow_add hlogpos]
      norm_num
    _ ≤ X ^ (5 / 6 : ℝ) * X ^ (1 / 6 : ℝ) :=
      mul_le_mul_of_nonneg_left hlogPower (Real.rpow_nonneg hXpos.le _)
    _ = X := by
      rw [← Real.rpow_add hXpos]
      norm_num

end PellPaper
