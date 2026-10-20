import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Eventual absorption of the explicit selected-moment logarithmic error

This Mathlib-only estimate concerns a literal expression in a natural scale.
For `log Y ≥ 1`, its two terms are bounded by `720` and `6400` times
`Y² (log Y)³`.  The standard estimate `(log Y)³ = o(Y)` then absorbs their
sum into `Y³`.  No character, moment, or arithmetic input is assumed.
-/

namespace PellPaper

open Asymptotics Filter

private theorem selectedMomentLogError_le_cubicLog (y l : ℝ) (hl : 1 ≤ l) :
    16 * y ^ 2 * (1 + 4 * l) * (1 + 2 * l) ^ 2 +
        256 * y ^ 2 * (1 + Real.log 2 + 3 * l) ^ 2 ≤
      7120 * y ^ 2 * l ^ 3 := by
  have hl0 : 0 ≤ l := le_trans zero_le_one hl
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlog2nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hfirst : 16 * (1 + 4 * l) * (1 + 2 * l) ^ 2 ≤ 720 * l ^ 3 := by
    calc
      16 * (1 + 4 * l) * (1 + 2 * l) ^ 2 ≤
          (16 * (5 * l)) * (3 * l) ^ 2 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (by linarith : 1 + 4 * l ≤ 5 * l)
            (by norm_num)
        · exact pow_le_pow_left₀ (by linarith) (by linarith : 1 + 2 * l ≤ 3 * l) 2
        · exact sq_nonneg _
        · positivity
      _ = 720 * l ^ 3 := by ring
  have hpower : l ^ 2 ≤ l ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hl (sq_nonneg l)]
  have hsecond : 256 * (1 + Real.log 2 + 3 * l) ^ 2 ≤ 6400 * l ^ 3 := by
    calc
      256 * (1 + Real.log 2 + 3 * l) ^ 2 ≤ 256 * (5 * l) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact pow_le_pow_left₀ (by linarith) (by linarith) 2
      _ = 6400 * l ^ 2 := by ring
      _ ≤ 6400 * l ^ 3 := mul_le_mul_of_nonneg_left hpower (by norm_num)
  calc
    16 * y ^ 2 * (1 + 4 * l) * (1 + 2 * l) ^ 2 +
        256 * y ^ 2 * (1 + Real.log 2 + 3 * l) ^ 2 =
        y ^ 2 * (16 * (1 + 4 * l) * (1 + 2 * l) ^ 2 +
          256 * (1 + Real.log 2 + 3 * l) ^ 2) := by ring
    _ ≤ y ^ 2 * (720 * l ^ 3 + 6400 * l ^ 3) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (sq_nonneg y)
    _ = 7120 * y ^ 2 * l ^ 3 := by ring

/-- The explicit logarithmic error is eventually at most the cubic natural
scale.  The eventual threshold is independent of any arithmetic data. -/
theorem eventually_selectedMomentLogError_le_cube :
    ∀ᶠ Y : ℕ in atTop,
      16 * (Y : ℝ) ^ 2 * (1 + 4 * Real.log (Y : ℝ)) *
          (1 + 2 * Real.log (Y : ℝ)) ^ 2 +
        256 * (Y : ℝ) ^ 2 * (1 + Real.log 2 + 3 * Real.log (Y : ℝ)) ^ 2 ≤
        (Y : ℝ) ^ 3 := by
  have hlittle : (fun y : ℝ => Real.log y ^ (3 : ℕ)) =o[atTop]
      (fun y : ℝ => y) := by
    simpa only [Real.rpow_ofNat, Real.rpow_one] using
      isLittleO_log_rpow_rpow_atTop (3 : ℝ) (show (0 : ℝ) < 1 by norm_num)
  have hcast : Tendsto (fun Y : ℕ => (Y : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hsmall := (hlittle.comp_tendsto hcast).def (show (0 : ℝ) < 1 / 7120 by norm_num)
  have hlog := (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop 1
  filter_upwards [hsmall, hlog] with Y hY hlogY
  have hlog0 : 0 ≤ Real.log (Y : ℝ) := le_trans zero_le_one hlogY
  change ‖Real.log (Y : ℝ) ^ (3 : ℕ)‖ ≤ (1 / 7120 : ℝ) * ‖(Y : ℝ)‖ at hY
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog0 3),
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg Y)] at hY
  have hscale : 7120 * Real.log (Y : ℝ) ^ 3 ≤ (Y : ℝ) := by nlinarith [hY]
  calc
    16 * (Y : ℝ) ^ 2 * (1 + 4 * Real.log (Y : ℝ)) *
          (1 + 2 * Real.log (Y : ℝ)) ^ 2 +
        256 * (Y : ℝ) ^ 2 * (1 + Real.log 2 + 3 * Real.log (Y : ℝ)) ^ 2 ≤
        7120 * (Y : ℝ) ^ 2 * Real.log (Y : ℝ) ^ 3 :=
      selectedMomentLogError_le_cubicLog (Y : ℝ) (Real.log (Y : ℝ)) hlogY
    _ = (Y : ℝ) ^ 2 * (7120 * Real.log (Y : ℝ) ^ 3) := by ring
    _ ≤ (Y : ℝ) ^ 2 * (Y : ℝ) :=
      mul_le_mul_of_nonneg_left hscale (sq_nonneg (Y : ℝ))
    _ = (Y : ℝ) ^ 3 := by ring

end PellPaper
