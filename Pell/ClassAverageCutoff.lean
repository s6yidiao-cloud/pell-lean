import Pell.ClassAverage

/-!
# Elementary algebra for the class-average cutoff

The cutoff in the final class-average argument is
`c * sqrt (log X / log (log X))`.  This module proves its positivity and
reciprocal identities and connects the reciprocal to `classAverageScale`.
These are algebraic facts; no exceptional-set or class-number estimate is
assumed or asserted here.
-/

namespace PellPaper

noncomputable section

/-- The cutoff used in the final class-average argument. -/
def classAverageCutoff (c X : ℝ) : ℝ :=
  c * Real.sqrt (Real.log X / Real.log (Real.log X))

theorem one_lt_log_of_exp_one_lt {X : ℝ} (hX : Real.exp 1 < X) :
    1 < Real.log X := by
  exact (Real.lt_log_iff_exp_lt ((Real.exp_pos 1).trans hX)).mpr hX

theorem classAverageCutoff_log_pos {X : ℝ} (hX : Real.exp 1 < X) :
    0 < Real.log X :=
  zero_lt_one.trans (one_lt_log_of_exp_one_lt hX)

theorem classAverageCutoff_log_log_pos {X : ℝ} (hX : Real.exp 1 < X) :
    0 < Real.log (Real.log X) :=
  Real.log_pos (one_lt_log_of_exp_one_lt hX)

theorem classAverageCutoff_pos {c X : ℝ} (hc : 0 < c)
    (hX : Real.exp 1 < X) : 0 < classAverageCutoff c X := by
  exact mul_pos hc (Real.sqrt_pos.2 (div_pos
    (classAverageCutoff_log_pos hX) (classAverageCutoff_log_log_pos hX)))

theorem classAverageCutoff_ne_zero {c X : ℝ} (hc : 0 < c)
    (hX : Real.exp 1 < X) : classAverageCutoff c X ≠ 0 :=
  (classAverageCutoff_pos hc hX).ne'

/-- The reciprocal cutoff has the saving factor from the headline bound.
The identity holds even outside the positive range because Lean's real
division and square root are total functions. -/
theorem one_div_classAverageCutoff (c X : ℝ) :
    1 / classAverageCutoff c X =
      (1 / c) * Real.sqrt (Real.log (Real.log X) / Real.log X) := by
  simp only [classAverageCutoff, one_div, mul_inv_rev, ← Real.sqrt_inv, inv_div]
  ring

theorem classAverageCutoff_mul_saving {c X : ℝ} (hX : Real.exp 1 < X) :
    classAverageCutoff c X *
      Real.sqrt (Real.log (Real.log X) / Real.log X) = c := by
  have hratio : 0 < Real.log X / Real.log (Real.log X) :=
    div_pos (classAverageCutoff_log_pos hX) (classAverageCutoff_log_log_pos hX)
  have hsqrt : Real.sqrt (Real.log X / Real.log (Real.log X)) ≠ 0 :=
    (Real.sqrt_pos.2 hratio).ne'
  have hrecip : Real.sqrt (Real.log (Real.log X) / Real.log X) =
      (Real.sqrt (Real.log X / Real.log (Real.log X)))⁻¹ := by
    rw [← Real.sqrt_inv, inv_div]
  rw [classAverageCutoff, hrecip]
  exact mul_inv_cancel_right₀ hsqrt c

theorem rpow_three_halves_eq_mul_sqrt {x : ℝ} (hx : 0 < x) :
    Real.rpow x (3 / 2) = x * Real.sqrt x := by
  calc
    Real.rpow x (3 / 2) = Real.rpow x (1 + 1 / 2) := by norm_num
    _ = x * Real.sqrt x := by
      rw [Real.rpow_eq_pow, Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- Express the class-average scale as the usual `X^(3/2) / log X`
scale multiplied by the reciprocal-cutoff saving. -/
theorem classAverageScale_eq_base_mul_saving {X : ℝ} (hX : 1 < X) :
    classAverageScale X =
      (Real.rpow X (3 / 2) / Real.log X) *
        Real.sqrt (Real.log (Real.log X) / Real.log X) := by
  have hlog : 0 < Real.log X := Real.log_pos hX
  rw [classAverageScale, Real.sqrt_div' _ hlog.le,
    rpow_three_halves_eq_mul_sqrt hlog]
  ring

/-- Dividing the base scale by the cutoff produces exactly the scale in
the class-average theorem, up to the constant `1 / c`. -/
theorem base_div_classAverageCutoff {c X : ℝ} (hX : 1 < X) :
    (Real.rpow X (3 / 2) / Real.log X) / classAverageCutoff c X =
      (1 / c) * classAverageScale X := by
  rw [div_eq_mul_one_div, one_div_classAverageCutoff,
    classAverageScale_eq_base_mul_saving hX]
  ring

end

end PellPaper
