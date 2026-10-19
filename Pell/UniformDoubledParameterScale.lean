import Pell.UniformExceptional
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Admissibility on the dyadic squarefree-kernel scales

A kernel block meeting the range above `sqrt X` has lower endpoint at least
`sqrt X / 2`. The logarithmic parameter range changes by an absolute factor.
-/

namespace PellPaper
noncomputable section

/-- A scale between `sqrt X / 2` and `2X` loses at most a fixed factor four
in the square root of `log/loglog`.  Together with `theta < 2*uniformQ theta`,
this turns `UniformAdmissible c theta X` into the direct theta-bound with
coefficient `8c` at the nearby scale. -/
theorem theta_le_eight_mul_of_uniformAdmissible_of_sqrt_half_le_two_mul
    {c theta X Z : ℝ}
    (hc : 0 ≤ c)
    (hX : Real.exp 12 ≤ X)
    (hZlower : Real.sqrt X / 2 ≤ Z)
    (hZupper : Z ≤ 2 * X)
    (h : UniformAdmissible c theta X) :
    theta ≤ (8 * c) * Real.sqrt
      (Real.log Z / Real.log (Real.log Z)) := by
  have hexpPos : 0 < Real.exp (12 : ℝ) := Real.exp_pos _
  have hXpos : 0 < X := hexpPos.trans_le hX
  have hlogX : 12 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log hexpPos hX
  have hlogXpos : 0 < Real.log X := by linarith
  have hsqrtXpos : 0 < Real.sqrt X := Real.sqrt_pos.2 hXpos
  have hhalfpos : 0 < Real.sqrt X / 2 := div_pos hsqrtXpos (by norm_num)
  have hZpos : 0 < Z := hhalfpos.trans_le hZlower
  have hlogZlower : Real.log X / 4 ≤ Real.log Z := by
    have hlogTwo : Real.log (2 : ℝ) ≤ 1 := by
      have hlogTwo' :=
        Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hlogTwo' ⊢
      exact hlogTwo'
    have hlogSqrtDiv :
        Real.log (Real.sqrt X / 2) = Real.log X / 2 - Real.log 2 := by
      rw [Real.log_div (Real.sqrt_ne_zero'.mpr hXpos) (by norm_num),
        Real.log_sqrt hXpos.le]
    have hquarter : Real.log X / 4 ≤ Real.log (Real.sqrt X / 2) := by
      rw [hlogSqrtDiv]
      linarith
    exact hquarter.trans (Real.log_le_log hhalfpos hZlower)
  have hlogZpos : 0 < Real.log Z := by
    have : 0 < Real.log X / 4 := div_pos hlogXpos (by norm_num)
    exact this.trans_le hlogZlower
  have hloglogZpos : 0 < Real.log (Real.log Z) := by
    apply Real.log_pos
    have : 3 ≤ Real.log X / 4 := by linarith
    linarith
  have hloglogXpos : 0 < Real.log (Real.log X) := by
    apply Real.log_pos
    linarith
  have hlogZupper : Real.log Z ≤ 2 * Real.log X := by
    calc
      Real.log Z ≤ Real.log (2 * X) := Real.log_le_log hZpos hZupper
      _ = Real.log 2 + Real.log X := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hXpos.ne']
      _ ≤ 2 * Real.log X := by
        have hlogTwoLe : Real.log (2 : ℝ) ≤ Real.log X := by
          have hlogTwoLeOne : Real.log (2 : ℝ) ≤ 1 := by
            have hlogTwo' :=
              Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
            norm_num at hlogTwo' ⊢
            exact hlogTwo'
          linarith
        linarith
  have hloglogZupper :
      Real.log (Real.log Z) ≤ 2 * Real.log (Real.log X) := by
    calc
      Real.log (Real.log Z) ≤ Real.log (2 * Real.log X) :=
        Real.log_le_log hlogZpos hlogZupper
      _ = Real.log 2 + Real.log (Real.log X) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlogXpos.ne']
      _ ≤ 2 * Real.log (Real.log X) := by
        have hlogTwoLe : Real.log (2 : ℝ) ≤ Real.log (Real.log X) := by
          have hlogTwoLeOne : Real.log (2 : ℝ) ≤ 1 := by
            have hlogTwo' :=
              Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
            norm_num at hlogTwo' ⊢
            exact hlogTwo'
          have honeLe : (1 : ℝ) ≤ Real.log (Real.log X) := by
            apply (Real.le_log_iff_exp_le hlogXpos).2
            exact (Real.exp_one_lt_three.le.trans (by norm_num : (3 : ℝ) ≤ 12)).trans hlogX
          exact hlogTwoLeOne.trans honeLe
        linarith
  have hratio :
      Real.log X / Real.log (Real.log X) ≤
        16 * (Real.log Z / Real.log (Real.log Z)) := by
    calc
      Real.log X / Real.log (Real.log X) ≤
          (4 * Real.log Z) / Real.log (Real.log X) := by
        apply div_le_div_of_nonneg_right
        · linarith
        · exact hloglogXpos.le
      _ ≤ (4 * Real.log Z) / (Real.log (Real.log Z) / 2) := by
        apply div_le_div_of_nonneg_left
        · positivity
        · positivity
        · linarith
      _ = 8 * (Real.log Z / Real.log (Real.log Z)) := by ring
      _ ≤ 16 * (Real.log Z / Real.log (Real.log Z)) := by
        have : 0 ≤ Real.log Z / Real.log (Real.log Z) :=
          div_nonneg hlogZpos.le hloglogZpos.le
        linarith
  have hratioZnonneg :
      0 ≤ Real.log Z / Real.log (Real.log Z) :=
    div_nonneg hlogZpos.le hloglogZpos.le
  have hsqrtRatio :
      Real.sqrt (Real.log X / Real.log (Real.log X)) ≤
        4 * Real.sqrt (Real.log Z / Real.log (Real.log Z)) := by
    calc
      Real.sqrt (Real.log X / Real.log (Real.log X)) ≤
          Real.sqrt (16 * (Real.log Z / Real.log (Real.log Z))) :=
        Real.sqrt_le_sqrt hratio
      _ = 4 * Real.sqrt (Real.log Z / Real.log (Real.log Z)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
        norm_num
  have hthetaQ : theta ≤ 2 * (uniformQ theta : ℝ) := by
    linarith [theta_add_half_le_two_mul_uniformQ theta]
  unfold UniformAdmissible at h
  calc
    theta ≤ 2 * (uniformQ theta : ℝ) := hthetaQ
    _ ≤ 2 * (c * Real.sqrt
        (Real.log X / Real.log (Real.log X))) := by gcongr
    _ ≤ 2 * (c * (4 * Real.sqrt
        (Real.log Z / Real.log (Real.log Z)))) := by
      gcongr
    _ = (8 * c) * Real.sqrt
        (Real.log Z / Real.log (Real.log Z)) := by ring


end
end PellPaper
