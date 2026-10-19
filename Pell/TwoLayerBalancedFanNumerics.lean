import Pell.TwoLayerBalancedFanRate

/-!
# Uniform numerical lower bound for the balanced two-layer fan surplus

This module verifies the elementary inequality used in the simplified
balanced-box argument.  Under `theta >= 3`, `B` within one of `theta^2`,
`m >= 9/10`, `q <= 7 theta / 6`, and the stated localization defect, the
exact discrete fan surplus is at least `theta^2 / 12`.
-/

namespace PellPaper

noncomputable section

private theorem balanced_localization_defect_le_theta_sq_div_thirty_six
    (B : ℕ) (theta m : ℝ)
    (htheta : 3 ≤ theta)
    (hBupper : (B : ℝ) < theta ^ 2 + 1)
    (hmupper : m ≤ 1)
    (hdefect : (1 - m) * theta ^ 2 ≤ 1 / 50) :
    (1 - m) * (B : ℝ) * ((B : ℝ) + 1) ≤ theta ^ 2 / 36 := by
  let t : ℝ := theta ^ 2
  let b : ℝ := B
  let delta : ℝ := 1 - m
  have ht9 : 9 ≤ t := by
    dsimp [t]
    nlinarith [sq_nonneg (theta - 3)]
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hdelta0 : 0 ≤ delta := by dsimp [delta]; linarith
  have hbupper : b ≤ t + 1 := by
    dsimp [b, t]
    exact hBupper.le
  have hbbound : b * (b + 1) ≤ (t + 1) * (t + 2) := by
    exact mul_le_mul hbupper (by linarith) (by positivity) (by positivity)
  have htquad : 0 ≤ t * (t - 9) :=
    mul_nonneg ht0 (sub_nonneg.mpr ht9)
  have hpoly : (t + 1) * (t + 2) ≤ (25 / 18) * t ^ 2 := by
    nlinarith
  have hdeltaPoly : delta * (b * (b + 1)) ≤
      delta * ((25 / 18) * t ^ 2) :=
    mul_le_mul_of_nonneg_left (hbbound.trans hpoly) hdelta0
  have hdefect' : delta * t ≤ 1 / 50 := by
    simpa [delta, t] using hdefect
  have hscaled : (delta * t) * t ≤ (1 / 50) * t :=
    mul_le_mul_of_nonneg_right hdefect' ht0
  have hlast : delta * ((25 / 18) * t ^ 2) ≤ t / 36 := by
    nlinarith
  dsimp [delta, b, t] at hdeltaPoly hlast ⊢
  simpa only [mul_assoc] using hdeltaPoly.trans hlast

private theorem balanced_quadratic_loss_le
    (theta m q : ℝ)
    (htheta : 3 ≤ theta)
    (hmlower : 9 / 10 ≤ m)
    (hq0 : 0 ≤ q) (hq : q ≤ 7 * theta / 6) :
    q ^ 2 / (4 * m) ≤ (245 / 648) * theta ^ 2 := by
  have htheta0 : 0 ≤ theta := by linarith
  have ha0 : 0 ≤ 7 * theta / 6 := by positivity
  have hqgap : 0 ≤ 7 * theta / 6 - q := sub_nonneg.mpr hq
  have hqprod : 0 ≤ q * (7 * theta / 6 - q) :=
    mul_nonneg hq0 hqgap
  have haprod : 0 ≤ (7 * theta / 6) * (7 * theta / 6 - q) :=
    mul_nonneg ha0 hqgap
  have hq2 : q ^ 2 ≤ (49 / 36) * theta ^ 2 := by
    nlinarith
  have hmpos : 0 < m := by linarith
  have ht0 : 0 ≤ theta ^ 2 := sq_nonneg theta
  have hmt : (9 / 10) * theta ^ 2 ≤ m * theta ^ 2 :=
    mul_le_mul_of_nonneg_right hmlower ht0
  apply (div_le_iff₀ (by positivity : 0 < 4 * m)).mpr
  nlinarith

/-- The balanced two-layer fan surplus has the manuscript's uniform
`theta^2 / 12` lower bound under the simplified parameter inequalities. -/
theorem theta_sq_div_twelve_le_twoLayerBalancedFanSurplus
    (B k : ℕ) (theta m q : ℝ)
    (htheta : 3 ≤ theta)
    (hBlower : theta ^ 2 ≤ (B : ℝ))
    (hBupper : (B : ℝ) < theta ^ 2 + 1)
    (hmlower : 9 / 10 ≤ m) (hmupper : m ≤ 1)
    (hq0 : 0 ≤ q) (hq : q ≤ 7 * theta / 6)
    (hdefect : (1 - m) * theta ^ 2 ≤ 1 / 50) :
    theta ^ 2 / 12 ≤ twoLayerBalancedFanSurplus B k m q := by
  have hmpos : 0 < m := by linarith
  have hfan := twoLayerBalancedFanSurplus_lower_bound B k m q hmpos
  have hquad := balanced_quadratic_loss_le theta m q
    htheta hmlower hq0 hq
  have hlocal := balanced_localization_defect_le_theta_sq_div_thirty_six
    B theta m htheta hBupper hmupper hdefect
  have hBone : theta ^ 2 + 1 ≤ (B : ℝ) + 1 := by linarith
  nlinarith

end

end PellPaper

