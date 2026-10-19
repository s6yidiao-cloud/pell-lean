import Pell.Main3UnbalancedCeilingParameters
import Pell.TwoLayerBalancedFanRate
import Mathlib.Tactic

/-!
# Numerical gain in the main3 large-analytic determinant estimate

This module verifies the numerical inequality in the large-analytic part of
the manuscript.  It starts from the exact two-layer fan surplus, subtracts the
fixed `kappa_u = 1/100` discriminant/coordinate-height charge, and proves that
the result is still at least `theta^2 / 16` for the manuscript choices
`B = ceil(theta^2)` and `m_u >= 71/72`.

Only scalar parameter arithmetic occurs here.  No evaluation determinant,
cell-fibre estimate, or asymptotic absorption assertion is introduced.
-/

namespace PellPaper

noncomputable section

/-- The explicit `kappa_u = 1/100` charge retained after the embedding-basis
discriminant factor is divided out. -/
def main3LargeAnalyticDiscriminantCharge (B : ℕ) (theta : ℝ) : ℝ :=
  (1 / 100 : ℝ) * (B : ℝ) * ((B : ℝ) + 2) / (2 * theta ^ 2)

private theorem main3LargeAnalytic_quadraticLoss_le
    (theta m q : ℝ)
    (htheta : 3 ≤ theta)
    (hmlower : 71 / 72 ≤ m)
    (hq0 : 0 ≤ q) (hq : q ≤ theta) :
    q ^ 2 / (4 * m) ≤ (18 / 71 : ℝ) * theta ^ 2 := by
  have htheta0 : 0 ≤ theta := by linarith
  have hqgap : 0 ≤ theta - q := sub_nonneg.mpr hq
  have hqprod : 0 ≤ q * (theta - q) := mul_nonneg hq0 hqgap
  have hq2 : q ^ 2 ≤ theta ^ 2 := by nlinarith
  have hmpos : 0 < m := by linarith
  apply (div_le_iff₀ (by positivity : 0 < 4 * m)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hmlower) (sq_nonneg theta)]

private theorem main3LargeAnalytic_localizationDefect_le
    (B : ℕ) (theta m : ℝ)
    (htheta : 3 ≤ theta)
    (hBupper : (B : ℝ) < theta ^ 2 + 1)
    (hmupper : m ≤ 1)
    (hdefect : (1 - m) * theta ^ 2 ≤ 1 / 8) :
    (1 - m) * (B : ℝ) * ((B : ℝ) + 1) ≤
      (11 / 64 : ℝ) * theta ^ 2 := by
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
  have hpoly : (t + 1) * (t + 2) ≤ (11 / 8 : ℝ) * t ^ 2 := by
    nlinarith
  have hdeltaPoly : delta * (b * (b + 1)) ≤
      delta * ((11 / 8 : ℝ) * t ^ 2) :=
    mul_le_mul_of_nonneg_left (hbbound.trans hpoly) hdelta0
  have hdefect' : delta * t ≤ (1 / 8 : ℝ) := by
    simpa [delta, t] using hdefect
  have hscaled : (delta * t) * t ≤ (1 / 8 : ℝ) * t :=
    mul_le_mul_of_nonneg_right hdefect' ht0
  have hlast : delta * ((11 / 8 : ℝ) * t ^ 2) ≤
      (11 / 64 : ℝ) * t := by
    nlinarith
  dsimp [delta, b, t] at hdeltaPoly hlast ⊢
  simpa only [mul_assoc] using hdeltaPoly.trans hlast

private theorem main3LargeAnalytic_discriminantCharge_le
    (B : ℕ) (theta : ℝ)
    (htheta : 3 ≤ theta)
    (hBupper : (B : ℝ) < theta ^ 2 + 1) :
    main3LargeAnalyticDiscriminantCharge B theta ≤
      theta ^ 2 / 128 := by
  let t : ℝ := theta ^ 2
  let b : ℝ := B
  have ht9 : 9 ≤ t := by
    dsimp [t]
    nlinarith [sq_nonneg (theta - 3)]
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht9
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hbupper : b ≤ t + 1 := by
    dsimp [b, t]
    exact hBupper.le
  have hbbound : b * (b + 2) ≤ (t + 1) * (t + 3) := by
    exact mul_le_mul hbupper (by linarith) (by positivity) (by linarith)
  have htquad : 0 ≤ t * (t - 9) :=
    mul_nonneg htpos.le (sub_nonneg.mpr ht9)
  have hpoly : (t + 1) * (t + 3) ≤ (25 / 16 : ℝ) * t ^ 2 := by
    nlinarith
  have hnumerator : b * (b + 2) ≤ (25 / 16 : ℝ) * t ^ 2 :=
    hbbound.trans hpoly
  unfold main3LargeAnalyticDiscriminantCharge
  dsimp [b, t] at hnumerator htpos ⊢
  apply (div_le_iff₀ (by positivity : 0 < 2 * theta ^ 2)).mpr
  nlinarith

/-- After the exact `kappa_u = 1/100` discriminant charge, the large-analytic
fan surplus retains the manuscript gain `theta^2 / 16`. -/
theorem theta_sq_div_sixteen_le_main3LargeAnalytic_chargedFanSurplus
    (B k : ℕ) (theta m q : ℝ)
    (htheta : 3 ≤ theta)
    (hBlower : theta ^ 2 ≤ (B : ℝ))
    (hBupper : (B : ℝ) < theta ^ 2 + 1)
    (hmlower : 71 / 72 ≤ m) (hmupper : m ≤ 1)
    (hq0 : 0 ≤ q) (hq : q ≤ theta)
    (hdefect : (1 - m) * theta ^ 2 ≤ 1 / 8) :
    theta ^ 2 / 16 ≤
      twoLayerBalancedFanSurplus B k m q -
        main3LargeAnalyticDiscriminantCharge B theta := by
  have hmpos : 0 < m := by linarith
  have hfan := twoLayerBalancedFanSurplus_lower_bound B k m q hmpos
  have hquad := main3LargeAnalytic_quadraticLoss_le
    theta m q htheta hmlower hq0 hq
  have hlocal := main3LargeAnalytic_localizationDefect_le
    B theta m htheta hBupper hmupper hdefect
  have hcharge := main3LargeAnalytic_discriminantCharge_le
    B theta htheta hBupper
  have hBhalf : theta ^ 2 / 2 ≤ ((B : ℝ) + 1) / 2 := by
    linarith
  have hthetaSq0 : 0 ≤ theta ^ 2 := sq_nonneg theta
  have hcoeff :
      theta ^ 2 / 16 + (18 / 71 : ℝ) * theta ^ 2 +
          (11 / 64 : ℝ) * theta ^ 2 + theta ^ 2 / 128 ≤
        theta ^ 2 / 2 := by
    nlinarith
  linarith

/-- The preceding numerical gain specialized to the literal main3 ceiling
degree and logarithmic mesh exponent. -/
theorem theta_sq_div_sixteen_le_main3LargeAnalytic_ceilingChargedFanSurplus
    (theta : ℝ) (Y : ℕ) (k : ℕ) (q : ℝ)
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hq0 : 0 ≤ q) (hq : q ≤ theta) :
    theta ^ 2 / 16 ≤
      twoLayerBalancedFanSurplus
          (main3BalancedDegree theta) k
          (main3UnbalancedMLogExponent theta Y) q -
        main3LargeAnalyticDiscriminantCharge
          (main3BalancedDegree theta) theta := by
  obtain ⟨_hMpos, _hMle, hmlower, hmupper, hdefect, _hmLog⟩ :=
    main3UnbalancedM_parameter_package theta Y htheta hY
  exact theta_sq_div_sixteen_le_main3LargeAnalytic_chargedFanSurplus
    (main3BalancedDegree theta) k theta
      (main3UnbalancedMLogExponent theta Y) q htheta
      (main3UnbalancedDegree_nearSquare theta).1
      (main3UnbalancedDegree_nearSquare theta).2
      hmlower hmupper hq0 hq hdefect

end

end PellPaper
