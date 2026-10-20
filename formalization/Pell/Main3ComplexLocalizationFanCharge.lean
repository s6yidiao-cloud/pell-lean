import Pell.Main3ComplexLocalizationScales
import Mathlib.Tactic

/-!
# Sharp fan charge for the main3 complex localization constants

The generic localization-scale bound allows the defect coefficient to be as
large as `B+1`.  In the actual two-layer fan, however, the selected index
satisfies `1 ≤ k`, so the exact coefficient `B+1-k` is at most `B`.

This module records that sharper loss and splits
`log (12 * sqrt |a|)` into a fixed part plus `(1/2) log |a|`.  Consequently
the complex defect localization costs exactly at most
`(B/2) log |a|`, up to a fixed degree-dependent term.  No fan index is
selected and no radial, discriminant, determinant, or counting statement is
asserted here.
-/

namespace PellPaper

noncomputable section

/-- The fixed part of the complex localization loss after using `1 ≤ k`.
It contains the source chart constant `3` and the fixed numerator `12`, but
no shift-dependent logarithm. -/
def main3ComplexLocalizationFixedFanCost (B : ℕ) : ℝ :=
  2 * ((B : ℝ) + 1) ^ 2 * Real.log 3 + (B : ℝ) * Real.log 12

/-- In a positive fan, the exact target coefficient `B+1-k` is at most `B`.
This sharpens the generic localization loss by one full copy of `cX`. -/
theorem twoLayerWeight_sub_fixedPositiveFanLocalizationLoss_le
    (B k : ℕ) (logM logX cM cX : ℝ)
    (hkpos : 1 ≤ k) (hkB : k ≤ B) (hcM : 0 ≤ cM) (hcX : 0 ≤ cX) :
    twoLayerWeight B k logM logX -
        (2 * ((B : ℝ) + 1) ^ 2 * cM + (B : ℝ) * cX) ≤
      twoLayerWeight B k (logM - cM) (logX - cX) := by
  have hkReal : (k : ℝ) ≤ B := by exact_mod_cast hkB
  have hkOne : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
  have hkNonneg : (0 : ℝ) ≤ k := by positivity
  have hBNonneg : (0 : ℝ) ≤ B := by positivity
  have hkSq : (k : ℝ) ^ 2 ≤ (B : ℝ) ^ 2 := by
    nlinarith
  have hsourceCoefficient :
      (B : ℝ) * ((B : ℝ) + 1) + (k : ℝ) ^ 2 ≤
        2 * ((B : ℝ) + 1) ^ 2 := by
    nlinarith
  have htargetCoefficientNonneg :
      0 ≤ (B : ℝ) + 1 - (k : ℝ) := by linarith
  have htargetCoefficient :
      (B : ℝ) + 1 - (k : ℝ) ≤ (B : ℝ) := by
    linarith
  have hsourceMul :=
    mul_le_mul_of_nonneg_right hsourceCoefficient hcM
  have htargetMul :=
    mul_le_mul_of_nonneg_right htargetCoefficient hcX
  rw [twoLayerWeight_sub_localizationConstants_eq
    B k logM logX cM cX hkB]
  linarith

/-- The shift-dependent numerator logarithm is exactly one half of
`log |a|` plus the fixed `log 12`. -/
theorem log_twelve_mul_sqrt_abs_eq
    {a : ℤ} (ha : a ≠ 0) :
    Real.log (12 * Real.sqrt |(a : ℝ)|) =
      Real.log 12 + Real.log |(a : ℝ)| / 2 := by
  have haReal : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hsqrt : Real.sqrt |(a : ℝ)| ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (abs_pos.mpr haReal))
  rw [Real.log_mul (by norm_num : (12 : ℝ) ≠ 0) hsqrt,
    Real.log_sqrt (abs_nonneg (a : ℝ))]

/-- Sharp localization loss at the literal main3 complex scales.  The only
shift-dependent contribution is `(B/2) * log |a|`; everything else is the
explicit fixed fan cost. -/
theorem twoLayerWeight_sub_main3ComplexPositiveFanCharge_le
    (B k M N : ℕ) (a : ℤ)
    (hkpos : 1 ≤ k) (hkB : k ≤ B) (ha : a ≠ 0) :
    twoLayerWeight B k (Real.log (M : ℝ)) (Real.log (N : ℝ)) -
        ((B : ℝ) / 2 * Real.log |(a : ℝ)| +
          main3ComplexLocalizationFixedFanCost B) ≤
      twoLayerWeight B k
        (main3ComplexSourceLogScale M)
        (main3ComplexDefectLogScale a N) := by
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt |(a : ℝ)| := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast Int.one_le_abs ha)
  have hfixedOne : (1 : ℝ) ≤ 12 * Real.sqrt |(a : ℝ)| := by
    nlinarith
  have hbase := twoLayerWeight_sub_fixedPositiveFanLocalizationLoss_le
    B k (Real.log (M : ℝ)) (Real.log (N : ℝ))
      (Real.log 3) (Real.log (12 * Real.sqrt |(a : ℝ)|))
      hkpos hkB (Real.log_nonneg (by norm_num))
      (Real.log_nonneg hfixedOne)
  rw [log_twelve_mul_sqrt_abs_eq ha] at hbase
  rw [main3ComplexSourceLogScale, main3ComplexDefectLogScale,
    log_twelve_mul_sqrt_abs_eq ha]
  unfold main3ComplexLocalizationFixedFanCost
  convert hbase using 1
  all_goals ring

end

end PellPaper
