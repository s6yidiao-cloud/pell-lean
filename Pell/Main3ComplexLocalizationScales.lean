import Pell.Main3ComplexRatioFanDecay
import Mathlib.Tactic

/-!
# Exact logarithmic scales for the main3 complex-place fan estimate

The complex local-log adapter bounds the source coordinate by `3/M`.  At the
imaginary place, the shifted-square quotient error and unit norm give a
target-versus-source-square error at most `8 * sqrt |a| / n`, so the defect
logarithm is at most `12 * sqrt |a| / n` after the explicit `3/2` log loss.

This module chooses logarithmic scales whose negative exponentials are these
literal quantities.  It also computes exactly how subtracting `log 3` and
`log (12 * sqrt |a|)` changes the two-layer weight and bounds that fixed loss
uniformly in the fan index `k ≤ B`.

No fan-index choice, radial/discriminant estimate, determinant vanishing, or
point count is asserted here.
-/

namespace PellPaper

noncomputable section

/-- Source local-log scale with the exact `3/M` chart constant removed. -/
def main3ComplexSourceLogScale (M : ℕ) : ℝ :=
  Real.log (M : ℝ) - Real.log 3

/-- Defect local-log scale retaining the sharp shifted-square numerator
`12 * sqrt |a|` rather than degrading it to the cell mesh. -/
def main3ComplexDefectLogScale (a : ℤ) (N : ℕ) : ℝ :=
  Real.log (N : ℝ) - Real.log (12 * Real.sqrt |(a : ℝ)|)

/-- The source scale exponentiates to the literal complex-chart bound. -/
theorem exp_neg_main3ComplexSourceLogScale_eq
    {M : ℕ} (hM : 0 < M) :
    Real.exp (-main3ComplexSourceLogScale M) = 3 / (M : ℝ) := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  rw [main3ComplexSourceLogScale, neg_sub, Real.exp_sub,
    Real.exp_log (by norm_num : (0 : ℝ) < 3), Real.exp_log hMreal]

/-- The defect scale exponentiates to the literal `3/2`-inflated
shifted-square error at the lower endpoint `N`. -/
theorem exp_neg_main3ComplexDefectLogScale_eq
    {a : ℤ} {N : ℕ} (ha : a ≠ 0) (hN : 0 < N) :
    Real.exp (-main3ComplexDefectLogScale a N) =
      12 * Real.sqrt |(a : ℝ)| / (N : ℝ) := by
  have hsqrt : 0 < Real.sqrt |(a : ℝ)| := by
    exact Real.sqrt_pos.2 (abs_pos.mpr (by exact_mod_cast ha))
  have hnumerator : 0 < 12 * Real.sqrt |(a : ℝ)| := by positivity
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  rw [main3ComplexDefectLogScale, neg_sub, Real.exp_sub,
    Real.exp_log hnumerator, Real.exp_log hNreal]

/-- The source logarithmic scale is positive as soon as the mesh denominator
is strictly larger than its fixed chart numerator. -/
theorem main3ComplexSourceLogScale_pos
    {M : ℕ} (hM : 3 < M) :
    0 < main3ComplexSourceLogScale M := by
  have hthree : (0 : ℝ) < 3 := by norm_num
  have hMreal : (0 : ℝ) < M := by positivity
  have hlt : (3 : ℝ) < M := by exact_mod_cast hM
  have hlog := Real.strictMonoOn_log hthree hMreal hlt
  simpa only [main3ComplexSourceLogScale, sub_pos] using hlog

/-- The defect logarithmic scale is positive once the dyadic lower endpoint
is larger than the fixed shifted-square numerator. -/
theorem main3ComplexDefectLogScale_pos
    {a : ℤ} {N : ℕ}
    (ha : a ≠ 0) (hN : 12 * Real.sqrt |(a : ℝ)| < (N : ℝ)) :
    0 < main3ComplexDefectLogScale a N := by
  have hsqrt : 0 < Real.sqrt |(a : ℝ)| := by
    exact Real.sqrt_pos.2 (abs_pos.mpr (by exact_mod_cast ha))
  have hnumerator : 0 < 12 * Real.sqrt |(a : ℝ)| := by positivity
  have hNreal : (0 : ℝ) < N := hnumerator.trans hN
  have hlog := Real.strictMonoOn_log hnumerator hNreal hN
  simpa only [main3ComplexDefectLogScale, sub_pos] using hlog

/-- A row numerator `n ≥ N` has its `3/2`-inflated shifted-square error
bounded by the common defect scale attached to the lower endpoint `N`. -/
theorem three_halves_mul_shiftedSquareError_le_exp_neg_defectLogScale
    {a : ℤ} {N n : ℕ}
    (ha : a ≠ 0) (hN : 0 < N) (hNn : N ≤ n) :
    (3 / 2 : ℝ) *
        ((8 * Real.sqrt |(a : ℝ)|) / (n : ℝ)) ≤
  Real.exp (-main3ComplexDefectLogScale a N) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hNnreal : (N : ℝ) ≤ n := by exact_mod_cast hNn
  rw [exp_neg_main3ComplexDefectLogScale_eq ha hN]
  calc
    (3 / 2 : ℝ) *
          ((8 * Real.sqrt |(a : ℝ)|) / (n : ℝ)) =
        12 * Real.sqrt |(a : ℝ)| / (n : ℝ) := by ring
    _ ≤ 12 * Real.sqrt |(a : ℝ)| / (N : ℝ) := by
      exact div_le_div_of_nonneg_left (by positivity) hNreal hNnreal

/-- Exact change in the two-layer weight after fixed source and defect
logarithmic constants are removed. -/
theorem twoLayerWeight_sub_localizationConstants_eq
    (B k : ℕ) (logM logX cM cX : ℝ) (hk : k ≤ B) :
    twoLayerWeight B k (logM - cM) (logX - cX) =
      twoLayerWeight B k logM logX -
          (((B : ℝ) * ((B : ℝ) + 1) + (k : ℝ) ^ 2) * cM) -
        (((B : ℝ) + 1 - (k : ℝ)) * cX) := by
  rw [twoLayerWeight_eq B k hk, twoLayerWeight_eq B k hk]
  ring

/-- Uniform fixed-loss form of the preceding identity.  The source
coefficient is at most `2(B+1)^2`, and the defect coefficient is at most
`B+1`, for every `k ≤ B`. -/
theorem twoLayerWeight_sub_fixedLocalizationLoss_le
    (B k : ℕ) (logM logX cM cX : ℝ)
    (hk : k ≤ B) (hcM : 0 ≤ cM) (hcX : 0 ≤ cX) :
    twoLayerWeight B k logM logX -
        (2 * ((B : ℝ) + 1) ^ 2 * cM +
          ((B : ℝ) + 1) * cX) ≤
      twoLayerWeight B k (logM - cM) (logX - cX) := by
  have hkReal : (k : ℝ) ≤ B := by exact_mod_cast hk
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
      (B : ℝ) + 1 - (k : ℝ) ≤ (B : ℝ) + 1 := by
    linarith
  have hsourceMul :=
    mul_le_mul_of_nonneg_right hsourceCoefficient hcM
  have htargetMul :=
    mul_le_mul_of_nonneg_right htargetCoefficient hcX
  rw [twoLayerWeight_sub_localizationConstants_eq B k logM logX cM cX hk]
  linarith

/-- Exact specialization of the weight identity to the two complex-place
localization scales. -/
theorem twoLayerWeight_main3ComplexLocalizationScales_eq
    (B k M N : ℕ) (a : ℤ) (hk : k ≤ B) :
    twoLayerWeight B k
        (main3ComplexSourceLogScale M)
        (main3ComplexDefectLogScale a N) =
      twoLayerWeight B k (Real.log (M : ℝ)) (Real.log (N : ℝ)) -
          (((B : ℝ) * ((B : ℝ) + 1) + (k : ℝ) ^ 2) *
            Real.log 3) -
        (((B : ℝ) + 1 - (k : ℝ)) *
          Real.log (12 * Real.sqrt |(a : ℝ)|)) := by
  exact twoLayerWeight_sub_localizationConstants_eq
    B k (Real.log (M : ℝ)) (Real.log (N : ℝ))
      (Real.log 3) (Real.log (12 * Real.sqrt |(a : ℝ)|)) hk

/-- Uniform fixed loss for the actual complex-place localization constants.
This is the form consumed by the later main3 rate ledger. -/
theorem twoLayerWeight_sub_main3ComplexLocalizationLoss_le
    (B k M N : ℕ) (a : ℤ) (hk : k ≤ B) (ha : a ≠ 0) :
    twoLayerWeight B k (Real.log (M : ℝ)) (Real.log (N : ℝ)) -
        (2 * ((B : ℝ) + 1) ^ 2 * Real.log 3 +
          ((B : ℝ) + 1) *
            Real.log (12 * Real.sqrt |(a : ℝ)|)) ≤
      twoLayerWeight B k
        (main3ComplexSourceLogScale M)
        (main3ComplexDefectLogScale a N) := by
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt |(a : ℝ)| := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast Int.one_le_abs ha)
  have hfixedOne : (1 : ℝ) ≤ 12 * Real.sqrt |(a : ℝ)| := by
    nlinarith
  exact twoLayerWeight_sub_fixedLocalizationLoss_le
    B k (Real.log (M : ℝ)) (Real.log (N : ℝ))
      (Real.log 3) (Real.log (12 * Real.sqrt |(a : ℝ)|)) hk
      (Real.log_nonneg (by norm_num)) (Real.log_nonneg hfixedOne)

end

end PellPaper
