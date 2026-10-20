import Pell.Main3LargeAnalyticComplexRadialLedger

/-!
# Sign-neutral logarithmic bounds for the fixed-key scales

The fixed-key source and target scales do not depend on the sign of the
shift coefficient.  Their existing logarithmic bounds were stated only for
a positive coefficient, although the literal real target-fibre branch may
have either sign.  Applying those results to `a` or `-a` removes this purely
formal mismatch while leaving the estimates unchanged.
-/

namespace PellPaper

noncomputable section

/-- The source-scale logarithmic bound for either sign of a nonzero shift. -/
theorem log_main3LargeAnalyticFixedKeySourceScaleUpper_le_of_ne_zero
    {D : ℕ} {a : ℤ} {key : ShiftedSquareAuxiliaryKey}
    (hD : 0 < D) (ha : a ≠ 0)
    (hC0pos : (0 : ℝ) < key.C₀)
    (hC0 : (key.C₀ : ℝ) ≤ 32 * Real.sqrt |(a : ℝ)|)
    (hr : (1 : ℝ) ≤ key.r) :
    Real.log (main3LargeAnalyticFixedKeySourceScaleUpper D key) ≤
      Real.log (D : ℝ) + Real.log 64 + Real.log |(a : ℝ)| / 2 := by
  rcases lt_or_gt_of_ne ha with haNeg | haPos
  · have hneg : 0 < -a := neg_pos.mpr haNeg
    have hC0neg : (key.C₀ : ℝ) ≤
        32 * Real.sqrt |((-a : ℤ) : ℝ)| := by
      simpa only [Int.cast_neg, abs_neg] using hC0
    have h := log_main3LargeAnalyticFixedKeySourceScaleUpper_le
      hD hneg hC0pos hC0neg hr
    simpa only [Int.cast_neg, abs_neg] using h
  · exact log_main3LargeAnalyticFixedKeySourceScaleUpper_le
      hD haPos hC0pos hC0 hr

/-- The target-scale logarithmic bound for either sign of a nonzero shift. -/
theorem log_main3LargeAnalyticFixedKeyTargetScaleUpper_le_of_ne_zero
    {Y : ℕ} {a : ℤ} {key : ShiftedSquareAuxiliaryKey}
    (hY : 0 < Y) (ha : a ≠ 0)
    (hC0pos : (0 : ℝ) < key.C₀)
    (hC0 : (key.C₀ : ℝ) ≤ 32 * Real.sqrt |(a : ℝ)|)
    (hell : (1 : ℝ) ≤ key.ell) :
    Real.log (main3LargeAnalyticFixedKeyTargetScaleUpper Y key) ≤
      Real.log (Y : ℝ) + Real.log 2048 + Real.log |(a : ℝ)| := by
  rcases lt_or_gt_of_ne ha with haNeg | haPos
  · have hneg : 0 < -a := neg_pos.mpr haNeg
    have hC0neg : (key.C₀ : ℝ) ≤
        32 * Real.sqrt |((-a : ℤ) : ℝ)| := by
      simpa only [Int.cast_neg, abs_neg] using hC0
    have h := log_main3LargeAnalyticFixedKeyTargetScaleUpper_le
      hY hneg hC0pos hC0neg hell
    simpa only [Int.cast_neg, abs_neg] using h
  · exact log_main3LargeAnalyticFixedKeyTargetScaleUpper_le
      hY haPos hC0pos hC0 hell

end

end PellPaper
