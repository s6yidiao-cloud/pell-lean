import Pell.Main3LargeAnalyticSignNeutralScaleLogBounds
import Pell.Main3LargeAnalyticTargetFibreHeightInputs
import Pell.Main3UnbalancedEnlargedDirectRangeSummation
import Mathlib.Tactic

/-!
# Coarse logarithmic coordinate budgets for a literal target fibre

For a nonempty fixed-key target fibre, the retained certificate supplies the
normalization bounds on `C₀`, `r`, and `ell`.  The enlarged active-index
estimates separately bound the shift and the source dyadic endpoint.  This
module combines those already checked inputs with the definitions of the raw
coordinate radii.

The constants are deliberately coarse: throughout `65536 ≤ Y` and
`3 ≤ theta`, the source radius costs at most `6 * theta * log Y` and the
target radius at most `2 * theta * log Y`.  No eventual-growth hypothesis is
used.
-/

namespace PellPaper

noncomputable section

/-- A large-analytic index has a nonzero shifted-square parameter. -/
theorem main3LargeAnalytic_shift_ne_zero_of_largeAnalyticIndex
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    shiftedSquareA h v ≠ 0 := by
  have hiLarge :=
    mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi
  have hiActive :=
    mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiLarge.1
  have hiBroad :=
    mem_unbalancedShiftedSquareDyadicCoverIndices.mp hiActive.1
  exact shiftedSquareA_ne_zero hiBroad.1 (by omega)

/-- At the fixed numerical base threshold, `log Y` absorbs the additive
constant `1 + log 2`. -/
theorem one_add_log_two_le_log_of_65536_le
    {Y : ℕ} (hY : 65536 ≤ Y) :
    1 + Real.log 2 ≤ Real.log (Y : ℝ) := by
  have hYreal : (65536 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hlogMono : Real.log (65536 : ℝ) ≤ Real.log (Y : ℝ) :=
    Real.log_le_log (by norm_num) hYreal
  have hlogTwoLower : (1 / 2 : ℝ) ≤ Real.log 2 := by
    exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9 |>.le
  rw [show (65536 : ℝ) = 2 ^ (16 : ℕ) by norm_num,
    Real.log_pow] at hlogMono
  norm_num at hlogMono
  linarith

/-- The sharp active-index shift estimate implies a convenient logarithmic
budget independent of the sign of the shift. -/
theorem main3LargeAnalytic_log_abs_shift_le_two_mul_log
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    Real.log |(shiftedSquareA h v : ℝ)| ≤
      2 * Real.log (Y : ℝ) := by
  have ha : shiftedSquareA h v ≠ 0 :=
    main3LargeAnalytic_shift_ne_zero_of_largeAnalyticIndex hi
  have haReal : (shiftedSquareA h v : ℝ) ≠ 0 := by exact_mod_cast ha
  have habsPos : 0 < |(shiftedSquareA h v : ℝ)| := abs_pos.mpr haReal
  have hiLarge :=
    mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi
  have hiBroad :=
    (mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiLarge.1).1
  have hshift : |(shiftedSquareA h v : ℝ)| < 2 * (Y : ℝ) :=
    (main3UnbalancedEnlargedShiftedSquareIndex_shift_abs_bounds
      htheta (by omega : 2 ≤ Y) hiBroad).2.2
  have hlog := Real.log_le_log habsPos hshift.le
  have hYpos : (0 : ℝ) < (Y : ℝ) := by positivity
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hYpos.ne'] at hlog
  have hlogTwo : Real.log 2 ≤ Real.log (Y : ℝ) := by
    exact Real.log_le_log (by norm_num) (by
      exact_mod_cast (show 2 ≤ Y by omega))
  linarith

/-- The enlarged active logarithmic factor gives a uniform coarse budget for
the source dyadic endpoint. -/
theorem main3LargeAnalytic_log_source_dyadic_le_eight_mul_theta_mul_log
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    Real.log (D : ℝ) ≤ 8 * theta * Real.log (Y : ℝ) := by
  have hiLarge :=
    mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi
  have hiActive :=
    mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiLarge.1
  have hendpoints :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_endpoint_height_package
      htheta (by omega : 2 ≤ Y) hiActive.1 hiActive.2
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hendpoints.1
  have hlogFactor :=
    main3UnbalancedEnlargedActiveIndex_logFactor_le
      htheta (by omega : 2 ≤ Y) hiLarge.1
  have hlogTwoNonneg : 0 ≤ Real.log (2 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hlogDToFactor :
      Real.log (D : ℝ) ≤ 1 + Real.log (2 * (D : ℝ)) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hDpos.ne']
    linarith
  have hYpos : (0 : ℝ) < (Y : ℝ) := by positivity
  have hlogYNonneg : 0 ≤ Real.log (Y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ Y by omega))
  have hlogTwoY :
      Real.log (((2 * Y : ℕ) : ℝ)) =
        Real.log 2 + Real.log (Y : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hYpos.ne']
  have hsmall :
      1 + Real.log (((2 * Y : ℕ) : ℝ)) ≤
        2 * Real.log (Y : ℝ) := by
    rw [hlogTwoY]
    linarith [one_add_log_two_le_log_of_65536_le hY]
  have hthetaUpper : theta + 1 ≤ 2 * theta := by linarith
  calc
    Real.log (D : ℝ) ≤ 1 + Real.log (2 * (D : ℝ)) := hlogDToFactor
    _ ≤ 2 * (theta + 1) *
        (1 + Real.log (((2 * Y : ℕ) : ℝ))) := hlogFactor
    _ ≤ 2 * (2 * theta) *
        (1 + Real.log (((2 * Y : ℕ) : ℝ))) := by
      gcongr
    _ ≤ 2 * (2 * theta) * (2 * Real.log (Y : ℝ)) := by
      gcongr
    _ = 8 * theta * Real.log (Y : ℝ) := by ring

/-- On a nonempty literal target fibre, the fixed-key source-coordinate
radius has logarithmic size at most `6 * theta * log Y`. -/
theorem log_main3LargeAnalyticFixedKeySourceCoordinateRadius_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    (p₀ : {p // p ∈ main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y}) :
    Real.log (main3LargeAnalyticFixedKeySourceCoordinateRadius
      (shiftedSquareA h v) D key) ≤
        6 * theta * Real.log (Y : ℝ) := by
  have ha : shiftedSquareA h v ≠ 0 :=
    main3LargeAnalytic_shift_ne_zero_of_largeAnalyticIndex hi
  have haReal : (shiftedSquareA h v : ℝ) ≠ 0 := by exact_mod_cast ha
  have habsPos : 0 < |(shiftedSquareA h v : ℝ)| := abs_pos.mpr haReal
  have hkey := main3LargeAnalytic_targetFibrePoint_key_scale_package
    htheta hY hi key cell y p₀
  have hiLarge :=
    mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi
  have hiActive :=
    mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiLarge.1
  have hendpoints :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_endpoint_height_package
      htheta (by omega : 2 ≤ Y) hiActive.1 hiActive.2
  have hDpos : 0 < D := hendpoints.1
  have hscaleLog :=
    log_main3LargeAnalyticFixedKeySourceScaleUpper_le_of_ne_zero
      hDpos ha hkey.1 hkey.2.1 hkey.2.2.1
  have hscalePos :
      0 < main3LargeAnalyticFixedKeySourceScaleUpper D key := by
    unfold main3LargeAnalyticFixedKeySourceScaleUpper
    exact div_pos
      (mul_pos (mul_pos (by norm_num) (by exact_mod_cast hDpos)) hkey.1)
      (pow_pos (zero_lt_one.trans_le hkey.2.2.1) 2)
  have hradiusLog :
      Real.log (main3LargeAnalyticFixedKeySourceCoordinateRadius
          (shiftedSquareA h v) D key) =
        Real.log 1024 + Real.log |(shiftedSquareA h v : ℝ)| +
          Real.log (main3LargeAnalyticFixedKeySourceScaleUpper D key) / 2 := by
    unfold main3LargeAnalyticFixedKeySourceCoordinateRadius
      shiftedSquareRawCoordinateScaleLoss
    rw [Real.log_mul
        (mul_ne_zero (by norm_num : (1024 : ℝ) ≠ 0) habsPos.ne')
        (Real.sqrt_pos.2 hscalePos).ne',
      Real.log_mul (by norm_num : (1024 : ℝ) ≠ 0) habsPos.ne',
      Real.log_sqrt hscalePos.le]
  have hshiftLog :=
    main3LargeAnalytic_log_abs_shift_le_two_mul_log htheta hY hi
  have hDLog :=
    main3LargeAnalytic_log_source_dyadic_le_eight_mul_theta_mul_log
      htheta hY hi
  have hlog1024 : Real.log 1024 ≤ Real.log (Y : ℝ) :=
    Real.log_le_log (by norm_num) (by
      exact_mod_cast (show 1024 ≤ Y by omega))
  have hlog64 : Real.log 64 ≤ Real.log (Y : ℝ) :=
    Real.log_le_log (by norm_num) (by
      exact_mod_cast (show 64 ≤ Y by omega))
  have hlogYNonneg : 0 ≤ Real.log (Y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ Y by omega))
  have hcoarse :
      Real.log (main3LargeAnalyticFixedKeySourceCoordinateRadius
          (shiftedSquareA h v) D key) ≤
        4 * theta * Real.log (Y : ℝ) +
          4 * Real.log (Y : ℝ) := by
    rw [hradiusLog]
    linarith
  have hconstant :
      4 * Real.log (Y : ℝ) ≤
        2 * theta * Real.log (Y : ℝ) := by
    have hfour : (4 : ℝ) ≤ 2 * theta := by linarith
    exact mul_le_mul_of_nonneg_right hfour hlogYNonneg
  linarith

/-- On a nonempty literal target fibre, the fixed-key target-coordinate
radius has logarithmic size at most `2 * theta * log Y`. -/
theorem log_main3LargeAnalyticFixedKeyTargetCoordinateRadius_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    (p₀ : {p // p ∈ main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y}) :
    Real.log (main3LargeAnalyticFixedKeyTargetCoordinateRadius
      (shiftedSquareA h v) Y key) ≤
        2 * theta * Real.log (Y : ℝ) := by
  have ha : shiftedSquareA h v ≠ 0 :=
    main3LargeAnalytic_shift_ne_zero_of_largeAnalyticIndex hi
  have haReal : (shiftedSquareA h v : ℝ) ≠ 0 := by exact_mod_cast ha
  have habsPos : 0 < |(shiftedSquareA h v : ℝ)| := abs_pos.mpr haReal
  have hkey := main3LargeAnalytic_targetFibrePoint_key_scale_package
    htheta hY hi key cell y p₀
  have hscaleLog :=
    log_main3LargeAnalyticFixedKeyTargetScaleUpper_le_of_ne_zero
      (by omega : 0 < Y) ha hkey.1 hkey.2.1 hkey.2.2.2
  have hscalePos :
      0 < main3LargeAnalyticFixedKeyTargetScaleUpper Y key := by
    unfold main3LargeAnalyticFixedKeyTargetScaleUpper
    exact div_pos
      (mul_pos (mul_pos (by norm_num) (by positivity))
        (pow_pos hkey.1 2))
      (pow_pos (zero_lt_one.trans_le hkey.2.2.2) 2)
  have hradiusLog :
      Real.log (main3LargeAnalyticFixedKeyTargetCoordinateRadius
          (shiftedSquareA h v) Y key) =
        Real.log 1024 + Real.log |(shiftedSquareA h v : ℝ)| +
          Real.log (main3LargeAnalyticFixedKeyTargetScaleUpper Y key) / 2 := by
    unfold main3LargeAnalyticFixedKeyTargetCoordinateRadius
      shiftedSquareRawCoordinateScaleLoss
    rw [Real.log_mul
        (mul_ne_zero (by norm_num : (1024 : ℝ) ≠ 0) habsPos.ne')
        (Real.sqrt_pos.2 hscalePos).ne',
      Real.log_mul (by norm_num : (1024 : ℝ) ≠ 0) habsPos.ne',
      Real.log_sqrt hscalePos.le]
  have hshiftLog :=
    main3LargeAnalytic_log_abs_shift_le_two_mul_log htheta hY hi
  have hlog1024 : Real.log 1024 ≤ Real.log (Y : ℝ) :=
    Real.log_le_log (by norm_num) (by
      exact_mod_cast (show 1024 ≤ Y by omega))
  have hlog2048 : Real.log 2048 ≤ Real.log (Y : ℝ) :=
    Real.log_le_log (by norm_num) (by
      exact_mod_cast (show 2048 ≤ Y by omega))
  have hlogYNonneg : 0 ≤ Real.log (Y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ Y by omega))
  have hcoarse :
      Real.log (main3LargeAnalyticFixedKeyTargetCoordinateRadius
          (shiftedSquareA h v) Y key) ≤
        5 * Real.log (Y : ℝ) := by
    rw [hradiusLog]
    linarith
  have hconstant :
      5 * Real.log (Y : ℝ) ≤
        2 * theta * Real.log (Y : ℝ) := by
    have hfive : (5 : ℝ) ≤ 2 * theta := by linarith
    exact mul_le_mul_of_nonneg_right hfive hlogYNonneg
  exact hcoarse.trans hconstant

end

end PellPaper
