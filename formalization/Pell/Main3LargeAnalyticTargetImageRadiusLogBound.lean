import Pell.Main3LargeAnalyticFixedKeyCellTargetRadialGeometry
import Pell.Main3LargeAnalyticTargetFibreCoordinateLogBounds

/-!
# Theta-free logarithmic target-radius bound from a nonempty cell image

The target-fibre height proof already derives the sharper intermediate bound
`log T₀ ≤ 5 log Y`, but its public endpoint weakens this to a multiple of
`theta`.  Matrix-height bookkeeping needs the sharper form.  This module
recovers the fixed-key scale data directly from one member of the exact target
image and exports that intermediate estimate.
-/

namespace PellPaper

noncomputable section

/-- One member of the exact fixed-key target image recovers all elementary
normalization bounds carried by the encoding certificate that produced it. -/
theorem main3LargeAnalytic_targetImagePoint_key_scale_package
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    {y : Fin 2 → ℤ}
    (hy : y ∈ main3LargeAnalyticFixedKeyCellTargetVectorImage
      htheta hY hi key cell) :
    (0 : ℝ) < key.C₀ ∧
      (key.C₀ : ℝ) ≤ 32 * Real.sqrt |(shiftedSquareA h v : ℝ)| ∧
      (1 : ℝ) ≤ key.r ∧ (1 : ℝ) ≤ key.ell := by
  obtain ⟨z, hz, _hyz⟩ :=
    (mem_main3LargeAnalyticFixedKeyCellTargetVectorImage_iff
      htheta hY hi key cell y).mp hy
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  obtain ⟨p, _hp, hkey, _hcell, _hgeometry, _hcode, _hzPoint⟩ :=
    main3LargeAnalytic_blockCellCoordinatePointImage_sameCertificate
      htheta hY hi hz
  let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta (by omega : 8 ≤ Y) hi p
  have hC₀pos : 0 < C.P.minkowski.C₀ := C.P.minkowski.C₀_pos
  have hC₀ := C.scaled.C₀_le_thirtytwo_mul_sqrt_abs
  have hr : 0 < C.P.r := C.P.r_pos
  have hell : 0 < C.P.ell := C.P.ell_pos
  rw [← hkey]
  exact ⟨by exact_mod_cast hC₀pos, hC₀,
    by exact_mod_cast hr, by exact_mod_cast hell⟩

/-- The exact raw target-coordinate radius of every nonempty fixed-key cell
has logarithmic height at most `5 log Y`, independently of `theta`. -/
theorem log_main3LargeAnalyticFixedKeyTargetCoordinateRadius_le_five_mul
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (hnonempty :
      (main3LargeAnalyticFixedKeyCellTargetVectorImage
        htheta hY hi key cell).Nonempty) :
    Real.log (main3LargeAnalyticFixedKeyTargetCoordinateRadius
      (shiftedSquareA h v) Y key) ≤ 5 * Real.log (Y : ℝ) := by
  obtain ⟨y, hy⟩ := hnonempty
  have ha : shiftedSquareA h v ≠ 0 :=
    main3LargeAnalytic_shift_ne_zero_of_largeAnalyticIndex hi
  have haReal : (shiftedSquareA h v : ℝ) ≠ 0 := by exact_mod_cast ha
  have habsPos : 0 < |(shiftedSquareA h v : ℝ)| := abs_pos.mpr haReal
  have hkey := main3LargeAnalytic_targetImagePoint_key_scale_package
    htheta hY hi key cell hy
  have hscaleLog :=
    log_main3LargeAnalyticFixedKeyTargetScaleUpper_le_of_ne_zero
      (by omega : 0 < Y) ha hkey.1 hkey.2.1 hkey.2.2.2
  have hscalePos :
      0 < main3LargeAnalyticFixedKeyTargetScaleUpper Y key :=
    main3LargeAnalyticFixedKeyTargetScaleUpper_pos_of_mem
      htheta hY hi key cell hy
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
  rw [hradiusLog]
  linarith

end

end PellPaper
