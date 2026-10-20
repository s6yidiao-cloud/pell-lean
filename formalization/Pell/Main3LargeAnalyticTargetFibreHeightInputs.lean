import Pell.Main3LargeAnalyticCommonFactorFiberReduction
import Pell.Main3LargeAnalyticFixedKeyCellCoordinateBounds

/-!
# Height inputs recovered from a nonempty literal target fibre

A point of the exact fixed-key, fixed-cell target fibre comes from one
retained encoding certificate.  This recovers both the normalization bounds
on the fixed auxiliary key and the common coordinate window for its literal
target vector.  These are elementary inputs to the later form-height ledger.
-/

namespace PellPaper

noncomputable section

/-- A nonempty target fibre recovers the normalization bounds carried by the
certificate that produced its fixed auxiliary key. -/
theorem main3LargeAnalytic_targetFibrePoint_key_scale_package
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    (p₀ : {p // p ∈ main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y}) :
    (0 : ℝ) < key.C₀ ∧
      (key.C₀ : ℝ) ≤ 32 * Real.sqrt |(shiftedSquareA h v : ℝ)| ∧
      (1 : ℝ) ≤ key.r ∧ (1 : ℝ) ≤ key.ell := by
  have hpImage :=
    (mem_main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y p₀.1).mp p₀.property |>.1
  rw [main3LargeAnalyticFixedKeyCellVectorImage] at hpImage
  obtain ⟨z, hz, _hzp⟩ := Finset.mem_map.mp hpImage
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  obtain ⟨p, hp, hkey, _hcell, _hgeometry, _hcode, _hzPoint⟩ :=
    main3LargeAnalytic_blockCellCoordinatePointImage_sameCertificate
      htheta hY hi hz
  let hY8 : 8 ≤ Y := by omega
  let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta hY8 hi p
  have hC0pos : 0 < C.P.minkowski.C₀ := C.P.minkowski.C₀_pos
  have hC0 := C.scaled.C₀_le_thirtytwo_mul_sqrt_abs
  have hr : 0 < C.P.r := C.P.r_pos
  have hell : 0 < C.P.ell := C.P.ell_pos
  rw [← hkey]
  exact ⟨by exact_mod_cast hC0pos, hC0,
    by exact_mod_cast hr, by exact_mod_cast hell⟩

/-- The fixed target vector of a nonempty literal fibre obeys the common
fixed-key target-coordinate radius. -/
theorem main3LargeAnalytic_targetFibrePoint_target_abs_bounds
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    (p₀ : {p // p ∈ main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y}) :
    |(y 0 : ℝ)| ≤
        main3LargeAnalyticFixedKeyTargetCoordinateRadius
          (shiftedSquareA h v) Y key ∧
      |(y 1 : ℝ)| ≤
        main3LargeAnalyticFixedKeyTargetCoordinateRadius
          (shiftedSquareA h v) Y key := by
  have hp :=
    (mem_main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y p₀.1).mp p₀.property
  have hpImage := hp.1
  rw [main3LargeAnalyticFixedKeyCellVectorImage] at hpImage
  obtain ⟨z, hz, hzp⟩ := Finset.mem_map.mp hpImage
  have hbounds :=
    main3LargeAnalytic_fixedKeyCellCoordinatePointImage_abs_bounds
      htheta hY hi hz
  change main3GeneralBidegreePointVectorEquiv z = p₀.1 at hzp
  rw [main3GeneralBidegreePointVectorEquiv_apply] at hzp
  have htarget : shiftedSquareCoordinatePointTargetVector z = y :=
    (congrArg Prod.snd hzp).trans hp.2
  have htarget0 := congrFun htarget 0
  have htarget1 := congrFun htarget 1
  change z.2.1 = y 0 at htarget0
  change z.2.2 = y 1 at htarget1
  rw [← htarget0, ← htarget1]
  exact hbounds.2

end

end PellPaper
