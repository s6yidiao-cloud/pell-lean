import Pell.Main3LargeAnalyticComplexRadialDiscriminantCost
import Pell.TwoLayerFullMinorHadamardHeight
import Pell.IntegerSymmetricRectangle
import Mathlib.Tactic

/-!
# Uniform raw-coordinate bounds on a main3 fixed-key cell image

Every point in one fixed auxiliary-key/archimedean-cell image retains the
same normalized package that produced its integral coordinates.  The dyadic
source and target bounds therefore give common real radii for all four raw
coordinates.  Taking integer floors produces the literal nonnegative
coordinate bounds consumed by the Hadamard kernel theorem.

The final result turns vanishing of all full bidegree-`(1,B)` minors into one
bounded nonzero integral two-layer form on the image.  No determinant-rate,
factorization, surface intersection, or point-count estimate is asserted.
-/

namespace PellPaper

noncomputable section

/-- Common source-coordinate radius on a fixed auxiliary-key fibre. -/
def main3LargeAnalyticFixedKeySourceCoordinateRadius
    (a : ℤ) (D : ℕ) (key : ShiftedSquareAuxiliaryKey) : ℝ :=
  shiftedSquareRawCoordinateScaleLoss a *
    Real.sqrt (main3LargeAnalyticFixedKeySourceScaleUpper D key)

/-- Common target-coordinate radius on a fixed auxiliary-key fibre. -/
def main3LargeAnalyticFixedKeyTargetCoordinateRadius
    (a : ℤ) (Y : ℕ) (key : ShiftedSquareAuxiliaryKey) : ℝ :=
  shiftedSquareRawCoordinateScaleLoss a *
    Real.sqrt (main3LargeAnalyticFixedKeyTargetScaleUpper Y key)

/-- Integral source bound obtained by flooring the common real radius. -/
def main3LargeAnalyticFixedKeySourceCoordinateBound
    (a : ℤ) (D : ℕ) (key : ShiftedSquareAuxiliaryKey) : ℤ :=
  ⌊main3LargeAnalyticFixedKeySourceCoordinateRadius a D key⌋

/-- Integral target bound obtained by flooring the common real radius. -/
def main3LargeAnalyticFixedKeyTargetCoordinateBound
    (a : ℤ) (Y : ℕ) (key : ShiftedSquareAuxiliaryKey) : ℤ :=
  ⌊main3LargeAnalyticFixedKeyTargetCoordinateRadius a Y key⌋

theorem main3LargeAnalyticFixedKeySourceCoordinateRadius_nonneg
    (a : ℤ) (D : ℕ) (key : ShiftedSquareAuxiliaryKey) :
    0 ≤ main3LargeAnalyticFixedKeySourceCoordinateRadius a D key := by
  unfold main3LargeAnalyticFixedKeySourceCoordinateRadius
  exact mul_nonneg (by
    unfold shiftedSquareRawCoordinateScaleLoss
    positivity) (Real.sqrt_nonneg _)

theorem main3LargeAnalyticFixedKeyTargetCoordinateRadius_nonneg
    (a : ℤ) (Y : ℕ) (key : ShiftedSquareAuxiliaryKey) :
    0 ≤ main3LargeAnalyticFixedKeyTargetCoordinateRadius a Y key := by
  unfold main3LargeAnalyticFixedKeyTargetCoordinateRadius
  exact mul_nonneg (by
    unfold shiftedSquareRawCoordinateScaleLoss
    positivity) (Real.sqrt_nonneg _)

theorem main3LargeAnalyticFixedKeySourceCoordinateBound_nonneg
    (a : ℤ) (D : ℕ) (key : ShiftedSquareAuxiliaryKey) :
    0 ≤ main3LargeAnalyticFixedKeySourceCoordinateBound a D key := by
  exact Int.floor_nonneg.mpr
    (main3LargeAnalyticFixedKeySourceCoordinateRadius_nonneg a D key)

theorem main3LargeAnalyticFixedKeyTargetCoordinateBound_nonneg
    (a : ℤ) (Y : ℕ) (key : ShiftedSquareAuxiliaryKey) :
    0 ≤ main3LargeAnalyticFixedKeyTargetCoordinateBound a Y key := by
  exact Int.floor_nonneg.mpr
    (main3LargeAnalyticFixedKeyTargetCoordinateRadius_nonneg a Y key)

/-- Every point in a fixed key-and-cell image obeys the same four real
raw-coordinate bounds.  The proof uses one retained certificate throughout. -/
theorem main3LargeAnalytic_fixedKeyCellCoordinatePointImage_abs_bounds
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    {key : ShiftedSquareAuxiliaryKey}
    {cell : Main3LargeAnalyticArchimedeanCellIndex}
    {z : GeneralBidegreeFormPoint}
    (hz : z ∈
      main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key cell) :
    (|(z.1.1 : ℝ)| ≤
        main3LargeAnalyticFixedKeySourceCoordinateRadius
          (shiftedSquareA h v) D key ∧
      |(z.1.2 : ℝ)| ≤
        main3LargeAnalyticFixedKeySourceCoordinateRadius
          (shiftedSquareA h v) D key) ∧
    (|(z.2.1 : ℝ)| ≤
        main3LargeAnalyticFixedKeyTargetCoordinateRadius
          (shiftedSquareA h v) Y key ∧
      |(z.2.2 : ℝ)| ≤
        main3LargeAnalyticFixedKeyTargetCoordinateRadius
          (shiftedSquareA h v) Y key) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let hY8 : 8 ≤ Y := by omega
  obtain ⟨p, hp, hkey, _hcell, _hgeometry, _hcode, hzPoint⟩ :=
    main3LargeAnalytic_blockCellCoordinatePointImage_sameCertificate
      htheta hY hi hz
  let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta hY8 hi p
  have hraw := shiftedSquare_primitiveRawCoordinates_scaleBounds
    (main3LargeAnalytic_shift_squarefree hi)
    C.scaled.base.source_pos C.scaled.base.shift_dominance C.P
  have hsource := shiftedSquareEAlpha_le_fixedKeySourceScaleUpper
    C.scaled.base.source_dyadic.2 C.P
  have htarget := shiftedSquareEGamma_le_fixedKeyTargetScaleUpper
    C.scaled.base.target_dyadic.2 C.P
  have hloss : 0 ≤ shiftedSquareRawCoordinateScaleLoss
      (shiftedSquareA h v) := by
    unfold shiftedSquareRawCoordinateScaleLoss
    positivity
  have hsourceSqrt : Real.sqrt (shiftedSquareEAlpha C.P) ≤
      Real.sqrt (main3LargeAnalyticFixedKeySourceScaleUpper D
        ⟨C.P.minkowski.C₀, C.P.r, C.P.ell, C.P.bζ⟩) :=
    Real.sqrt_le_sqrt hsource
  have htargetSqrt : Real.sqrt (shiftedSquareEGamma C.P) ≤
      Real.sqrt (main3LargeAnalyticFixedKeyTargetScaleUpper Y
        ⟨C.P.minkowski.C₀, C.P.r, C.P.ell, C.P.bζ⟩) :=
    Real.sqrt_le_sqrt htarget
  have hsourceMul := mul_le_mul_of_nonneg_left hsourceSqrt hloss
  have htargetMul := mul_le_mul_of_nonneg_left htargetSqrt hloss
  rw [hzPoint, ← hkey]
  unfold main3LargeAnalyticFixedKeySourceCoordinateRadius
    main3LargeAnalyticFixedKeyTargetCoordinateRadius
  exact ⟨⟨hraw.1.1.trans hsourceMul, hraw.1.2.trans hsourceMul⟩,
    ⟨hraw.2.1.trans htargetMul, hraw.2.2.trans htargetMul⟩⟩

/-- The preceding real inequalities give the exact integer bounds required
by the general-bidegree and two-layer evaluation APIs. -/
theorem main3LargeAnalytic_fixedKeyCellCoordinatePointImage_coordinatesBounded
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    {key : ShiftedSquareAuxiliaryKey}
    {cell : Main3LargeAnalyticArchimedeanCellIndex}
    {z : GeneralBidegreeFormPoint}
    (hz : z ∈
      main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key cell) :
    generalBidegreeFormPointCoordinatesBounded
      (main3LargeAnalyticFixedKeySourceCoordinateBound
        (shiftedSquareA h v) D key)
      (main3LargeAnalyticFixedKeyTargetCoordinateBound
        (shiftedSquareA h v) Y key) z := by
  have hbounds :=
    main3LargeAnalytic_fixedKeyCellCoordinatePointImage_abs_bounds
      htheta hY hi hz
  unfold generalBidegreeFormPointCoordinatesBounded
    main3LargeAnalyticFixedKeySourceCoordinateBound
    main3LargeAnalyticFixedKeyTargetCoordinateBound
  constructor
  · exact Int.le_floor.mpr (by simpa using hbounds.1.1)
  constructor
  · exact Int.le_floor.mpr (by simpa using hbounds.1.2)
  constructor
  · exact Int.le_floor.mpr (by simpa using hbounds.2.1)
  · exact Int.le_floor.mpr (by simpa using hbounds.2.2)

/-- Full integral-minor vanishing on a fixed key-and-cell image yields one
bounded nonzero integral two-layer form vanishing on every image point. -/
theorem
    exists_nonzero_bounded_integral_twoLayerForm_on_main3LargeAnalytic_fixedKeyCellImage
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (hminor : ∀ s : generalBidegreeFormIndex 1 B ↪
        {z // z ∈
          main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
            htheta hY hi key cell},
      ((generalBidegreeFormEvaluationMatrix 1 B
        (fun z : {z // z ∈
          main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
            htheta hY hi key cell} => z.1)).submatrix s id).det = 0) :
    ∃ r : ℕ, r < 2 * (B + 1) ∧
      ∃ f : twoLayerFormIndex B → ℤ, f ≠ 0 ∧
        (∀ z ∈
          main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
            htheta hY hi key cell,
          twoLayerFormEval B f z = 0) ∧
        ∀ j, (|f j| : ℝ) ≤
          (√(r : ℝ) *
            (((main3LargeAnalyticFixedKeySourceCoordinateBound
                (shiftedSquareA h v) D key) *
              (main3LargeAnalyticFixedKeyTargetCoordinateBound
                (shiftedSquareA h v) Y key) ^ B : ℤ) : ℝ)) ^ r := by
  obtain ⟨r, hr, f, hf0, hfvanish, hfbound⟩ :=
    exists_nonzero_real_bounded_integral_generalBidegreeForm_of_forall_fullIntegralEvaluationMinors_eq_zero_hadamard_separateBounds
      1 B
      (fun z : {z // z ∈
        main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
          htheta hY hi key cell} => z.1)
      hminor
      (main3LargeAnalyticFixedKeySourceCoordinateBound_nonneg
        (shiftedSquareA h v) D key)
      (main3LargeAnalyticFixedKeyTargetCoordinateBound_nonneg
        (shiftedSquareA h v) Y key)
      (fun z =>
        main3LargeAnalytic_fixedKeyCellCoordinatePointImage_coordinatesBounded
          htheta hY hi z.2)
  refine ⟨r, by simpa using hr, f, hf0, ?_, ?_⟩
  · intro z hz
    have hz' := hfvanish
      (⟨z, hz⟩ : {z // z ∈
        main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
          htheta hY hi key cell})
    rw [generalBidegreeFormEval_one_eq_twoLayerFormEval] at hz'
    exact hz'
  · intro j
    simpa only [pow_one] using hfbound j

end

end PellPaper
