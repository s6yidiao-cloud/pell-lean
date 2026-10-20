import Pell.Main3LargeAnalyticFixedKeyCellArithmetic

/-!
# Intrinsic arithmetic split on one fixed key and cell

The original fixed-cell arithmetic split placed every target vector in a
coarse symmetric rectangle.  Here the same generic surface-projection theorem
is applied with the exact target projection of the fixed key-and-cell image.
Thus the residual eliminant-square term retains the cell-conditioned target
geometry, while the common-factor-zero branch and the factor `2` are
unchanged.
-/

namespace PellPaper

noncomputable section

/-- The exact target-vector projection of one fixed-key, fixed-cell vector
image. -/
def main3LargeAnalyticFixedKeyCellTargetVectorImage
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex) :
    Finset (Fin 2 → ℤ) :=
  (main3LargeAnalyticFixedKeyCellVectorImage
    htheta hY hi key cell).image Prod.snd

/-- The factor-zero plus eliminant-square split with the residual term
restricted to the actual target image of the fixed key and cell. -/
theorem card_main3LargeAnalytic_fixedKeyCellImage_le_factorZeros_add_intrinsicResidualSquares
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B) :
    (main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key cell).card ≤
      ((main3LargeAnalyticFixedKeyCellVectorImage htheta hY hi key cell).filter
        fun p => MvPolynomial.eval p.2 data.targetFactor = 0).card +
      2 * ((main3LargeAnalyticFixedKeyCellTargetVectorImage
        htheta hY hi key cell).filter fun y =>
          IsSquare (MvPolynomial.eval y
            (twoLayerEliminant data.residualDegree data.residualForm
              (main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi)
              (shiftedSquareAuxiliaryKeySurfaceLevel key))) ∧
          MvPolynomial.eval y
            (twoLayerEliminant data.residualDegree data.residualForm
              (main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi)
              (shiftedSquareAuxiliaryKeySurfaceLevel key)) ≠ 0).card := by
  rw [← card_main3LargeAnalyticFixedKeyCellVectorImage htheta hY hi key cell]
  apply card_shiftedSquareCoordinateSurface_le_targetFactorZeros_add_twiceSquares
    B data.residualDegree data.form data.residualForm data.targetFactor
    data.factorization data.residual_components_nonvanishing
    (main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi)
    (shiftedSquareAuxiliaryKeySurfaceLevel key) data.surfaceLevel_ne_zero
    (main3LargeAnalyticFixedKeyCellVectorImage htheta hY hi key cell)
    (main3LargeAnalyticFixedKeyCellTargetVectorImage
      htheta hY hi key cell)
  · intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hp
    exact (main3LargeAnalytic_blockCellCoordinatePointImage_primitive
      htheta hY hi hz).1
  · intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hp
    exact (main3LargeAnalytic_blockCellCoordinatePointImage_primitive
      htheta hY hi hz).2
  · intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hp
    have heq : main3GeneralBidegreePointVectorEquiv.toEmbedding z =
        (shiftedSquareCoordinatePointSourceVector z,
          shiftedSquareCoordinatePointTargetVector z) :=
      main3GeneralBidegreePointVectorEquiv_apply z
    rw [heq]
    simpa only [
      shiftedSquareCoordinatePoint,
      shiftedSquareCoordinatePointSourceVector,
      shiftedSquareCoordinatePointTargetVector,
      Matrix.cons_val_zero, Matrix.cons_val_one] using data.form_vanish z hz
  · intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hp
    exact (main3LargeAnalytic_blockCellCoordinatePointImage_surfaceData
      htheta hY hi hz).1
  · intro p hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

end

end PellPaper
