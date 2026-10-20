import Pell.Main3LargeAnalyticFixedKeyCellIntrinsicArithmetic
import Pell.Main3LargeAnalyticCommonFactorRealCount
import Pell.Main3LargeAnalyticCellCoordinatePointImage
import Mathlib.Tactic

/-!
# Fixed-cell common/residual real-count composition

This candidate casts the exact intrinsic fixed-key/fixed-cell arithmetic split
to `ℝ`, inserts the proved common-factor-zero estimate, and leaves the exact
cell-conditioned residual square-filter estimate as a supplied real bound.
The final statement is transferred back from the coordinate image to the
literal key-and-cell point fibre.

No residual geometry, square-sieve estimate, or Weil input is asserted here.
-/

namespace PellPaper

noncomputable section

/-- A supplied real bound for the exact cell-conditioned residual square
filter combines with the proved common-factor estimate to bound the literal
fixed-key/fixed-cell point fibre. -/
theorem card_main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_cast_le_commonFactor_add_twice_intrinsicResidual
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B)
    (R : ℝ)
    (hresidual :
      (((main3LargeAnalyticFixedKeyCellTargetVectorImage
        htheta hY hi key cell).filter fun y =>
          IsSquare (MvPolynomial.eval y
            (twoLayerEliminant data.residualDegree data.residualForm
              (main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi)
              (shiftedSquareAuxiliaryKeySurfaceLevel key))) ∧
          MvPolynomial.eval y
            (twoLayerEliminant data.residualDegree data.residualForm
              (main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi)
              (shiftedSquareAuxiliaryKeySurfaceLevel key)) ≠ 0).card : ℝ) ≤ R) :
    ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
        htheta hY hi key cell).card : ℝ) ≤
      2048 * (B : ℝ) * theta *
          ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) +
        2 * R := by
  have hsplitNat :=
    card_main3LargeAnalytic_fixedKeyCellImage_le_factorZeros_add_intrinsicResidualSquares
      htheta hY hi key cell data
  have hsplitReal :
      ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
          htheta hY hi key cell).card : ℝ) ≤
        (((main3LargeAnalyticFixedKeyCellVectorImage
          htheta hY hi key cell).filter fun p =>
            MvPolynomial.eval p.2 data.targetFactor = 0).card : ℝ) +
        2 * (((main3LargeAnalyticFixedKeyCellTargetVectorImage
          htheta hY hi key cell).filter fun y =>
            IsSquare (MvPolynomial.eval y
              (twoLayerEliminant data.residualDegree data.residualForm
                (main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi)
                (shiftedSquareAuxiliaryKeySurfaceLevel key))) ∧
            MvPolynomial.eval y
              (twoLayerEliminant data.residualDegree data.residualForm
                (main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi)
                (shiftedSquareAuxiliaryKeySurfaceLevel key)) ≠ 0).card : ℝ) := by
    exact_mod_cast hsplitNat
  have hcommon :=
    card_main3LargeAnalytic_commonFactorZero_cast_le_2048_mul_degreeBudget_mul_theta_mul_key_divisors
      htheta hY hi key cell data
  calc
    ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
        htheta hY hi key cell).card : ℝ) =
        ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
          htheta hY hi key cell).card : ℝ) := by
      exact_mod_cast
        (card_main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage_eq
          htheta hY hi key cell).symm
    _ ≤
        (((main3LargeAnalyticFixedKeyCellVectorImage
          htheta hY hi key cell).filter fun p =>
            MvPolynomial.eval p.2 data.targetFactor = 0).card : ℝ) +
        2 * (((main3LargeAnalyticFixedKeyCellTargetVectorImage
          htheta hY hi key cell).filter fun y =>
            IsSquare (MvPolynomial.eval y
              (twoLayerEliminant data.residualDegree data.residualForm
                (main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi)
                (shiftedSquareAuxiliaryKeySurfaceLevel key))) ∧
            MvPolynomial.eval y
              (twoLayerEliminant data.residualDegree data.residualForm
                (main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi)
                (shiftedSquareAuxiliaryKeySurfaceLevel key)) ≠ 0).card : ℝ) :=
      hsplitReal
    _ ≤
        2048 * (B : ℝ) * theta *
            ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) +
          2 * R := by
      exact add_le_add hcommon
        (mul_le_mul_of_nonneg_left hresidual (by norm_num))

end

end PellPaper
