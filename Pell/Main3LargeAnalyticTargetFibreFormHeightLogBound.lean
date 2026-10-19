import Pell.Main3LargeAnalyticTargetFibreCoefficientLogBound
import Pell.QuadraticFormRealHeightMajorantBound
import Mathlib.Tactic

/-!
# Logarithmic form-vector height budget for a literal main3 target fibre

The coefficient majorant of the primitive fixed-target surface form and the
literal source-coordinate radius are both at least one.  Their checked
logarithmic bounds, together with the generic estimate `H ≤ 6 K X`, give the
coarse numerator-height budget

`log H ≤ 21 * theta * log Y`.

The constant is intentionally rounded to match the subsequent reciprocal
height-window capacity lemma.
-/

namespace PellPaper

noncomputable section

/-- For a point of a literal main3 target fibre, the exact real-height
majorant used by the same-ideal unit-orbit count has logarithm at most
`21 * theta * log Y`. -/
theorem log_main3LargeAnalyticFixedTargetFormIdealVectorRealHeightMajorant_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    (p₀ : Main3LargeAnalyticFixedKeyCellTargetFibrePoint
      htheta hY hi key cell y)
    (w s : ℕ)
    (hdisc :
      (main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y).discriminant =
        ((w * s ^ 2 : ℕ) : ℤ)) :
    Real.log
        (IntegralBinaryQuadraticForm.formIdealVectorRealHeightMajorant
          ((w * s ^ 2 : ℕ) : ℤ)
          (main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y)
          (main3LargeAnalyticFixedKeySourceCoordinateRadius
            (shiftedSquareA h v) D key)) ≤
      21 * theta * Real.log (Y : ℝ) := by
  let Q := main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y
  let K := main3LargeAnalyticFixedTargetPrimitiveSurfaceCoefficientMajorant
    h v Y key
  let X := main3LargeAnalyticFixedKeySourceCoordinateRadius
    (shiftedSquareA h v) D key
  have hK : (1 : ℝ) ≤ K := by
    dsimp only [K]
    exact
      one_le_main3LargeAnalyticFixedTargetPrimitiveSurfaceCoefficientMajorant_of_targetFibrePoint
        htheta hY hi key cell y p₀
  have hX : (1 : ℝ) ≤ X := by
    dsimp only [X]
    exact
      one_le_main3LargeAnalyticFixedKeySourceCoordinateRadius_of_targetFibrePoint
        htheta hY hi key cell y p₀
  have hcoeff :=
    main3LargeAnalytic_fixedTargetPrimitiveSurfaceForm_coefficients_abs_le
      htheta hY hi key cell y p₀
  change |(Q.a : ℝ)| ≤ K ∧ |(Q.b : ℝ)| ≤ K ∧ |(Q.c : ℝ)| ≤ K at hcoeff
  have hheight :
      Real.log
          (IntegralBinaryQuadraticForm.formIdealVectorRealHeightMajorant
            ((w * s ^ 2 : ℕ) : ℤ) Q X) ≤
        Real.log 6 + Real.log K + Real.log X :=
    IntegralBinaryQuadraticForm.log_formIdealVectorRealHeightMajorant_le_log_six_add
      ((w * s ^ 2 : ℕ) : ℤ) (by positivity) Q hdisc hK hX
        hcoeff.1 hcoeff.2.1 hcoeff.2.2
  have hlogK : Real.log K ≤ 3 * theta * Real.log (Y : ℝ) := by
    dsimp only [K]
    exact
      log_main3LargeAnalyticFixedTargetPrimitiveSurfaceCoefficientMajorant_le
        htheta hY hi key cell y p₀
  have hlogX : Real.log X ≤ 6 * theta * Real.log (Y : ℝ) := by
    dsimp only [X]
    exact log_main3LargeAnalyticFixedKeySourceCoordinateRadius_le
      htheta hY hi key cell y p₀
  have hlogSix : Real.log 6 ≤ Real.log (Y : ℝ) :=
    Real.log_le_log (by norm_num) (by
      exact_mod_cast (show 6 ≤ Y by omega))
  have hlogYNonneg : 0 ≤ Real.log (Y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ Y by omega))
  have hlogYLeThetaLogY :
      Real.log (Y : ℝ) ≤ theta * Real.log (Y : ℝ) := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right
        (show (1 : ℝ) ≤ theta by linarith) hlogYNonneg
  have hthetaLogYNonneg :
      0 ≤ theta * Real.log (Y : ℝ) := by positivity
  change
    Real.log
        (IntegralBinaryQuadraticForm.formIdealVectorRealHeightMajorant
          ((w * s ^ 2 : ℕ) : ℤ) Q X) ≤
      21 * theta * Real.log (Y : ℝ)
  linarith

end

end PellPaper
