import Pell.Main3LargeAnalyticTargetFibreCoefficientBounds
import Pell.Main3LargeAnalyticTargetFibreRadiusLowerBounds
import Pell.Main3LargeAnalyticTargetFibreCoordinateLogBounds
import Mathlib.Tactic

/-!
# Logarithmic coefficient budget for a literal main3 target fibre

For a nonempty fixed-key target fibre, the explicit primitive-form
coefficient majorant is at least one and has logarithmic size at most
`3 * theta * log Y`.  The estimate uses only the already checked target
coordinate radius, the nonvanishing shifted-square parameter, and the
elementary comparison

`2 * (8 * |a| + 4) <= 24 * |a|`.
-/

namespace PellPaper

noncomputable section

/-- A nonempty literal target fibre makes the explicit primitive-surface
coefficient majorant at least one. -/
theorem
    one_le_main3LargeAnalyticFixedTargetPrimitiveSurfaceCoefficientMajorant_of_targetFibrePoint
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    (p₀ : Main3LargeAnalyticFixedKeyCellTargetFibrePoint
      htheta hY hi key cell y) :
    (1 : ℝ) ≤
      main3LargeAnalyticFixedTargetPrimitiveSurfaceCoefficientMajorant
        h v Y key := by
  have hT :=
    one_le_main3LargeAnalyticFixedKeyTargetCoordinateRadius_of_targetFibrePoint
      htheta hY hi key cell y p₀
  have hM :
      (1 : ℝ) ≤ ((8 * (shiftedSquareA h v).natAbs + 4 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 8 * (shiftedSquareA h v).natAbs + 4 by omega)
  unfold main3LargeAnalyticFixedTargetPrimitiveSurfaceCoefficientMajorant
  calc
    (1 : ℝ) ≤ 2 * 1 * 1 := by norm_num
    _ ≤ 2 * ((8 * (shiftedSquareA h v).natAbs + 4 : ℕ) : ℝ) *
        main3LargeAnalyticFixedKeyTargetCoordinateRadius
          (shiftedSquareA h v) Y key := by gcongr

/-- On a nonempty literal target fibre, the explicit primitive-surface
coefficient majorant has logarithmic size at most `3 * theta * log Y`. -/
theorem
    log_main3LargeAnalyticFixedTargetPrimitiveSurfaceCoefficientMajorant_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    (p₀ : Main3LargeAnalyticFixedKeyCellTargetFibrePoint
      htheta hY hi key cell y) :
    Real.log
        (main3LargeAnalyticFixedTargetPrimitiveSurfaceCoefficientMajorant
          h v Y key) ≤
      3 * theta * Real.log (Y : ℝ) := by
  let a := shiftedSquareA h v
  let T := main3LargeAnalyticFixedKeyTargetCoordinateRadius a Y key
  have ha : a ≠ 0 := by
    exact main3LargeAnalytic_shift_ne_zero_of_largeAnalyticIndex hi
  have hnPosNat : 0 < a.natAbs := Int.natAbs_pos.mpr ha
  have hnPos : (0 : ℝ) < (a.natAbs : ℝ) := by exact_mod_cast hnPosNat
  have hTOne : (1 : ℝ) ≤ T := by
    dsimp only [T, a]
    exact
      one_le_main3LargeAnalyticFixedKeyTargetCoordinateRadius_of_targetFibrePoint
        htheta hY hi key cell y p₀
  have hTPos : 0 < T := zero_lt_one.trans_le hTOne
  have hfactorNat :
      2 * (8 * a.natAbs + 4) ≤ 24 * a.natAbs := by omega
  have hfactor :
      (2 : ℝ) * ((8 * a.natAbs + 4 : ℕ) : ℝ) ≤
        24 * (a.natAbs : ℝ) := by
    exact_mod_cast hfactorNat
  have hmajorantPos :
      0 < main3LargeAnalyticFixedTargetPrimitiveSurfaceCoefficientMajorant
        h v Y key := by
    unfold main3LargeAnalyticFixedTargetPrimitiveSurfaceCoefficientMajorant
    dsimp only [a] at hnPos ⊢
    positivity
  have hmajorantLe :
      main3LargeAnalyticFixedTargetPrimitiveSurfaceCoefficientMajorant
          h v Y key ≤
        24 * (a.natAbs : ℝ) * T := by
    unfold main3LargeAnalyticFixedTargetPrimitiveSurfaceCoefficientMajorant
    dsimp only [a, T] at hfactor hTPos ⊢
    exact mul_le_mul_of_nonneg_right hfactor hTPos.le
  have hlogMajorant := Real.log_le_log hmajorantPos hmajorantLe
  have hlogProduct :
      Real.log (24 * (a.natAbs : ℝ) * T) =
        Real.log 24 + Real.log (a.natAbs : ℝ) + Real.log T := by
    rw [Real.log_mul
        (mul_ne_zero (by norm_num : (24 : ℝ) ≠ 0) hnPos.ne') hTPos.ne',
      Real.log_mul (by norm_num : (24 : ℝ) ≠ 0) hnPos.ne']
  rw [hlogProduct] at hlogMajorant
  have hlogShift :
      Real.log (a.natAbs : ℝ) ≤ 2 * Real.log (Y : ℝ) := by
    dsimp only [a]
    simpa only [Nat.cast_natAbs, Int.cast_abs] using
      (main3LargeAnalytic_log_abs_shift_le_two_mul_log htheta hY hi)
  have hlogTarget : Real.log T ≤ 2 * theta * Real.log (Y : ℝ) := by
    dsimp only [T, a]
    exact log_main3LargeAnalyticFixedKeyTargetCoordinateRadius_le
      htheta hY hi key cell y p₀
  have hlog24 : Real.log 24 ≤ Real.log (Y : ℝ) :=
    Real.log_le_log (by norm_num) (by
      exact_mod_cast (show 24 ≤ Y by omega))
  have hlogYNonneg : 0 ≤ Real.log (Y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ Y by omega))
  have hthree :
      3 * Real.log (Y : ℝ) ≤ theta * Real.log (Y : ℝ) :=
    mul_le_mul_of_nonneg_right htheta hlogYNonneg
  linarith

end

end PellPaper
