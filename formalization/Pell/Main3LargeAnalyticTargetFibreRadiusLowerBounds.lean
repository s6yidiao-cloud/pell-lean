import Pell.Main3LargeAnalyticTargetFibreUnitHeightCount
import Pell.Main3LargeAnalyticTargetFibreHeightInputs
import Pell.Main3LargeAnalyticTargetFibreSurfaceForm

/-!
# Lower bounds for literal target-fibre coordinate radii

The source and target vectors in a retained target fibre are primitive.
Consequently each has a nonzero integral coordinate, whose absolute value is
at least one.  The checked coordinate windows therefore have radii at least
one.  This elementary observation will absorb additive constants in the
form-vector height ledger.
-/

namespace PellPaper

noncomputable section

/-- A nonempty literal target fibre has source-coordinate radius at least
one. -/
theorem one_le_main3LargeAnalyticFixedKeySourceCoordinateRadius_of_targetFibrePoint
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    (p₀ : Main3LargeAnalyticFixedKeyCellTargetFibrePoint
      htheta hY hi key cell y) :
    (1 : ℝ) ≤ main3LargeAnalyticFixedKeySourceCoordinateRadius
      (shiftedSquareA h v) D key := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let B := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  have hsurface := main3LargeAnalytic_targetFibre_primitive_surfaceForm
    htheta hY hi key cell y p₀.property
  change IsCoprime (p₀.1.1 0) (p₀.1.1 1) ∧
      IsCoprime (y 0) (y 1) ∧
        (shiftedSquareSurfaceForm B.t B.c y).eval
            (p₀.1.1 0) (p₀.1.1 1) =
          shiftedSquareAuxiliaryKeySurfaceLevel key ∧
        shiftedSquareAuxiliaryKeySurfaceLevel key ≠ 0 at hsurface
  have hp₀pair : (p₀.1.1 0, p₀.1.1 1) ∈
      main3LargeAnalyticFixedKeyCellTargetFibreSourcePairs
        htheta hY hi key cell y := by
    rw [main3LargeAnalyticFixedKeyCellTargetFibreSourcePairs]
    exact Finset.mem_image.mpr ⟨p₀.1, p₀.property, rfl⟩
  have hbounds := main3LargeAnalytic_targetFibreSourcePair_abs_bounds
    htheta hY hi key cell y hp₀pair
  rcases hsurface.1.ne_zero_or_ne_zero with hzero | hone
  · have hcoord : (1 : ℝ) ≤ |(p₀.1.1 0 : ℝ)| := by
      exact_mod_cast Int.one_le_abs hzero
    exact hcoord.trans hbounds.1
  · have hcoord : (1 : ℝ) ≤ |(p₀.1.1 1 : ℝ)| := by
      exact_mod_cast Int.one_le_abs hone
    exact hcoord.trans hbounds.2

/-- A nonempty literal target fibre has target-coordinate radius at least
one. -/
theorem one_le_main3LargeAnalyticFixedKeyTargetCoordinateRadius_of_targetFibrePoint
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    (p₀ : Main3LargeAnalyticFixedKeyCellTargetFibrePoint
      htheta hY hi key cell y) :
    (1 : ℝ) ≤ main3LargeAnalyticFixedKeyTargetCoordinateRadius
      (shiftedSquareA h v) Y key := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let B := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  have hsurface := main3LargeAnalytic_targetFibre_primitive_surfaceForm
    htheta hY hi key cell y p₀.property
  change IsCoprime (p₀.1.1 0) (p₀.1.1 1) ∧
      IsCoprime (y 0) (y 1) ∧
        (shiftedSquareSurfaceForm B.t B.c y).eval
            (p₀.1.1 0) (p₀.1.1 1) =
          shiftedSquareAuxiliaryKeySurfaceLevel key ∧
        shiftedSquareAuxiliaryKeySurfaceLevel key ≠ 0 at hsurface
  have hbounds := main3LargeAnalytic_targetFibrePoint_target_abs_bounds
    htheta hY hi key cell y p₀
  rcases hsurface.2.1.ne_zero_or_ne_zero with hzero | hone
  · have hcoord : (1 : ℝ) ≤ |(y 0 : ℝ)| := by
      exact_mod_cast Int.one_le_abs hzero
    exact hcoord.trans hbounds.1
  · have hcoord : (1 : ℝ) ≤ |(y 1 : ℝ)| := by
      exact_mod_cast Int.one_le_abs hone
    exact hcoord.trans hbounds.2

end

end PellPaper
