import Pell.Main3LargeAnalyticTargetFibreHeightInputs
import Pell.Main3LargeAnalyticPrimitiveFormPellReduction
import Mathlib.Tactic

/-!
# Coefficient height of a literal main3 target-fibre form

The fixed-target surface form is obtained by contracting the fixed block's
six raw surface coefficients against the two target coordinates.  A point in
the target fibre puts both target coordinates in the common fixed-key radius,
so the triangle inequality bounds each raw quadratic-form coefficient by
twice the raw coefficient height times that radius.  Positivity of the common
coefficient content then shows that passing to the primitive part cannot
increase any absolute coefficient.

No logarithmic estimate or regulator bound is asserted here.
-/

namespace PellPaper

noncomputable section

/-- A common real majorant for all three coefficients of the primitive
fixed-target surface form. -/
def main3LargeAnalyticFixedTargetPrimitiveSurfaceCoefficientMajorant
    (h : ℤ) (v Y : ℕ) (key : ShiftedSquareAuxiliaryKey) : ℝ :=
  2 * ((8 * (shiftedSquareA h v).natAbs + 4 : ℕ) : ℝ) *
    main3LargeAnalyticFixedKeyTargetCoordinateRadius
      (shiftedSquareA h v) Y key

/-- Contracting one row of the fixed raw surface tensor against a target in
the fixed-key coordinate window costs at most twice the tensor height times
the target radius. -/
private theorem main3LargeAnalytic_fixedTargetSurfaceTensorRow_abs_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (y : Fin 2 → ℤ)
    (hy : |(y 0 : ℝ)| ≤
          main3LargeAnalyticFixedKeyTargetCoordinateRadius
            (shiftedSquareA h v) Y key ∧
        |(y 1 : ℝ)| ≤
          main3LargeAnalyticFixedKeyTargetCoordinateRadius
            (shiftedSquareA h v) Y key)
    (i : Fin 3) :
    |((main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi i 0 * y 0 +
        main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi i 1 * y 1 :
          ℤ) : ℝ)| ≤
      main3LargeAnalyticFixedTargetPrimitiveSurfaceCoefficientMajorant
        h v Y key := by
  let M : ℝ := ((8 * (shiftedSquareA h v).natAbs + 4 : ℕ) : ℝ)
  let R : ℝ := main3LargeAnalyticFixedKeyTargetCoordinateRadius
    (shiftedSquareA h v) Y key
  have hM : 0 ≤ M := by positivity
  have hcoeff (j : Fin 2) :
      |(main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi i j : ℝ)| ≤
        M := by
    dsimp only [M]
    rw [← Int.cast_abs]
    have hcoeffInt :=
      main3LargeAnalytic_blockCoordinateSurfaceCoefficients_abs_le hi i j
    have hcoeffReal :
        ((|main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi i j| : ℤ) : ℝ) ≤
          ((((8 * (shiftedSquareA h v).natAbs + 4 : ℕ) : ℤ)) : ℝ) := by
      exact_mod_cast hcoeffInt
    simpa only [Int.cast_natCast] using hcoeffReal
  simp only [Int.cast_add, Int.cast_mul]
  change
    |(main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi i 0 : ℝ) *
          (y 0 : ℝ) +
        (main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi i 1 : ℝ) *
          (y 1 : ℝ)| ≤ 2 * M * R
  calc
    |(main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi i 0 : ℝ) *
          (y 0 : ℝ) +
        (main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi i 1 : ℝ) *
          (y 1 : ℝ)| ≤
        |(main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi i 0 : ℝ) *
          (y 0 : ℝ)| +
        |(main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi i 1 : ℝ) *
          (y 1 : ℝ)| := abs_add_le _ _
    _ =
        |(main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi i 0 : ℝ)| *
            |(y 0 : ℝ)| +
          |(main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi i 1 : ℝ)| *
            |(y 1 : ℝ)| := by rw [abs_mul, abs_mul]
    _ ≤ M * R + M * R := by
      exact add_le_add
        (mul_le_mul (hcoeff 0) hy.1 (abs_nonneg _) hM)
        (mul_le_mul (hcoeff 1) hy.2 (abs_nonneg _) hM)
    _ = 2 * M * R := by ring

/-- Before removing content, all three coefficients of the literal fixed
target surface form obey the common target-radius majorant. -/
theorem main3LargeAnalytic_fixedTargetSurfaceForm_coefficients_abs_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    (p₀ : Main3LargeAnalyticFixedKeyCellTargetFibrePoint
      htheta hY hi key cell y) :
    let S := main3LargeAnalyticFixedTargetSurfaceForm hi y
    |(S.a : ℝ)| ≤
        main3LargeAnalyticFixedTargetPrimitiveSurfaceCoefficientMajorant
          h v Y key ∧
      |(S.b : ℝ)| ≤
        main3LargeAnalyticFixedTargetPrimitiveSurfaceCoefficientMajorant
          h v Y key ∧
      |(S.c : ℝ)| ≤
        main3LargeAnalyticFixedTargetPrimitiveSurfaceCoefficientMajorant
          h v Y key := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let B := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  have hy := main3LargeAnalytic_targetFibrePoint_target_abs_bounds
    htheta hY hi key cell y p₀
  have hrow := main3LargeAnalytic_fixedTargetSurfaceTensorRow_abs_le
    hi key y hy
  change
    |((shiftedSquareSurfaceForm B.t B.c y).a : ℝ)| ≤
        main3LargeAnalyticFixedTargetPrimitiveSurfaceCoefficientMajorant
          h v Y key ∧
      |((shiftedSquareSurfaceForm B.t B.c y).b : ℝ)| ≤
        main3LargeAnalyticFixedTargetPrimitiveSurfaceCoefficientMajorant
          h v Y key ∧
      |((shiftedSquareSurfaceForm B.t B.c y).c : ℝ)| ≤
        main3LargeAnalyticFixedTargetPrimitiveSurfaceCoefficientMajorant
          h v Y key
  have hrow0 := hrow (0 : Fin 3)
  have hrow1 := hrow (1 : Fin 3)
  have hrow2 := hrow (2 : Fin 3)
  change
    |((shiftedSquareSurfaceCoefficients B.t B.c 0 0 * y 0 +
        shiftedSquareSurfaceCoefficients B.t B.c 0 1 * y 1 : ℤ) : ℝ)| ≤ _
      at hrow0
  change
    |((shiftedSquareSurfaceCoefficients B.t B.c 1 0 * y 0 +
        shiftedSquareSurfaceCoefficients B.t B.c 1 1 * y 1 : ℤ) : ℝ)| ≤ _
      at hrow1
  change
    |((shiftedSquareSurfaceCoefficients B.t B.c 2 0 * y 0 +
        shiftedSquareSurfaceCoefficients B.t B.c 2 1 * y 1 : ℤ) : ℝ)| ≤ _
      at hrow2
  simpa [shiftedSquareSurfaceForm, shiftedSquareSurfaceCoefficients] using
    And.intro hrow0 (And.intro hrow1 hrow2)

/-- Removing the positive common content cannot enlarge any coefficient.
Thus all three coefficients of the literal primitive surface form obey the
same explicit majorant as the raw form. -/
theorem main3LargeAnalytic_fixedTargetPrimitiveSurfaceForm_coefficients_abs_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    (p₀ : Main3LargeAnalyticFixedKeyCellTargetFibrePoint
      htheta hY hi key cell y) :
    let Q := main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y
    |(Q.a : ℝ)| ≤
        main3LargeAnalyticFixedTargetPrimitiveSurfaceCoefficientMajorant
          h v Y key ∧
      |(Q.b : ℝ)| ≤
        main3LargeAnalyticFixedTargetPrimitiveSurfaceCoefficientMajorant
          h v Y key ∧
      |(Q.c : ℝ)| ≤
        main3LargeAnalyticFixedTargetPrimitiveSurfaceCoefficientMajorant
          h v Y key := by
  let S := main3LargeAnalyticFixedTargetSurfaceForm hi y
  let g := integralBinaryQuadraticFormContent S
  let Q := integralBinaryQuadraticFormPrimitivePart S
  change |(Q.a : ℝ)| ≤ _ ∧ |(Q.b : ℝ)| ≤ _ ∧ |(Q.c : ℝ)| ≤ _
  have hraw := main3LargeAnalytic_fixedTargetSurfaceForm_coefficients_abs_le
    htheta hY hi key cell y p₀
  change |(S.a : ℝ)| ≤ _ ∧ |(S.b : ℝ)| ≤ _ ∧ |(S.c : ℝ)| ≤ _
    at hraw
  have hsurface := main3LargeAnalytic_targetFibre_primitive_surfaceForm
    htheta hY hi key cell y p₀.property
  have hgpos : 0 < g := by
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
        (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let B := shiftedSquareFixedExplicitIntegralBasisData
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
    change IsCoprime (p₀.1.1 0) (p₀.1.1 1) ∧
        IsCoprime (y 0) (y 1) ∧ _ at hsurface
    change 0 < integralBinaryQuadraticFormContent
      (shiftedSquareSurfaceForm B.t B.c y)
    exact shiftedSquareSurfaceForm_content_pos B.t B.c y hsurface.2.1
  have hgOne : (1 : ℝ) ≤ (g : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hgpos.ne')
  have hcoeffShrink
      (q s : ℤ) (hscale : (g : ℤ) * q = s) :
      |(q : ℝ)| ≤ |(s : ℝ)| := by
    have hscaleReal : (g : ℝ) * (q : ℝ) = (s : ℝ) := by
      exact_mod_cast hscale
    calc
      |(q : ℝ)| = 1 * |(q : ℝ)| := by ring
      _ ≤ (g : ℝ) * |(q : ℝ)| :=
        mul_le_mul_of_nonneg_right hgOne (abs_nonneg _)
      _ = |(g : ℝ) * (q : ℝ)| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (g : ℝ))]
      _ = |(s : ℝ)| := congrArg abs hscaleReal
  refine ⟨(hcoeffShrink Q.a S.a ?_).trans hraw.1,
    (hcoeffShrink Q.b S.b ?_).trans hraw.2.1,
    (hcoeffShrink Q.c S.c ?_).trans hraw.2.2⟩
  · exact integralBinaryQuadraticFormContent_mul_primitivePart_a S
  · exact integralBinaryQuadraticFormContent_mul_primitivePart_b S
  · exact integralBinaryQuadraticFormContent_mul_primitivePart_c S

end

end PellPaper
