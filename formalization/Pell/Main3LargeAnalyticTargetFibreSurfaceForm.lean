import Pell.Main3LargeAnalyticCommonFactorFiberReduction
import Pell.Main3LargeAnalyticFixedBasisEncoding
import Pell.ShiftedSquareSurfaceForm
import Mathlib.Tactic

/-!
# The fixed surface form on one main3 large-analytic target fibre

This file identifies the exact arithmetic carried by a member of the target
fibre introduced in `Main3LargeAnalyticCommonFactorFiberReduction`.
The integral basis is the canonical basis chosen from the fixed shift before
the fibre point is selected.  Every retained source vector is primitive and
represents the fixed nonzero auxiliary-key level on the corresponding
fixed-target binary quadratic form.

No representation-number estimate, unit-orbit bound, or target-fibre
cardinality bound is asserted here.
-/

namespace PellPaper

noncomputable section

/-- Evaluation scales by the coefficient content when an integral binary
quadratic form is replaced by its primitive part. -/
private theorem integralBinaryQuadraticFormContent_mul_primitivePart_eval
    (Q : IntegralBinaryQuadraticForm) (x₀ x₁ : ℤ) :
    (integralBinaryQuadraticFormContent Q : ℤ) *
        (integralBinaryQuadraticFormPrimitivePart Q).eval x₀ x₁ =
      Q.eval x₀ x₁ := by
  calc
    (integralBinaryQuadraticFormContent Q : ℤ) *
          (integralBinaryQuadraticFormPrimitivePart Q).eval x₀ x₁ =
        ((integralBinaryQuadraticFormContent Q : ℤ) *
            (integralBinaryQuadraticFormPrimitivePart Q).a) * x₀ ^ 2 +
          ((integralBinaryQuadraticFormContent Q : ℤ) *
            (integralBinaryQuadraticFormPrimitivePart Q).b) * x₀ * x₁ +
          ((integralBinaryQuadraticFormContent Q : ℤ) *
            (integralBinaryQuadraticFormPrimitivePart Q).c) * x₁ ^ 2 := by
      simp only [IntegralBinaryQuadraticForm.eval]
      ring
    _ = Q.eval x₀ x₁ := by
      rw [integralBinaryQuadraticFormContent_mul_primitivePart_a,
        integralBinaryQuadraticFormContent_mul_primitivePart_b,
        integralBinaryQuadraticFormContent_mul_primitivePart_c]
      rfl

/-- A member of the exact target fibre consists of two primitive coordinate
vectors, and its source vector represents the fixed nonzero key level on the
literal binary quadratic form determined by the shift-fixed basis and the
fixed target `y`. -/
theorem main3LargeAnalytic_targetFibre_primitive_surfaceForm
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    {p : (Fin 2 → ℤ) × (Fin 2 → ℤ)}
    (hp : p ∈ main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let B := shiftedSquareFixedExplicitIntegralBasisData
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
    IsCoprime (p.1 0) (p.1 1) ∧
      IsCoprime (y 0) (y 1) ∧
        (shiftedSquareSurfaceForm B.t B.c y).eval (p.1 0) (p.1 1) =
            shiftedSquareAuxiliaryKeySurfaceLevel key ∧
          shiftedSquareAuxiliaryKeySurfaceLevel key ≠ 0 := by
  classical
  obtain ⟨hpImage, hpy⟩ :=
    (mem_main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y p).mp hp
  obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hpImage
  have heq : main3GeneralBidegreePointVectorEquiv.toEmbedding z =
      (shiftedSquareCoordinatePointSourceVector z,
        shiftedSquareCoordinatePointTargetVector z) :=
    main3GeneralBidegreePointVectorEquiv_apply z
  rw [heq] at hpy ⊢
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let B := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  change IsCoprime
      (shiftedSquareCoordinatePointSourceVector z 0)
      (shiftedSquareCoordinatePointSourceVector z 1) ∧
    IsCoprime (y 0) (y 1) ∧
      (shiftedSquareSurfaceForm B.t B.c y).eval
          (shiftedSquareCoordinatePointSourceVector z 0)
          (shiftedSquareCoordinatePointSourceVector z 1) =
        shiftedSquareAuxiliaryKeySurfaceLevel key ∧
      shiftedSquareAuxiliaryKeySurfaceLevel key ≠ 0
  have hprimitive :=
    main3LargeAnalytic_blockCellCoordinatePointImage_primitive
      htheta hY hi hz
  have hsource : IsCoprime
      (shiftedSquareCoordinatePointSourceVector z 0)
      (shiftedSquareCoordinatePointSourceVector z 1) := by
    simpa only [shiftedSquareCoordinatePointSourceVector,
      Matrix.cons_val_zero, Matrix.cons_val_one] using hprimitive.1
  have htarget : IsCoprime (y 0) (y 1) := by
    rw [← hpy]
    simpa only [shiftedSquareCoordinatePointTargetVector,
      Matrix.cons_val_zero, Matrix.cons_val_one] using hprimitive.2
  have hsurface :=
    main3LargeAnalytic_blockCellCoordinatePointImage_surfaceData
      htheta hY hi hz
  change quadraticLinearFormEval
      (shiftedSquareSurfaceCoefficients B.t B.c)
      (shiftedSquareCoordinatePointSourceVector z)
      (shiftedSquareCoordinatePointTargetVector z) =
        shiftedSquareAuxiliaryKeySurfaceLevel key ∧
      shiftedSquareAuxiliaryKeySurfaceLevel key ≠ 0 at hsurface
  refine ⟨hsource, htarget, ?_, hsurface.2⟩
  rw [← hpy]
  rw [← quadraticLinearFormEval_shiftedSquareSurfaceCoefficients]
  exact hsurface.1

/-- The target of a fibre member retains the precise norm-factorization data
used by the positive-nonsquare-discriminant theorem.  Here `w` is the
squarefree target parameter of the original block point, while `ell` and
`C₀` are fields of that point's single retained normalized package. -/
theorem main3LargeAnalytic_targetFibre_targetNormData
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    {p : (Fin 2 → ℤ) × (Fin 2 → ℤ)}
    (hp : p ∈ main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let B := shiftedSquareFixedExplicitIntegralBasisData
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
    ∃ ell w C₀ : ℕ,
      0 < ell ∧ Squarefree w ∧ 1 < w ∧ 0 < C₀ ∧
        ell ^ 2 ∣ w * C₀ ^ 2 ∧
          shiftedSquareExplicitNormFormEval B.t B.c y =
            ((w * (C₀ / ell) ^ 2 : ℕ) : ℤ) := by
  classical
  obtain ⟨hpImage, hpy⟩ :=
    (mem_main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y p).mp hp
  obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hpImage
  have heq : main3GeneralBidegreePointVectorEquiv.toEmbedding z =
      (shiftedSquareCoordinatePointSourceVector z,
        shiftedSquareCoordinatePointTargetVector z) :=
    main3GeneralBidegreePointVectorEquiv_apply z
  rw [heq] at hpy
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let B := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  change ∃ ell w C₀ : ℕ,
    0 < ell ∧ Squarefree w ∧ 1 < w ∧ 0 < C₀ ∧
      ell ^ 2 ∣ w * C₀ ^ 2 ∧
        shiftedSquareExplicitNormFormEval B.t B.c y =
          ((w * (C₀ / ell) ^ 2 : ℕ) : ℤ)
  obtain ⟨q, hq, _hkey, _hcell, _hgeometry, _hcode, hzPackage⟩ :=
    main3LargeAnalytic_blockCellCoordinatePointImage_sameCertificate
      htheta hY hi hz
  let hY8 : 8 ≤ Y := by omega
  let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta hY8 hi q
  have hy : y = C.P.y := by
    rw [hzPackage] at hpy
    calc
      y = shiftedSquareCoordinatePointTargetVector
          ((C.P.x 0, C.P.x 1), (C.P.y 0, C.P.y 1)) := hpy.symm
      _ = C.P.y := by
        funext j
        fin_cases j <;> rfl
  have hwone : 1 < q.1.2.1 := by
    have hYw : Y ≤ q.1.2.1 := C.scaled.base.target_dyadic.1
    omega
  refine ⟨C.P.ell, q.1.2.1, C.P.minkowski.C₀,
    C.P.ell_pos, C.scaled.base.target_squarefree, hwone,
    C.P.minkowski.C₀_pos, C.P.ell_sq_dvd, ?_⟩
  rw [hy, ← C.t_eq, ← C.c_eq]
  exact C.P.normalized_target_norm

/-- Consequently, the primitive part of the fixed-target surface form is an
indefinite primitive binary quadratic form with positive nonsquare
discriminant.  Its discriminant retains a squarefree kernel `w > 1` coming
from the literal original block point. -/
theorem main3LargeAnalytic_targetFibre_surfacePrimitivePart_discriminantData
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    {p : (Fin 2 → ℤ) × (Fin 2 → ℤ)}
    (hp : p ∈ main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let B := shiftedSquareFixedExplicitIntegralBasisData
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
    let Q := integralBinaryQuadraticFormPrimitivePart
      (shiftedSquareSurfaceForm B.t B.c y)
    Q.Primitive ∧ 0 < Q.discriminant ∧ ¬ IsSquare Q.discriminant ∧
      ∃ w s : ℕ, Squarefree w ∧ 1 < w ∧ 0 < s ∧
        Q.discriminant = ((w * s ^ 2 : ℕ) : ℤ) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let B := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let Q := integralBinaryQuadraticFormPrimitivePart
    (shiftedSquareSurfaceForm B.t B.c y)
  change Q.Primitive ∧ 0 < Q.discriminant ∧
    ¬ IsSquare Q.discriminant ∧
      ∃ w s : ℕ, Squarefree w ∧ 1 < w ∧ 0 < s ∧
        Q.discriminant = ((w * s ^ 2 : ℕ) : ℤ)
  have hsurface := main3LargeAnalytic_targetFibre_primitive_surfaceForm
    htheta hY hi key cell y hp
  change IsCoprime (p.1 0) (p.1 1) ∧
      IsCoprime (y 0) (y 1) ∧
        (shiftedSquareSurfaceForm B.t B.c y).eval (p.1 0) (p.1 1) =
            shiftedSquareAuxiliaryKeySurfaceLevel key ∧
          shiftedSquareAuxiliaryKeySurfaceLevel key ≠ 0 at hsurface
  have htargetNorm := main3LargeAnalytic_targetFibre_targetNormData
    htheta hY hi key cell y hp
  change ∃ ell w C₀ : ℕ,
    0 < ell ∧ Squarefree w ∧ 1 < w ∧ 0 < C₀ ∧
      ell ^ 2 ∣ w * C₀ ^ 2 ∧
        shiftedSquareExplicitNormFormEval B.t B.c y =
          ((w * (C₀ / ell) ^ 2 : ℕ) : ℤ) at htargetNorm
  obtain ⟨ell, w, C₀, hell, hw, hwone, hC₀, hdiv, hnorm⟩ := htargetNorm
  have hdisc :=
    shiftedSquareSurfacePrimitivePart_discriminant_pos_not_isSquare
      B.t B.c y hsurface.2.1 B.t_zero_or_one hell hw hwone hC₀ hdiv
        (by simpa only [shiftedSquareExplicitNormFormEval] using hnorm)
  obtain ⟨s, hs, _hscases, hscale⟩ := hdisc.2.2.2.2
  exact ⟨hdisc.1, hdisc.2.2.1, hdisc.2.2.2.1,
    w, s, hw, hwone, hs, hscale⟩

/-- Passing from the literal surface form to its primitive part loses only
its content, which is exactly `1` or `2`.  Thus every source in the target
fibre represents the fixed nonzero quotient of the key level by that common
content. -/
theorem main3LargeAnalytic_targetFibre_primitivePart_representation
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    {p : (Fin 2 → ℤ) × (Fin 2 → ℤ)}
    (hp : p ∈ main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let B := shiftedSquareFixedExplicitIntegralBasisData
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
    let S := shiftedSquareSurfaceForm B.t B.c y
    let g := integralBinaryQuadraticFormContent S
    let Q := integralBinaryQuadraticFormPrimitivePart S
    0 < g ∧ (g = 1 ∨ g = 2) ∧
      (g : ℤ) ∣ shiftedSquareAuxiliaryKeySurfaceLevel key ∧
        Q.eval (p.1 0) (p.1 1) =
            shiftedSquareAuxiliaryKeySurfaceLevel key / (g : ℤ) ∧
          Q.eval (p.1 0) (p.1 1) ≠ 0 := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let B := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let S := shiftedSquareSurfaceForm B.t B.c y
  let g := integralBinaryQuadraticFormContent S
  let Q := integralBinaryQuadraticFormPrimitivePart S
  change 0 < g ∧ (g = 1 ∨ g = 2) ∧
    (g : ℤ) ∣ shiftedSquareAuxiliaryKeySurfaceLevel key ∧
      Q.eval (p.1 0) (p.1 1) =
          shiftedSquareAuxiliaryKeySurfaceLevel key / (g : ℤ) ∧
        Q.eval (p.1 0) (p.1 1) ≠ 0
  have hsurface := main3LargeAnalytic_targetFibre_primitive_surfaceForm
    htheta hY hi key cell y hp
  change IsCoprime (p.1 0) (p.1 1) ∧
      IsCoprime (y 0) (y 1) ∧
        S.eval (p.1 0) (p.1 1) =
            shiftedSquareAuxiliaryKeySurfaceLevel key ∧
          shiftedSquareAuxiliaryKeySurfaceLevel key ≠ 0 at hsurface
  have hgpos : 0 < g := by
    exact shiftedSquareSurfaceForm_content_pos B.t B.c y hsurface.2.1
  have hgle : g ≤ 2 := by
    exact shiftedSquareSurfaceForm_content_le_two_of_t_zero_or_one
      B.t B.c y hsurface.2.1 B.t_zero_or_one
  have hgcases : g = 1 ∨ g = 2 := by omega
  have hscale : (g : ℤ) * Q.eval (p.1 0) (p.1 1) =
      shiftedSquareAuxiliaryKeySurfaceLevel key := by
    exact (integralBinaryQuadraticFormContent_mul_primitivePart_eval
      S (p.1 0) (p.1 1)).trans hsurface.2.2.1
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hgpos.ne'
  have hdvd : (g : ℤ) ∣ shiftedSquareAuxiliaryKeySurfaceLevel key :=
    ⟨Q.eval (p.1 0) (p.1 1), hscale.symm⟩
  have hquotient : Q.eval (p.1 0) (p.1 1) =
      shiftedSquareAuxiliaryKeySurfaceLevel key / (g : ℤ) := by
    rw [← hscale]
    simp only [Int.mul_ediv_cancel_left _ hg0]
  have heval0 : Q.eval (p.1 0) (p.1 1) ≠ 0 := by
    intro heval
    rw [heval, mul_zero] at hscale
    exact hsurface.2.2.2 hscale.symm
  exact ⟨hgpos, hgcases, hdvd, hquotient, heval0⟩

end

end PellPaper
