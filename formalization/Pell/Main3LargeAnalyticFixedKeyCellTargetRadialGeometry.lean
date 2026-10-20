import Pell.PrimitiveWedgeReducedTargetCover
import Mathlib.Tactic

/-!
# Radial geometry for one fixed main3 target cell

This module packages the exact fixed-cell target image with the Hermitian
radial functional required by `exists_primitiveWedge_reducedTargetCover`.
The complex and real branches use the sharp target norm scales, so their
wedge constants retain the respective factors `6 / M` and `2 / M`.
-/

namespace PellPaper

open scoped MatrixGroups ComplexConjugate

noncomputable section

local instance main3LargeAnalyticFixedKeyCellTargetRadialGeometry_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-! ## The anchor-Hermitian additive functional -/

/-- The target linear form, regarded as an additive homomorphism on integral
target columns. -/
def main3IntegralTargetLinearFormAddHom (omega : ℂ) :
    (Fin 2 → ℤ) →+ ℂ where
  toFun y := main3IntegralTargetLinearForm omega y
  map_zero' := by simp [main3IntegralTargetLinearForm]
  map_add' y₁ y₂ := by
    simp only [main3IntegralTargetLinearForm, Pi.add_apply, Int.cast_add]
    ring

@[simp]
theorem main3IntegralTargetLinearFormAddHom_apply
    (omega : ℂ) (y : Fin 2 → ℤ) :
    main3IntegralTargetLinearFormAddHom omega y =
      main3IntegralTargetLinearForm omega y := rfl

/-- The real Hermitian row anchored at `y₀`. -/
def main3AnchorHermitianRadialAddHom
    (s : ℝ) (omega : ℂ) (y₀ : Fin 2 → ℤ) :
    (Fin 2 → ℤ) →+ ℝ where
  toFun y := s *
    (conj (main3IntegralTargetLinearFormAddHom omega y₀) *
      main3IntegralTargetLinearFormAddHom omega y).re
  map_zero' := by
    change s *
      (conj (main3IntegralTargetLinearFormAddHom omega y₀) *
        main3IntegralTargetLinearFormAddHom omega 0).re = 0
    rw [(main3IntegralTargetLinearFormAddHom omega).map_zero]
    simp
  map_add' y₁ y₂ := by
    change s *
      (conj (main3IntegralTargetLinearFormAddHom omega y₀) *
        main3IntegralTargetLinearFormAddHom omega (y₁ + y₂)).re = _
    rw [(main3IntegralTargetLinearFormAddHom omega).map_add, mul_add,
      Complex.add_re]
    ring

@[simp]
theorem main3AnchorHermitianRadialAddHom_apply
    (s : ℝ) (omega : ℂ) (y₀ y : Fin 2 → ℤ) :
    main3AnchorHermitianRadialAddHom s omega y₀ y =
      s * (conj (main3IntegralTargetLinearForm omega y₀) *
        main3IntegralTargetLinearForm omega y).re := rfl

/-- The Hermitian row evaluates at its anchor as the weighted squared norm. -/
theorem main3AnchorHermitianRadialAddHom_self
    (s : ℝ) (omega : ℂ) (y₀ : Fin 2 → ℤ) :
    main3AnchorHermitianRadialAddHom s omega y₀ y₀ =
      s * ‖main3IntegralTargetLinearForm omega y₀‖ ^ 2 := by
  rw [main3AnchorHermitianRadialAddHom_apply,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

/-- Cauchy--Schwarz for the anchor-Hermitian row. -/
theorem abs_main3AnchorHermitianRadialAddHom_le
    (s : ℝ) (omega : ℂ) (y₀ y : Fin 2 → ℤ) :
    |main3AnchorHermitianRadialAddHom s omega y₀ y| ≤
      |s| * ‖main3IntegralTargetLinearForm omega y₀‖ *
        ‖main3IntegralTargetLinearForm omega y‖ := by
  rw [main3AnchorHermitianRadialAddHom_apply, abs_mul]
  calc
    |s| * |(conj (main3IntegralTargetLinearForm omega y₀) *
          main3IntegralTargetLinearForm omega y).re| ≤
        |s| * ‖conj (main3IntegralTargetLinearForm omega y₀) *
          main3IntegralTargetLinearForm omega y‖ := by
      gcongr
      exact Complex.abs_re_le_norm _
    _ = |s| * ‖main3IntegralTargetLinearForm omega y₀‖ *
        ‖main3IntegralTargetLinearForm omega y‖ := by
      rw [norm_mul, Complex.norm_conj]
      ring

/-- The same estimate with a nonnegative scalar written without `|s|`. -/
theorem abs_main3AnchorHermitianRadialAddHom_le_of_nonneg
    {s : ℝ} (hs : 0 ≤ s) (omega : ℂ) (y₀ y : Fin 2 → ℤ) :
    |main3AnchorHermitianRadialAddHom s omega y₀ y| ≤
      s * ‖main3IntegralTargetLinearForm omega y₀‖ *
        ‖main3IntegralTargetLinearForm omega y‖ := by
  simpa only [abs_of_nonneg hs] using
    abs_main3AnchorHermitianRadialAddHom_le s omega y₀ y

/-! ## A compact wrapper for the generic reduced-cover theorem -/

/-- The input certificate for the primitive wedge reduced-cover theorem. -/
structure PrimitiveWedgeReducedTargetCoverCertificate
    (T : Finset (Fin 2 → ℤ)) (R K C : ℝ) where
  ell : (Fin 2 → ℤ) →+ ℝ
  anchor : Fin 2 → ℤ
  anchor_mem : anchor ∈ T
  primitive : ∀ y ∈ T, IsCoprime (y 0) (y 1)
  R_pos : 0 < R
  K_pos : 0 < K
  C_pos : 0 < C
  anchor_pos : 0 < ell anchor
  radial : ∀ y ∈ T, |ell y| ≤ R
  wedge : ∀ y₁ ∈ T, ∀ y₂ ∈ T,
    |(main3IntegralTargetWedge y₁ y₂ : ℝ)| ≤ K
  radius_le : R ≤ C * ell anchor

/-- The complete output proposition of the reduced-cover construction.  It
is named here so branch-specific certificates can expose the exact image,
primitivity, recovery, rectangle, and thin/full alternatives without copying
the implementation theorem at every use site. -/
def PrimitiveWedgeReducedTargetCoverSpec
    (T : Finset (Fin 2 → ℤ)) (ell : (Fin 2 → ℤ) →+ ℝ)
    (y₀ : Fin 2 → ℤ) (R K C : ℝ) (G H : SL(2, ℤ)) : Prop :=
  let rho := ell y₀
  let U := K / 2
  let V := 1 + C / 2
  let M₀ := 2 * rho * V / R
  (∀ i, G i 0 = y₀ i) ∧
  let beta := ell (fun i ↦ G i 1)
  let z := -K * beta / R
  let mu := firstSlopeSupNorm U V M₀ z
  let delta := M₀ / (U * V)
  let A := 4 / mu
  let B := 4 * mu / delta
  let W := G * H
  slopeVectorSupNorm U V M₀ z (H 0 0, H 1 0) = mu ∧
  (∀ y ∈ T,
    slopeVectorSupNorm U V M₀ z
      (G.toLin'.symm y 0, G.toLin'.symm y 1) ≤ 2) ∧
  1 ≤ M₀ ∧
  0 < mu ∧
  0 < delta ∧
  delta = 4 * rho / (R * K) ∧
  mu ^ 2 ≤ delta ∧
  U * V / M₀ = R * K / (4 * rho) ∧
  U * V / M₀ ≤ C * K / 4 ∧
  A * B = 4 * R * K / rho ∧
  (∀ (S : ℝ) (y : Fin 2 → ℤ),
    slopeVectorSupNorm U V M₀ z
        (G.toLin'.symm y 0, G.toLin'.symm y 1) ≤ S →
      |((W.toLin'.symm y 0 : ℤ) : ℝ)| ≤ 2 * S / mu ∧
      |((W.toLin'.symm y 1 : ℤ) : ℝ)| ≤
        2 * mu * S / delta) ∧
  (sl2InverseTargetImage W T).card = T.card ∧
  (∀ x ∈ sl2InverseTargetImage W T, IsCoprime (x 0) (x 1)) ∧
  (∀ y ∈ T, W.toLin' (W.toLin'.symm y) = y) ∧
  sl2InverseTargetImage W T ⊆ integerSymmetricRectangle A B ∧
  2 ≤ A ∧
  A ≤ 4 * (U + V) ∧
  B ≤ 4 * (U + V) ∧
  (B < 1 → T.card ≤ 2) ∧
  (1 ≤ B →
    ((integerSymmetricRectangle A B).card : ℝ) ≤ 144 * U * V / M₀ ∧
    ((integerSymmetricRectangle A B).card : ℝ) ≤ 36 * C * K ∧
    ((integerSymmetricInterval A).card : ℝ) ≤ 12 / mu ∧
    ((integerSymmetricInterval B).card : ℝ) ≤ 12 * mu / delta ∧
    ((integerSymmetricInterval A).card : ℝ) +
      ((integerSymmetricInterval B).card : ℝ) ≤ 24 / mu)

/-- A certified family has the complete public reduced-cover specification
from `exists_primitiveWedge_reducedTargetCover`. -/
theorem PrimitiveWedgeReducedTargetCoverCertificate.exists_reducedTargetCover
    {T : Finset (Fin 2 → ℤ)} {R K C : ℝ}
    (cert : PrimitiveWedgeReducedTargetCoverCertificate T R K C) :
    ∃ G H : SL(2, ℤ),
      PrimitiveWedgeReducedTargetCoverSpec
        T cert.ell cert.anchor R K C G H := by
  simpa only [PrimitiveWedgeReducedTargetCoverSpec] using
    exists_primitiveWedge_reducedTargetCover
      T cert.ell cert.anchor R K C cert.anchor_mem cert.primitive
        cert.R_pos cert.K_pos cert.C_pos cert.anchor_pos cert.radial cert.wedge
        cert.radius_le

/-! ## Dyadic target scale facts -/

/-- The lower half of the target dyadic interval supplies the reverse target
scale inequality, with the exact factor two. -/
theorem main3LargeAnalyticFixedKeyTargetScaleUpper_le_two_mul_EGamma
    {a : ℤ} {d w n Y : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (hYw : Y ≤ w)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    main3LargeAnalyticFixedKeyTargetScaleUpper Y
        ⟨P.minkowski.C₀, P.r, P.ell, P.bζ⟩ ≤
      2 * shiftedSquareEGamma P := by
  unfold main3LargeAnalyticFixedKeyTargetScaleUpper shiftedSquareEGamma
  have hYwR : (Y : ℝ) ≤ (w : ℝ) := by exact_mod_cast hYw
  have hnum : 2 * (Y : ℝ) * (P.minkowski.C₀ : ℝ) ^ 2 ≤
      2 * (w : ℝ) * (P.minkowski.C₀ : ℝ) ^ 2 := by
    gcongr
  calc
    2 * (Y : ℝ) * (P.minkowski.C₀ : ℝ) ^ 2 / (P.ell : ℝ) ^ 2 ≤
        2 * (w : ℝ) * (P.minkowski.C₀ : ℝ) ^ 2 /
          (P.ell : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ = 2 * (((w * P.minkowski.C₀ ^ 2 : ℕ) : ℝ) /
        (P.ell : ℝ) ^ 2) := by
      push_cast
      ring

/-- A nonempty literal fixed-key cell has strictly positive target scale. -/
theorem main3LargeAnalyticFixedKeyTargetScaleUpper_pos_of_mem
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    {y : Fin 2 → ℤ}
    (hy : y ∈ main3LargeAnalyticFixedKeyCellTargetVectorImage
      htheta hY hi key cell) :
    0 < main3LargeAnalyticFixedKeyTargetScaleUpper Y key := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  obtain ⟨z, hz, _hyz⟩ :=
    (mem_main3LargeAnalyticFixedKeyCellTargetVectorImage_iff
      htheta hY hi key cell y).mp hy
  obtain ⟨p, _hp, hkey, _hcell, _hgeometry, _hcode, _hzPoint⟩ :=
    main3LargeAnalytic_blockCellCoordinatePointImage_sameCertificate
      htheta hY hi hz
  let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta (by omega : 8 ≤ Y) hi p
  rw [← hkey]
  unfold main3LargeAnalyticFixedKeyTargetScaleUpper
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have hC₀pos : (0 : ℝ) < C.P.minkowski.C₀ := by
    exact_mod_cast C.P.minkowski.C₀_pos
  have hellpos : (0 : ℝ) < C.P.ell := by exact_mod_cast C.P.ell_pos
  positivity

/-! ## Exact complex-place target radial scale -/

/-- Every target in a positive-shift complex cell has norm square between
`E / 2` and `E`, where `E` is the fixed-key target scale. -/
theorem main3LargeAnalyticFixedKeyComplexCellTargetVectorImage_norm_sq_bounds
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : ComplexUnitCircleSlopeCellIndex)
    (ha : 0 < shiftedSquareA h v)
    {y : Fin 2 → ℤ}
    (hy : y ∈ main3LargeAnalyticFixedKeyCellTargetVectorImage
      htheta hY hi key (Sum.inr cell)) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let F := shiftedSquareFixedExplicitIntegralBasisData
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
    let sigma := shiftedSquareImaginaryPlaceEmbedding
      (shiftedSquareA h v) ha
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    E ≤ 2 * ‖main3IntegralTargetLinearForm (sigma F.omega) y‖ ^ 2 ∧
      ‖main3IntegralTargetLinearForm (sigma F.omega) y‖ ^ 2 ≤ E := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  obtain ⟨z, hz, rfl⟩ :=
    (mem_main3LargeAnalyticFixedKeyCellTargetVectorImage_iff
      htheta hY hi key (Sum.inr cell) y).mp hy
  obtain ⟨p, _hp, hkey, _hcell, _hgeometry, _hcode, hzPoint⟩ :=
    main3LargeAnalytic_blockCellCoordinatePointImage_sameCertificate
      htheta hY hi hz
  let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta (by omega : 8 ≤ Y) hi p
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquareImaginaryPlaceEmbedding
    (shiftedSquareA h v) ha
  have hzPackage : z = main3ShiftedSquarePackagePoint C.P :=
    hzPoint.trans (main3ShiftedSquarePackagePoint_eq C.P).symm
  have hden :=
    main3ShiftedSquarePackagePoint_targetDenominator_eq
      F C.P C.omega_eq sigma
  have hlinear :
      main3IntegralTargetLinearForm (sigma F.omega)
          (shiftedSquareCoordinatePointTargetVector z) =
        sigma (shiftedSquareIntegralBasisElement C.P.basis C.P.y :
          rationalQuadraticAlgebra (-(shiftedSquareA h v))) := by
    rw [hzPackage]
    simpa only [main3IntegralTargetLinearForm,
      shiftedSquareCoordinatePointTargetVector,
      main3ShiftedSquarePackagePoint, Matrix.cons_val_zero,
      Matrix.cons_val_one, main3ShiftedSquareEmbeddingOmega] using hden
  have hnormSq :
      ‖main3IntegralTargetLinearForm (sigma F.omega)
          (shiftedSquareCoordinatePointTargetVector z)‖ ^ 2 =
        shiftedSquareEGamma C.P := by
    rw [hlinear]
    exact shiftedSquare_imaginaryPlace_targetPrimitive_norm_sq_eq_EGamma
      ha C.P
  constructor
  · rw [hnormSq, ← hkey]
    exact main3LargeAnalyticFixedKeyTargetScaleUpper_le_two_mul_EGamma
      C.scaled.base.target_dyadic.1 C.P
  · rw [hnormSq, ← hkey]
    exact shiftedSquareEGamma_le_fixedKeyTargetScaleUpper
      C.scaled.base.target_dyadic.2 C.P

/-! ## Complex-cell reduced-cover certificate -/

/-- A nonempty complex fixed-cell target image supplies the sharp Hermitian
input certificate.  The final four identities record the normalized
parameters and the exact side/cardinality constants inherited by the generic
reduced-cover specification. -/
theorem exists_main3LargeAnalyticFixedKeyComplexCellTargetRadialCoverCertificate
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : ComplexUnitCircleSlopeCellIndex)
    (ha : 0 < shiftedSquareA h v)
    (hnonempty :
      (main3LargeAnalyticFixedKeyCellTargetVectorImage
        htheta hY hi key (Sum.inr cell)).Nonempty) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let F := shiftedSquareFixedExplicitIntegralBasisData
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
    let sigma := shiftedSquareImaginaryPlaceEmbedding
      (shiftedSquareA h v) ha
    let T := main3LargeAnalyticFixedKeyCellTargetVectorImage
      htheta hY hi key (Sum.inr cell)
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    let Delta := Real.sqrt
      |(NumberField.discr
        (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
    let Mmesh := (main3UnbalancedM theta Y : ℝ)
    let K := (6 * E / Mmesh) / Delta
    ∃ cert : PrimitiveWedgeReducedTargetCoverCertificate T E K 2,
      cert.ell = main3AnchorHermitianRadialAddHom
        1 (sigma F.omega) cert.anchor ∧
      E ≤ 2 * cert.ell cert.anchor ∧
      cert.ell cert.anchor ≤ E ∧
      let rho := cert.ell cert.anchor
      let U := K / 2
      let V := 1 + (2 : ℝ) / 2
      let M₀ := 2 * rho * V / E
      V = 2 ∧
      M₀ = 4 * rho / E ∧
      2 ≤ M₀ ∧ M₀ ≤ 4 ∧
      4 * (U + V) = 2 * K + 8 ∧
      36 * 2 * K = 432 * E / (Mmesh * Delta) := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquareImaginaryPlaceEmbedding
    (shiftedSquareA h v) ha
  let T := main3LargeAnalyticFixedKeyCellTargetVectorImage
    htheta hY hi key (Sum.inr cell)
  let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let Delta := Real.sqrt
    |(NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
  let Mmesh := (main3UnbalancedM theta Y : ℝ)
  let K := (6 * E / Mmesh) / Delta
  obtain ⟨y₀, hy₀⟩ := hnonempty
  have hE : 0 < E := by
    dsimp only [E]
    exact main3LargeAnalyticFixedKeyTargetScaleUpper_pos_of_mem
      htheta hY hi key (Sum.inr cell) hy₀
  have hdiscZ :
      NumberField.discr
        (rationalQuadraticAlgebra (-(shiftedSquareA h v))) ≠ 0 :=
    NumberField.discr_ne_zero _
  have hdiscR :
      (NumberField.discr
        (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ) ≠ 0 := by
    exact_mod_cast hdiscZ
  have hDelta : 0 < Delta := by
    dsimp only [Delta]
    exact Real.sqrt_pos.2 (abs_pos.mpr hdiscR)
  have hMmesh : 0 < Mmesh := by
    dsimp only [Mmesh]
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 6)
      (six_le_main3UnbalancedM htheta hY))
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hnorm : ∀ y ∈ T,
      E ≤ 2 * ‖main3IntegralTargetLinearForm (sigma F.omega) y‖ ^ 2 ∧
        ‖main3IntegralTargetLinearForm (sigma F.omega) y‖ ^ 2 ≤ E := by
    intro y hy
    simpa only [T, E, F, sigma] using
      main3LargeAnalyticFixedKeyComplexCellTargetVectorImage_norm_sq_bounds
        htheta hY hi key cell ha hy
  let ell := main3AnchorHermitianRadialAddHom 1 (sigma F.omega) y₀
  have hrhoEq : ell y₀ =
      ‖main3IntegralTargetLinearForm (sigma F.omega) y₀‖ ^ 2 := by
    simpa only [ell, one_mul] using
      main3AnchorHermitianRadialAddHom_self 1 (sigma F.omega) y₀
  have hrhoLower : E ≤ 2 * ell y₀ := by
    rw [hrhoEq]
    exact (hnorm y₀ hy₀).1
  have hrhoUpper : ell y₀ ≤ E := by
    rw [hrhoEq]
    exact (hnorm y₀ hy₀).2
  have hrhoPos : 0 < ell y₀ := by nlinarith
  have hradial : ∀ y ∈ T, |ell y| ≤ E := by
    intro y hy
    have hCauchy :=
      abs_main3AnchorHermitianRadialAddHom_le_of_nonneg
        (by norm_num : (0 : ℝ) ≤ 1) (sigma F.omega) y₀ y
    have hprod :
        ‖main3IntegralTargetLinearForm (sigma F.omega) y₀‖ *
            ‖main3IntegralTargetLinearForm (sigma F.omega) y‖ ≤ E := by
      have h₀ := (hnorm y₀ hy₀).2
      have hy' := (hnorm y hy).2
      nlinarith [sq_nonneg
        (‖main3IntegralTargetLinearForm (sigma F.omega) y₀‖ -
          ‖main3IntegralTargetLinearForm (sigma F.omega) y‖)]
    have hCauchy' : |ell y| ≤
        ‖main3IntegralTargetLinearForm (sigma F.omega) y₀‖ *
          ‖main3IntegralTargetLinearForm (sigma F.omega) y‖ := by
      simpa only [ell, one_mul] using hCauchy
    exact hCauchy'.trans hprod
  have hwedge : ∀ y₁ ∈ T, ∀ y₂ ∈ T,
      |(main3IntegralTargetWedge y₁ y₂ : ℝ)| ≤ K := by
    intro y₁ hy₁ y₂ hy₂
    apply (le_div_iff₀ hDelta).2
    simpa only [K, E, Mmesh, Delta, T] using
      main3LargeAnalyticFixedKeyComplexCellTargetVectorImage_wedge_le
        htheta hY hi key cell ha hy₁ hy₂
  let cert : PrimitiveWedgeReducedTargetCoverCertificate T E K 2 :=
    { ell := ell
      anchor := y₀
      anchor_mem := hy₀
      primitive := by
        intro y hy
        exact main3LargeAnalyticFixedKeyCellTargetVectorImage_primitive
          htheta hY hi key (Sum.inr cell) hy
      R_pos := hE
      K_pos := hK
      C_pos := by norm_num
      anchor_pos := hrhoPos
      radial := hradial
      wedge := hwedge
      radius_le := hrhoLower }
  refine ⟨cert, ?_, ?_, ?_, ?_⟩
  · rfl
  · simpa only [cert] using hrhoLower
  · simpa only [cert] using hrhoUpper
  · refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩
    · ring
    · apply (le_div_iff₀ hE).2
      have := hrhoLower
      dsimp only [cert] at *
      norm_num at *
      nlinarith
    · apply (div_le_iff₀ hE).2
      have := hrhoUpper
      dsimp only [cert] at *
      nlinarith
    · ring
    · ring

/-! ## Exact real-place target radial scale -/

/-- Coordinate-point form of the real weighted target norm bounds.  The
normalized target parameter lies in `[1/2,2]`; the exact target norm product
then converts this into the displayed two-sided estimate. -/
theorem main3LargeAnalytic_realCellCoordinatePointImage_targetVector_weighted_norm_sq_bounds
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : RealSquareMapCellPairIndex)
    (ha : shiftedSquareA h v < 0)
    {z : GeneralBidegreeFormPoint}
    (hz : z ∈
      main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key (Sum.inl cell)) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let F := shiftedSquareFixedExplicitIntegralBasisData
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
    let sigma := shiftedSquarePositiveRealPlaceEmbedding
      (shiftedSquareA h v) ha
    let c := main3LargeAnalyticRealCellSignedCentre theta Y h v cell
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    E ≤ 4 * (c ^ 2 *
        ‖main3IntegralTargetLinearForm (sigma F.omega)
          (shiftedSquareCoordinatePointTargetVector z)‖ ^ 2) ∧
      c ^ 2 *
          ‖main3IntegralTargetLinearForm (sigma F.omega)
            (shiftedSquareCoordinatePointTargetVector z)‖ ^ 2 ≤
        2 * E := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  obtain ⟨p, _hp, hkey, _hcell, _hgeometry, _hcode, hzPoint⟩ :=
    main3LargeAnalytic_blockCellCoordinatePointImage_sameCertificate
      htheta hY hi hz
  let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta (by omega : 8 ≤ Y) hi p
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding
    (shiftedSquareA h v) ha
  let c := main3LargeAnalyticRealCellSignedCentre theta Y h v cell
  let S := main3LargeAnalyticRealCellNormalizedSource hi ha cell z
  let T := main3LargeAnalyticRealCellNormalizedTarget hi ha cell z
  let eps := (8 * Real.sqrt |(shiftedSquareA h v : ℝ)|) / (N : ℝ)
  let y := shiftedSquareCoordinatePointTargetVector z
  let gamma := main3IntegralTargetLinearForm (sigma F.omega) y
  let gammaBar := main3IntegralTargetLinearForm (sigma (star F.omega)) y
  have hnorm :=
    main3LargeAnalytic_realCellCoordinatePointImage_normalized_geometry
      htheta hY hi key cell ha hz
  change c ≠ 0 ∧ 1 ≤ S ∧
      S ≤ 1 + 1 / (main3UnbalancedM theta Y : ℝ) ∧ 0 < T ∧
      main3EmbeddingSourceRatio
          (sigma F.omega) (sigma (star F.omega)) z = ((c * S : ℝ) : ℂ) ∧
      main3EmbeddingTargetRatio
          (sigma F.omega) (sigma (star F.omega)) z = ((c ^ 2 * T : ℝ) : ℂ)
        at hnorm
  have hc : c ≠ 0 := hnorm.1
  have hSpos : 0 < S := zero_lt_one.trans_le hnorm.2.1
  have hTpos : 0 < T := hnorm.2.2.2.1
  have heps : eps ≤ 1 / 3 := by
    simpa only [eps] using
      main3LargeAnalytic_realCell_endpoint_error_le_one_third htheta hY hi
  have herror : |T / S ^ 2 - 1| ≤ eps := by
    simpa only [S, T, eps] using
      main3LargeAnalytic_realCellCoordinatePointImage_normalized_ratio_error_le_endpoint
        htheta hY hi key cell ha hz
  have herr := abs_le.mp herror
  have hratioLower : (2 / 3 : ℝ) ≤ T / S ^ 2 := by linarith
  have hratioUpper : T / S ^ 2 ≤ (4 / 3 : ℝ) := by linarith
  have hSsqLower : (1 : ℝ) ≤ S ^ 2 := by nlinarith [hnorm.2.1]
  have hTLower : (1 / 2 : ℝ) ≤ T := by
    have hmul : (2 / 3 : ℝ) * S ^ 2 ≤ T :=
      (le_div_iff₀ (sq_pos_of_pos hSpos)).mp hratioLower
    nlinarith
  have hM : (6 : ℝ) ≤ main3UnbalancedM theta Y := by
    exact_mod_cast six_le_main3UnbalancedM htheta hY
  have hInvM : 1 / (main3UnbalancedM theta Y : ℝ) ≤ 1 / 6 :=
    one_div_le_one_div_of_le (by norm_num) hM
  have hSUpper : S ≤ (7 / 6 : ℝ) := by
    have := hnorm.2.2.1
    linarith
  have hSsqUpper : S ^ 2 ≤ (7 / 6 : ℝ) ^ 2 := by
    nlinarith [hSpos.le]
  have hTUpper : T ≤ 2 := by
    have hmul : T ≤ (4 / 3 : ℝ) * S ^ 2 :=
      (div_le_iff₀ (sq_pos_of_pos hSpos)).mp hratioUpper
    calc
      T ≤ (4 / 3 : ℝ) * S ^ 2 := hmul
      _ ≤ (4 / 3 : ℝ) * (7 / 6 : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hSsqUpper (by norm_num)
      _ ≤ 2 := by norm_num
  have hzPackage : z = main3ShiftedSquarePackagePoint C.P :=
    hzPoint.trans (main3ShiftedSquarePackagePoint_eq C.P).symm
  have hratio := main3ShiftedSquarePackagePoint_ratioPair_eq
    F C.P C.omega_eq sigma
  have htargetPackage : shiftedSquareTargetEmbeddingRatio C.P sigma =
      ((c ^ 2 * T : ℝ) : ℂ) := by
    rw [← hnorm.2.2.2.2.2]
    rw [hzPackage]
    simpa only [main3ShiftedSquareEmbeddingOmega,
      main3ShiftedSquareEmbeddingOmegaBar] using (congrArg Prod.snd hratio).symm
  have hden := main3ShiftedSquarePackagePoint_targetDenominator_eq
    F C.P C.omega_eq sigma
  have hnum := main3ShiftedSquarePackagePoint_targetNumerator_eq
    F C.P C.omega_eq sigma
  have hlinear : gamma =
      sigma (shiftedSquareIntegralBasisElement C.P.basis C.P.y :
        rationalQuadraticAlgebra (-(shiftedSquareA h v))) := by
    dsimp only [gamma, y]
    rw [hzPackage]
    simpa only [main3IntegralTargetLinearForm,
      shiftedSquareCoordinatePointTargetVector,
      main3ShiftedSquarePackagePoint, Matrix.cons_val_zero,
      Matrix.cons_val_one, main3ShiftedSquareEmbeddingOmega] using hden
  have hlinearBar : gammaBar =
      sigma (star (shiftedSquareIntegralBasisElement C.P.basis C.P.y :
        rationalQuadraticAlgebra (-(shiftedSquareA h v)))) := by
    dsimp only [gammaBar, y]
    rw [hzPackage]
    simpa only [main3IntegralTargetLinearForm,
      shiftedSquareCoordinatePointTargetVector,
      main3ShiftedSquarePackagePoint, Matrix.cons_val_zero,
      Matrix.cons_val_one, main3ShiftedSquareEmbeddingOmegaBar] using hnum
  have hgamma : gamma ≠ 0 := by
    rw [hlinear]
    exact shiftedSquare_targetEmbeddingRatio_denominator_ne_zero C.P sigma
  have hratioComplex : gammaBar / gamma = ((c ^ 2 * T : ℝ) : ℂ) := by
    rw [hlinear, hlinearBar]
    simpa only [shiftedSquareTargetEmbeddingRatio] using htargetPackage
  have htargetNorm := congrArg norm hratioComplex
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (sq_pos_of_ne_zero hc) hTpos)] at htargetNorm
  have hgammaNorm : ‖gamma‖ ≠ 0 := norm_ne_zero_iff.mpr hgamma
  have hgammaBarMul : ‖gammaBar‖ = c ^ 2 * T * ‖gamma‖ := by
    apply (div_eq_iff hgammaNorm).mp
    simpa only [mul_comm, mul_left_comm, mul_assoc] using htargetNorm
  obtain ⟨_hdpos, hwpos, _hnpos, _hdLower, _hdUpper,
      _hwLower, hwUpper, _hNn, _hnUpper, _heq, _hsf⟩ :=
    mem_squarefreeShiftedSquareBlock.mp p.2
  have hproduct : ‖gamma‖ * ‖gammaBar‖ = shiftedSquareEGamma C.P := by
    rw [hlinear, hlinearBar]
    exact shiftedSquare_positiveRealPlace_target_norm_mul_eq_EGamma
      ha hwpos C.P
  have henergy : c ^ 2 * ‖gamma‖ ^ 2 * T = shiftedSquareEGamma C.P := by
    rw [← hproduct, hgammaBarMul]
    ring
  have hQnonneg : 0 ≤ c ^ 2 * ‖gamma‖ ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hQupperEG : c ^ 2 * ‖gamma‖ ^ 2 ≤
      2 * shiftedSquareEGamma C.P := by
    calc
      c ^ 2 * ‖gamma‖ ^ 2 ≤
          2 * (c ^ 2 * ‖gamma‖ ^ 2 * T) := by
        nlinarith [mul_nonneg hQnonneg (sub_nonneg.mpr hTLower)]
      _ = 2 * shiftedSquareEGamma C.P := by rw [henergy]
  have hEGlowerQ : shiftedSquareEGamma C.P ≤
      2 * (c ^ 2 * ‖gamma‖ ^ 2) := by
    calc
      shiftedSquareEGamma C.P = c ^ 2 * ‖gamma‖ ^ 2 * T := henergy.symm
      _ ≤ (c ^ 2 * ‖gamma‖ ^ 2) * 2 :=
        mul_le_mul_of_nonneg_left hTUpper hQnonneg
      _ = 2 * (c ^ 2 * ‖gamma‖ ^ 2) := by ring
  have hEGupper := shiftedSquareEGamma_le_fixedKeyTargetScaleUpper
    hwUpper C.P
  have hElower :=
    main3LargeAnalyticFixedKeyTargetScaleUpper_le_two_mul_EGamma
      C.scaled.base.target_dyadic.1 C.P
  rw [hkey] at hEGupper hElower
  change main3LargeAnalyticFixedKeyTargetScaleUpper Y key ≤
        4 * (c ^ 2 * ‖gamma‖ ^ 2) ∧
      c ^ 2 * ‖gamma‖ ^ 2 ≤
        2 * main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  constructor
  · calc
      main3LargeAnalyticFixedKeyTargetScaleUpper Y key ≤
          2 * shiftedSquareEGamma C.P := hElower
      _ ≤ 4 * (c ^ 2 * ‖gamma‖ ^ 2) := by linarith
  · calc
      c ^ 2 * ‖gamma‖ ^ 2 ≤ 2 * shiftedSquareEGamma C.P := hQupperEG
      _ ≤ 2 * main3LargeAnalyticFixedKeyTargetScaleUpper Y key := by
        gcongr

/-- Target-image form of the two-sided real weighted norm estimate. -/
theorem main3LargeAnalyticFixedKeyRealCellTargetVectorImage_weighted_norm_sq_bounds
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : RealSquareMapCellPairIndex)
    (ha : shiftedSquareA h v < 0)
    {y : Fin 2 → ℤ}
    (hy : y ∈ main3LargeAnalyticFixedKeyCellTargetVectorImage
      htheta hY hi key (Sum.inl cell)) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let F := shiftedSquareFixedExplicitIntegralBasisData
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
    let sigma := shiftedSquarePositiveRealPlaceEmbedding
      (shiftedSquareA h v) ha
    let c := main3LargeAnalyticRealCellSignedCentre theta Y h v cell
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    E ≤ 4 * (c ^ 2 * ‖main3IntegralTargetLinearForm (sigma F.omega) y‖ ^ 2) ∧
      c ^ 2 * ‖main3IntegralTargetLinearForm (sigma F.omega) y‖ ^ 2 ≤
        2 * E := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  obtain ⟨z, hz, rfl⟩ :=
    (mem_main3LargeAnalyticFixedKeyCellTargetVectorImage_iff
      htheta hY hi key (Sum.inl cell) y).mp hy
  exact
    main3LargeAnalytic_realCellCoordinatePointImage_targetVector_weighted_norm_sq_bounds
      htheta hY hi key cell ha hz

/-! ## Real-cell reduced-cover certificate -/

/-- A nonempty real fixed-cell target image supplies the signed-centre
Hermitian certificate.  Its normalized reciprocal-minimum parameter lies in
`[5/4,10]`, and the generic side/full-card constants simplify to `2K+20`
and `576 E/(M Delta)`. -/
theorem exists_main3LargeAnalyticFixedKeyRealCellTargetRadialCoverCertificate
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : RealSquareMapCellPairIndex)
    (ha : shiftedSquareA h v < 0)
    (hnonempty :
      (main3LargeAnalyticFixedKeyCellTargetVectorImage
        htheta hY hi key (Sum.inl cell)).Nonempty) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let F := shiftedSquareFixedExplicitIntegralBasisData
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
    let sigma := shiftedSquarePositiveRealPlaceEmbedding
      (shiftedSquareA h v) ha
    let c := main3LargeAnalyticRealCellSignedCentre theta Y h v cell
    let T := main3LargeAnalyticFixedKeyCellTargetVectorImage
      htheta hY hi key (Sum.inl cell)
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    let Delta := Real.sqrt
      |(NumberField.discr
        (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
    let Mmesh := (main3UnbalancedM theta Y : ℝ)
    let K := (2 * E / Mmesh) / Delta
    ∃ cert : PrimitiveWedgeReducedTargetCoverCertificate T (2 * E) K 8,
      cert.ell = main3AnchorHermitianRadialAddHom
        (c ^ 2) (sigma F.omega) cert.anchor ∧
      E ≤ 4 * cert.ell cert.anchor ∧
      cert.ell cert.anchor ≤ 2 * E ∧
      let rho := cert.ell cert.anchor
      let U := K / 2
      let V := 1 + (8 : ℝ) / 2
      let M₀ := 2 * rho * V / (2 * E)
      V = 5 ∧
      M₀ = 5 * rho / E ∧
      (5 / 4 : ℝ) ≤ M₀ ∧ M₀ ≤ 10 ∧
      4 * (U + V) = 2 * K + 20 ∧
      36 * 8 * K = 576 * E / (Mmesh * Delta) := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding
    (shiftedSquareA h v) ha
  let c := main3LargeAnalyticRealCellSignedCentre theta Y h v cell
  let T := main3LargeAnalyticFixedKeyCellTargetVectorImage
    htheta hY hi key (Sum.inl cell)
  let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let Delta := Real.sqrt
    |(NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
  let Mmesh := (main3UnbalancedM theta Y : ℝ)
  let K := (2 * E / Mmesh) / Delta
  obtain ⟨y₀, hy₀⟩ := hnonempty
  have hE : 0 < E := by
    dsimp only [E]
    exact main3LargeAnalyticFixedKeyTargetScaleUpper_pos_of_mem
      htheta hY hi key (Sum.inl cell) hy₀
  have hdiscZ :
      NumberField.discr
        (rationalQuadraticAlgebra (-(shiftedSquareA h v))) ≠ 0 :=
    NumberField.discr_ne_zero _
  have hdiscR :
      (NumberField.discr
        (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ) ≠ 0 := by
    exact_mod_cast hdiscZ
  have hDelta : 0 < Delta := by
    dsimp only [Delta]
    exact Real.sqrt_pos.2 (abs_pos.mpr hdiscR)
  have hMmesh : 0 < Mmesh := by
    dsimp only [Mmesh]
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 6)
      (six_le_main3UnbalancedM htheta hY))
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hnorm : ∀ y ∈ T,
      E ≤ 4 * (c ^ 2 *
        ‖main3IntegralTargetLinearForm (sigma F.omega) y‖ ^ 2) ∧
      c ^ 2 * ‖main3IntegralTargetLinearForm (sigma F.omega) y‖ ^ 2 ≤
        2 * E := by
    intro y hy
    simpa only [T, E, F, sigma, c] using
      main3LargeAnalyticFixedKeyRealCellTargetVectorImage_weighted_norm_sq_bounds
        htheta hY hi key cell ha hy
  let ell := main3AnchorHermitianRadialAddHom
    (c ^ 2) (sigma F.omega) y₀
  have hrhoEq : ell y₀ =
      c ^ 2 * ‖main3IntegralTargetLinearForm (sigma F.omega) y₀‖ ^ 2 := by
    simpa only [ell] using
      main3AnchorHermitianRadialAddHom_self (c ^ 2) (sigma F.omega) y₀
  have hrhoLower : E ≤ 4 * ell y₀ := by
    rw [hrhoEq]
    exact (hnorm y₀ hy₀).1
  have hrhoUpper : ell y₀ ≤ 2 * E := by
    rw [hrhoEq]
    exact (hnorm y₀ hy₀).2
  have hrhoPos : 0 < ell y₀ := by nlinarith
  have hradial : ∀ y ∈ T, |ell y| ≤ 2 * E := by
    intro y hy
    have hCauchy :=
      abs_main3AnchorHermitianRadialAddHom_le_of_nonneg
        (sq_nonneg c) (sigma F.omega) y₀ y
    have hprod :
        c ^ 2 * ‖main3IntegralTargetLinearForm (sigma F.omega) y₀‖ *
            ‖main3IntegralTargetLinearForm (sigma F.omega) y‖ ≤ 2 * E := by
      have h₀ := (hnorm y₀ hy₀).2
      have hy' := (hnorm y hy).2
      nlinarith [sq_nonneg
        (c * ‖main3IntegralTargetLinearForm (sigma F.omega) y₀‖ -
          c * ‖main3IntegralTargetLinearForm (sigma F.omega) y‖)]
    have hCauchy' : |ell y| ≤
        c ^ 2 * ‖main3IntegralTargetLinearForm (sigma F.omega) y₀‖ *
          ‖main3IntegralTargetLinearForm (sigma F.omega) y‖ := by
      simpa only [ell] using hCauchy
    exact hCauchy'.trans hprod
  have hwedge : ∀ y₁ ∈ T, ∀ y₂ ∈ T,
      |(main3IntegralTargetWedge y₁ y₂ : ℝ)| ≤ K := by
    intro y₁ hy₁ y₂ hy₂
    apply (le_div_iff₀ hDelta).2
    simpa only [K, E, Mmesh, Delta, T] using
      main3LargeAnalyticFixedKeyRealCellTargetVectorImage_wedge_le
        htheta hY hi key cell ha hy₁ hy₂
  have hcompare : 2 * E ≤ 8 * ell y₀ := by nlinarith
  let cert : PrimitiveWedgeReducedTargetCoverCertificate T (2 * E) K 8 :=
    { ell := ell
      anchor := y₀
      anchor_mem := hy₀
      primitive := by
        intro y hy
        exact main3LargeAnalyticFixedKeyCellTargetVectorImage_primitive
          htheta hY hi key (Sum.inl cell) hy
      R_pos := by positivity
      K_pos := hK
      C_pos := by norm_num
      anchor_pos := hrhoPos
      radial := hradial
      wedge := hwedge
      radius_le := hcompare }
  refine ⟨cert, ?_, ?_, ?_, ?_⟩
  · rfl
  · simpa only [cert] using hrhoLower
  · simpa only [cert] using hrhoUpper
  · refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩
    · ring
    · rw [show
          2 * cert.ell cert.anchor * (1 + (8 : ℝ) / 2) / (2 * E) =
            5 * cert.ell cert.anchor / E by ring]
      apply (le_div_iff₀ hE).2
      have := hrhoLower
      dsimp only [cert] at *
      norm_num at *
      nlinarith
    · rw [show
          2 * cert.ell cert.anchor * (1 + (8 : ℝ) / 2) / (2 * E) =
            5 * cert.ell cert.anchor / E by ring]
      apply (div_le_iff₀ hE).2
      have := hrhoUpper
      dsimp only [cert] at *
      nlinarith
    · ring
    · ring

end

end PellPaper
