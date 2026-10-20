import Pell.Main3LargeAnalyticFixedKeyCellTargetImageWitness
import Pell.Main3LargeAnalyticRealCellRateLedger
import Pell.Main3LargeAnalyticComplexCellMinorVanishing
import Pell.Main3EmbeddingBasisColumnChangeDeterminant
import Mathlib.Tactic

/-!
# Fixed-cell intrinsic target lattice geometry

This candidate keeps the literal target image of one fixed auxiliary key and
one archimedean cell.  The basic algebraic identity turns the determinant of
two integral target-coordinate columns into a difference of embedded target
linear forms.  The real and complex cell geometries then provide the missing
`1 / M` gain, while the exact target norm identities retain only the common
fixed-key upper scale.
-/

namespace PellPaper

noncomputable section

local instance main3LargeAnalyticFixedKeyCellTargetLatticeGeometry_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- The integral target vector evaluated at one embedded basis generator. -/
def main3IntegralTargetLinearForm (omega : ℂ) (y : Fin 2 → ℤ) : ℂ :=
  (y 0 : ℂ) + omega * (y 1 : ℂ)

/-- The oriented integral area of two target-coordinate columns. -/
def main3IntegralTargetWedge (y₁ y₂ : Fin 2 → ℤ) : ℤ :=
  y₁ 0 * y₂ 1 - y₁ 1 * y₂ 0

/-- Exact two-column identity in the embedded integral basis. -/
theorem main3IntegralTargetLinearForm_wedge_identity
    (omega omegaBar : ℂ) (y₁ y₂ : Fin 2 → ℤ) :
    main3IntegralTargetLinearForm omegaBar y₁ *
          main3IntegralTargetLinearForm omega y₂ -
        main3IntegralTargetLinearForm omegaBar y₂ *
          main3IntegralTargetLinearForm omega y₁ =
      (main3IntegralTargetWedge y₁ y₂ : ℂ) * (omega - omegaBar) := by
  simp only [main3IntegralTargetLinearForm, main3IntegralTargetWedge]
  push_cast
  ring

/-- The embedded basis difference converts the norm of the exact wedge
identity into the square root of the field discriminant. -/
theorem norm_main3IntegralTargetLinearForm_wedge_eq
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (y₁ y₂ : Fin 2 → ℤ) :
    ‖main3IntegralTargetLinearForm (sigma (star F.omega)) y₁ *
          main3IntegralTargetLinearForm (sigma F.omega) y₂ -
        main3IntegralTargetLinearForm (sigma (star F.omega)) y₂ *
          main3IntegralTargetLinearForm (sigma F.omega) y₁‖ =
      |(main3IntegralTargetWedge y₁ y₂ : ℝ)| *
        Real.sqrt
          |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)| := by
  rw [main3IntegralTargetLinearForm_wedge_identity, norm_mul,
    Complex.norm_intCast]
  have hdiff :
      ‖sigma F.omega - sigma (star F.omega)‖ =
        Real.sqrt
          |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)| := by
    calc
      ‖sigma F.omega - sigma (star F.omega)‖ =
          Real.sqrt (‖sigma F.omega - sigma (star F.omega)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt
          |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)| := by
        congr 1
        rw [← map_sub]
        exact shiftedSquareFixedBasis_embeddingDifference_norm_sq F sigma
  rw [hdiff]

/-- Clearing the two target denominators turns a quotient difference into
the cross product occurring in the wedge identity. -/
private theorem targetLinearForm_cross_eq_ratioDifference_mul
    (gammaBar₁ gamma₁ gammaBar₂ gamma₂ : ℂ)
    (hgamma₁ : gamma₁ ≠ 0) (hgamma₂ : gamma₂ ≠ 0) :
    gammaBar₁ * gamma₂ - gammaBar₂ * gamma₁ =
      (gammaBar₁ / gamma₁ - gammaBar₂ / gamma₂) *
        (gamma₁ * gamma₂) := by
  field_simp

/-- A target denominator in a positive-shift cell has the common fixed-key
square-root bound. -/
private theorem complex_targetLinearForm_norm_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (ha : 0 < shiftedSquareA h v)
    {key : ShiftedSquareAuxiliaryKey}
    {cell : ComplexUnitCircleSlopeCellIndex}
    {z : GeneralBidegreeFormPoint}
    (hz : z ∈
      main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key (Sum.inr cell)) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let F := shiftedSquareFixedExplicitIntegralBasisData
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
    let sigma := shiftedSquareImaginaryPlaceEmbedding
      (shiftedSquareA h v) ha
    ‖main3IntegralTargetLinearForm (sigma F.omega)
        (shiftedSquareCoordinatePointTargetVector z)‖ ≤
      Real.sqrt (main3LargeAnalyticFixedKeyTargetScaleUpper Y key) := by
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
  let sigma := shiftedSquareImaginaryPlaceEmbedding
    (shiftedSquareA h v) ha
  have hzPackage : z = main3ShiftedSquarePackagePoint C.P :=
    hzPoint.trans (main3ShiftedSquarePackagePoint_eq C.P).symm
  have hden :=
    main3ShiftedSquarePackagePoint_targetDenominator_eq
      F C.P C.omega_eq sigma
  have htarget :=
    shiftedSquareEGamma_le_fixedKeyTargetScaleUpper
      C.scaled.base.target_dyadic.2 C.P
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
  rw [hlinear,
    shiftedSquare_imaginaryPlace_targetPrimitive_norm_eq_sqrt_EGamma ha C.P]
  rw [← hkey]
  exact Real.sqrt_le_sqrt htarget

/-- Two literal coordinate points in one positive-shift cell have target
wedge area bounded by the cell diameter times the fixed-key radial scale. -/
private theorem complex_coordinatePoint_targetWedge_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : ComplexUnitCircleSlopeCellIndex)
    (ha : 0 < shiftedSquareA h v)
    {z₁ z₂ : GeneralBidegreeFormPoint}
    (hz₁ : z₁ ∈
      main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key (Sum.inr cell))
    (hz₂ : z₂ ∈
      main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key (Sum.inr cell)) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    |(main3IntegralTargetWedge
        (shiftedSquareCoordinatePointTargetVector z₁)
        (shiftedSquareCoordinatePointTargetVector z₂) : ℝ)| *
        Real.sqrt
          |(NumberField.discr
            (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)| ≤
      6 * main3LargeAnalyticFixedKeyTargetScaleUpper Y key /
        (main3UnbalancedM theta Y : ℝ) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquareImaginaryPlaceEmbedding
    (shiftedSquareA h v) ha
  let y₁ := shiftedSquareCoordinatePointTargetVector z₁
  let y₂ := shiftedSquareCoordinatePointTargetVector z₂
  let gamma₁ := main3IntegralTargetLinearForm (sigma F.omega) y₁
  let gamma₂ := main3IntegralTargetLinearForm (sigma F.omega) y₂
  let gammaBar₁ :=
    main3IntegralTargetLinearForm (sigma (star F.omega)) y₁
  let gammaBar₂ :=
    main3IntegralTargetLinearForm (sigma (star F.omega)) y₂
  let q₁ := main3EmbeddingTargetRatio
    (sigma F.omega) (sigma (star F.omega)) z₁
  let q₂ := main3EmbeddingTargetRatio
    (sigma F.omega) (sigma (star F.omega)) z₂
  have hg₁ :=
    main3LargeAnalytic_complexCellCoordinatePointImage_embeddingRatio_geometry
      htheta hY hi key cell ha hz₁
  have hg₂ :=
    main3LargeAnalytic_complexCellCoordinatePointImage_embeddingRatio_geometry
      htheta hY hi key cell ha hz₂
  dsimp only at hg₁ hg₂
  have hgamma₁ : gamma₁ ≠ 0 := by
    simpa only [gamma₁, y₁, main3IntegralTargetLinearForm,
      shiftedSquareCoordinatePointTargetVector, Matrix.cons_val_zero,
      Matrix.cons_val_one, F, sigma] using hg₁.2.1
  have hgamma₂ : gamma₂ ≠ 0 := by
    simpa only [gamma₂, y₂, main3IntegralTargetLinearForm,
      shiftedSquareCoordinatePointTargetVector, Matrix.cons_val_zero,
      Matrix.cons_val_one, F, sigma] using hg₂.2.1
  have hq₁ : q₁ = gammaBar₁ / gamma₁ := by
    simp only [q₁, gammaBar₁, gamma₁, y₁,
      main3EmbeddingTargetRatio, main3IntegralTargetLinearForm,
      shiftedSquareCoordinatePointTargetVector, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  have hq₂ : q₂ = gammaBar₂ / gamma₂ := by
    simp only [q₂, gammaBar₂, gamma₂, y₂,
      main3EmbeddingTargetRatio, main3IntegralTargetLinearForm,
      shiftedSquareCoordinatePointTargetVector, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  obtain ⟨p, _hp, _hkey, hselector, _hgeometry, _hcode, _hpoint⟩ :=
    main3LargeAnalytic_blockCellCoordinatePointImage_sameCertificate
      htheta hY hi hz₁
  have hcellMem :=
    main3LargeAnalytic_blockPointArchimedeanCellSelector_mem
      htheta hY hi p
  rw [hselector] at hcellMem
  have hcell : cell ∈ complexUnitCircleSlopeCellIndices
      (main3UnbalancedM theta Y) :=
    mem_main3LargeAnalytic_archimedeanCellIndices_inr.mp hcellMem
  have hM : 0 < main3UnbalancedM theta Y :=
    lt_of_lt_of_le (by omega) (ten_le_main3UnbalancedM htheta hY)
  have hdist : ‖q₁ - q₂‖ ≤
      6 / (main3UnbalancedM theta Y : ℝ) := by
    exact norm_sub_le_six_div_of_mem_complexUnitCircleSquareTargetTube
      hM hcell hg₁.2.2.1.2 hg₂.2.2.1.2
  rw [hq₁, hq₂] at hdist
  have hnorm₁ : ‖gamma₁‖ ≤
      Real.sqrt (main3LargeAnalyticFixedKeyTargetScaleUpper Y key) := by
    simpa only [gamma₁, y₁, F, sigma] using
      complex_targetLinearForm_norm_le htheta hY hi ha hz₁
  have hnorm₂ : ‖gamma₂‖ ≤
      Real.sqrt (main3LargeAnalyticFixedKeyTargetScaleUpper Y key) := by
    simpa only [gamma₂, y₂, F, sigma] using
      complex_targetLinearForm_norm_le htheta hY hi ha hz₂
  have hscale : 0 ≤ main3LargeAnalyticFixedKeyTargetScaleUpper Y key := by
    unfold main3LargeAnalyticFixedKeyTargetScaleUpper
    positivity
  have hcross :
      ‖gammaBar₁ * gamma₂ - gammaBar₂ * gamma₁‖ ≤
        6 * main3LargeAnalyticFixedKeyTargetScaleUpper Y key /
          (main3UnbalancedM theta Y : ℝ) := by
    rw [targetLinearForm_cross_eq_ratioDifference_mul
      gammaBar₁ gamma₁ gammaBar₂ gamma₂ hgamma₁ hgamma₂,
      norm_mul, norm_mul]
    calc
      ‖gammaBar₁ / gamma₁ - gammaBar₂ / gamma₂‖ *
            (‖gamma₁‖ * ‖gamma₂‖) ≤
          (6 / (main3UnbalancedM theta Y : ℝ)) *
            (Real.sqrt (main3LargeAnalyticFixedKeyTargetScaleUpper Y key) *
              Real.sqrt (main3LargeAnalyticFixedKeyTargetScaleUpper Y key)) := by
        gcongr
      _ = 6 * main3LargeAnalyticFixedKeyTargetScaleUpper Y key /
          (main3UnbalancedM theta Y : ℝ) := by
        rw [← sq, Real.sq_sqrt hscale]
        ring
  have hwedge := norm_main3IntegralTargetLinearForm_wedge_eq F sigma y₁ y₂
  rw [← hwedge]
  simpa only [gammaBar₁, gammaBar₂, gamma₁, gamma₂, y₁, y₂]
    using hcross

/-- In a literal positive-shift fixed cell, any two retained integral target
vectors span a parallelogram of discriminant-weighted area at most
`6 E_gamma^+ / M`. -/
theorem main3LargeAnalyticFixedKeyComplexCellTargetVectorImage_wedge_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : ComplexUnitCircleSlopeCellIndex)
    (ha : 0 < shiftedSquareA h v)
    {y₁ y₂ : Fin 2 → ℤ}
    (hy₁ : y₁ ∈ main3LargeAnalyticFixedKeyCellTargetVectorImage
      htheta hY hi key (Sum.inr cell))
    (hy₂ : y₂ ∈ main3LargeAnalyticFixedKeyCellTargetVectorImage
      htheta hY hi key (Sum.inr cell)) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    |(main3IntegralTargetWedge y₁ y₂ : ℝ)| *
        Real.sqrt
          |(NumberField.discr
            (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)| ≤
      6 * main3LargeAnalyticFixedKeyTargetScaleUpper Y key /
        (main3UnbalancedM theta Y : ℝ) := by
  obtain ⟨z₁, hz₁, rfl⟩ :=
    (mem_main3LargeAnalyticFixedKeyCellTargetVectorImage_iff
      htheta hY hi key (Sum.inr cell) y₁).mp hy₁
  obtain ⟨z₂, hz₂, rfl⟩ :=
    (mem_main3LargeAnalyticFixedKeyCellTargetVectorImage_iff
      htheta hY hi key (Sum.inr cell) y₂).mp hy₂
  exact complex_coordinatePoint_targetWedge_le
    htheta hY hi key cell ha hz₁ hz₂

/-- Two real targets in the same literal target interval differ by at most
the square of the common centre divided by the mesh parameter. -/
private theorem abs_sub_le_sq_div_of_mem_realSquareMapTargetCell
    {M s : ℝ} (hM : 0 < M) (hs : 0 < s) {k : ℤ} {r₁ r₂ : ℝ}
    (hr₁ : realSquareMapTargetCell M s k r₁)
    (hr₂ : realSquareMapTargetCell M s k r₂) :
    |r₁ - r₂| ≤ s ^ 2 / M := by
  have hupper : M * (r₁ / s ^ 2 - r₂ / s ^ 2) ≤ 1 := by
    have hrewrite : M * (r₁ / s ^ 2 - r₂ / s ^ 2) =
        M * (r₁ / s ^ 2 - 1) - M * (r₂ / s ^ 2 - 1) := by ring
    rw [hrewrite]
    linarith [hr₁.2, hr₂.1]
  have hlower : -(1 : ℝ) ≤
      M * (r₁ / s ^ 2 - r₂ / s ^ 2) := by
    have hrewrite : M * (r₁ / s ^ 2 - r₂ / s ^ 2) =
        M * (r₁ / s ^ 2 - 1) - M * (r₂ / s ^ 2 - 1) := by ring
    rw [hrewrite]
    linarith [hr₁.1, hr₂.2]
  have hnormalized : |r₁ / s ^ 2 - r₂ / s ^ 2| ≤ 1 / M := by
    rw [abs_le]
    constructor
    · rw [show -(1 / M) = (-1 : ℝ) / M by ring]
      apply (div_le_iff₀ hM).2
      nlinarith
    · apply (le_div_iff₀ hM).2
      nlinarith
  have hsSq : 0 ≤ s ^ 2 := sq_nonneg s
  have hrewrite : r₁ - r₂ =
      s ^ 2 * (r₁ / s ^ 2 - r₂ / s ^ 2) := by
    field_simp [hs.ne']
  calc
    |r₁ - r₂| = s ^ 2 * |r₁ / s ^ 2 - r₂ / s ^ 2| := by
      rw [hrewrite, abs_mul, abs_of_nonneg hsSq]
    _ ≤ s ^ 2 * (1 / M) :=
      mul_le_mul_of_nonneg_left hnormalized hsSq
    _ = s ^ 2 / M := by ring

/-- The lower endpoint `k ≥ -1` and `M ≥ 6` keep every normalized
target coordinate in a selected real target cell above `1/2`. -/
private theorem one_half_le_normalized_of_mem_realSquareMapTargetCell
    {M s r : ℝ} (hM : 6 ≤ M) {k : ℤ}
    (hk : (-1 : ℤ) ≤ k)
    (hr : realSquareMapTargetCell M s k r) :
    (1 / 2 : ℝ) ≤ r / s ^ 2 := by
  have hMpos : 0 < M := by linarith
  have hkReal : (-1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hraw : (-2 : ℝ) < M * (r / s ^ 2 - 1) := by
    linarith [hr.1]
  have hminusThird : (-1 / 3 : ℝ) ≤ -2 / M := by
    apply (le_div_iff₀ hMpos).2
    nlinarith
  have hquot : -2 / M < r / s ^ 2 - 1 := by
    exact (div_lt_iff₀ hMpos).2 (by simpa [mul_comm] using hraw)
  linarith

/-- At the positive real place, the square of a target denominator times the
square of its cell centre is at most twice the fixed-key target scale. -/
private theorem real_targetLinearForm_center_sq_norm_sq_le
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
    let centre := annularMultiplicativeCenter
      (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
      (main3UnbalancedM theta Y) cell.1.2.1 cell.1.2.2
    centre ^ 2 *
        ‖main3IntegralTargetLinearForm (sigma F.omega)
          (shiftedSquareCoordinatePointTargetVector z)‖ ^ 2 ≤
      2 * main3LargeAnalyticFixedKeyTargetScaleUpper Y key := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding
    (shiftedSquareA h v) ha
  let centre := annularMultiplicativeCenter
    (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
    (main3UnbalancedM theta Y) cell.1.2.1 cell.1.2.2
  let y := shiftedSquareCoordinatePointTargetVector z
  let gamma := main3IntegralTargetLinearForm (sigma F.omega) y
  let gammaBar := main3IntegralTargetLinearForm (sigma (star F.omega)) y
  let q := main3EmbeddingTargetRatio
    (sigma F.omega) (sigma (star F.omega)) z
  have hg :=
    main3LargeAnalytic_realCellCoordinatePointImage_embeddingRatio_geometry
      htheta hY hi key cell ha hz
  dsimp only at hg
  rcases hg with
    ⟨⟨_hsourceDen, htargetDen, _hsourceIm, htargetIm,
      _hsourceNe, htargetPos⟩, hcellGeometry⟩
  have hgamma : gamma ≠ 0 := by
    simpa only [gamma, y, main3IntegralTargetLinearForm,
      shiftedSquareCoordinatePointTargetVector, Matrix.cons_val_zero,
      Matrix.cons_val_one, F, sigma] using htargetDen
  have hq : q = gammaBar / gamma := by
    simp only [q, gammaBar, gamma, y, main3EmbeddingTargetRatio,
      main3IntegralTargetLinearForm, shiftedSquareCoordinatePointTargetVector,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  have hqReal : q = ((q.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]
      simpa only [q] using htargetIm
  have hratioReal : gammaBar / gamma = ((q.re : ℝ) : ℂ) :=
    hq.symm.trans hqReal
  have htargetNorm := congrArg norm hratioReal
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by simpa only [q] using htargetPos)] at htargetNorm
  have hgammaNorm : ‖gamma‖ ≠ 0 := norm_ne_zero_iff.mpr hgamma
  have hgammaBarMul : ‖gammaBar‖ = q.re * ‖gamma‖ := by
    apply (div_eq_iff hgammaNorm).mp
    simpa only [mul_comm] using htargetNorm
  obtain ⟨p, _hp, hkey, hselector, _hgeometry, _hcode, hzPoint⟩ :=
    main3LargeAnalytic_blockCellCoordinatePointImage_sameCertificate
      htheta hY hi hz
  let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta (by omega : 8 ≤ Y) hi p
  have hzPackage : z = main3ShiftedSquarePackagePoint C.P :=
    hzPoint.trans (main3ShiftedSquarePackagePoint_eq C.P).symm
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
  obtain ⟨_hdpos, hwpos, _hnpos, _hdLower, _hdUpper,
      _hwLower, hwUpper, _hNn, _hnUpper, _heq, _hsf⟩ :=
    mem_squarefreeShiftedSquareBlock.mp p.2
  have hproduct : ‖gamma‖ * ‖gammaBar‖ = shiftedSquareEGamma C.P := by
    rw [hlinear, hlinearBar]
    exact shiftedSquare_positiveRealPlace_target_norm_mul_eq_EGamma
      ha hwpos C.P
  have henergy : q.re * ‖gamma‖ ^ 2 = shiftedSquareEGamma C.P := by
    rw [← hproduct, hgammaBarMul]
    ring
  have hcellMem :=
    main3LargeAnalytic_blockPointArchimedeanCellSelector_mem
      htheta hY hi p
  rw [hselector] at hcellMem
  have hpairMem :=
    mem_main3LargeAnalytic_archimedeanCellIndices_inl.mp hcellMem
  have hoffset : cell.2 ∈ realSquareMapTargetOffsets := by
    exact (Finset.mem_product.mp hpairMem).2
  have hk : (-1 : ℤ) ≤ cell.2 :=
    (Finset.mem_Icc.mp (by
      simpa only [realSquareMapTargetOffsets] using hoffset)).1
  have hF : 1 ≤ shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v) := by
    have haOne : (1 : ℝ) ≤ |(shiftedSquareA h v : ℝ)| := by
      exact_mod_cast Int.one_le_abs (ne_of_lt ha)
    unfold shiftedSquareEmbeddingScaleLoss
    nlinarith
  have hcentre : 0 < centre := by
    dsimp only [centre, annularMultiplicativeCenter]
    exact mul_pos
      (annularDyadicStart_pos hF cell.1.2.1)
      (pow_pos (by unfold localRatioMeshStep; positivity) _)
  have hM : (6 : ℝ) ≤ main3UnbalancedM theta Y := by
    exact_mod_cast six_le_main3UnbalancedM htheta hY
  have htargetCell : realSquareMapTargetCell
      (main3UnbalancedM theta Y : ℝ) centre cell.2 q.re := by
    simpa only [Prod.snd, q, centre] using hcellGeometry.2
  have hnormalized : (1 / 2 : ℝ) ≤ q.re / centre ^ 2 :=
    one_half_le_normalized_of_mem_realSquareMapTargetCell
      hM hk htargetCell
  have hcentreSq : 0 ≤ centre ^ 2 := sq_nonneg centre
  have hnormSq : 0 ≤ ‖gamma‖ ^ 2 := sq_nonneg _
  have hscaledEnergy :
      centre ^ 2 * ‖gamma‖ ^ 2 * (q.re / centre ^ 2) =
        shiftedSquareEGamma C.P := by
    calc
      centre ^ 2 * ‖gamma‖ ^ 2 * (q.re / centre ^ 2) =
          q.re * ‖gamma‖ ^ 2 := by
        field_simp [hcentre.ne']
      _ = shiftedSquareEGamma C.P := henergy
  have htargetUpper :=
    shiftedSquareEGamma_le_fixedKeyTargetScaleUpper hwUpper C.P
  have hradial : centre ^ 2 * ‖gamma‖ ^ 2 ≤
      2 * shiftedSquareEGamma C.P := by
    have hx : 0 ≤ centre ^ 2 * ‖gamma‖ ^ 2 :=
      mul_nonneg hcentreSq hnormSq
    calc
      centre ^ 2 * ‖gamma‖ ^ 2 ≤
          2 * (centre ^ 2 * ‖gamma‖ ^ 2 *
            (q.re / centre ^ 2)) := by
        nlinarith [mul_nonneg hx (sub_nonneg.mpr hnormalized)]
      _ = 2 * shiftedSquareEGamma C.P := by rw [hscaledEnergy]
  calc
    centre ^ 2 * ‖gamma‖ ^ 2 ≤ 2 * shiftedSquareEGamma C.P := hradial
    _ ≤ 2 * main3LargeAnalyticFixedKeyTargetScaleUpper Y key := by
      rw [← hkey]
      gcongr

/-- Two literal coordinate points in one negative-shift real cell have target
wedge area bounded by the target-interval width times the fixed-key radial
scale. -/
private theorem real_coordinatePoint_targetWedge_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : RealSquareMapCellPairIndex)
    (ha : shiftedSquareA h v < 0)
    {z₁ z₂ : GeneralBidegreeFormPoint}
    (hz₁ : z₁ ∈
      main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key (Sum.inl cell))
    (hz₂ : z₂ ∈
      main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key (Sum.inl cell)) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    |(main3IntegralTargetWedge
        (shiftedSquareCoordinatePointTargetVector z₁)
        (shiftedSquareCoordinatePointTargetVector z₂) : ℝ)| *
        Real.sqrt
          |(NumberField.discr
            (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)| ≤
      2 * main3LargeAnalyticFixedKeyTargetScaleUpper Y key /
        (main3UnbalancedM theta Y : ℝ) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding
    (shiftedSquareA h v) ha
  let centre := annularMultiplicativeCenter
    (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
    (main3UnbalancedM theta Y) cell.1.2.1 cell.1.2.2
  let y₁ := shiftedSquareCoordinatePointTargetVector z₁
  let y₂ := shiftedSquareCoordinatePointTargetVector z₂
  let gamma₁ := main3IntegralTargetLinearForm (sigma F.omega) y₁
  let gamma₂ := main3IntegralTargetLinearForm (sigma F.omega) y₂
  let gammaBar₁ :=
    main3IntegralTargetLinearForm (sigma (star F.omega)) y₁
  let gammaBar₂ :=
    main3IntegralTargetLinearForm (sigma (star F.omega)) y₂
  let q₁ := main3EmbeddingTargetRatio
    (sigma F.omega) (sigma (star F.omega)) z₁
  let q₂ := main3EmbeddingTargetRatio
    (sigma F.omega) (sigma (star F.omega)) z₂
  have hg₁ :=
    main3LargeAnalytic_realCellCoordinatePointImage_embeddingRatio_geometry
      htheta hY hi key cell ha hz₁
  have hg₂ :=
    main3LargeAnalytic_realCellCoordinatePointImage_embeddingRatio_geometry
      htheta hY hi key cell ha hz₂
  dsimp only at hg₁ hg₂
  rcases hg₁ with
    ⟨⟨_hsourceDen₁, htargetDen₁, _hsourceIm₁, htargetIm₁,
      _hsourceNe₁, _htargetPos₁⟩, hcellGeometry₁⟩
  rcases hg₂ with
    ⟨⟨_hsourceDen₂, htargetDen₂, _hsourceIm₂, htargetIm₂,
      _hsourceNe₂, _htargetPos₂⟩, hcellGeometry₂⟩
  have hgamma₁ : gamma₁ ≠ 0 := by
    simpa only [gamma₁, y₁, main3IntegralTargetLinearForm,
      shiftedSquareCoordinatePointTargetVector, Matrix.cons_val_zero,
      Matrix.cons_val_one, F, sigma] using htargetDen₁
  have hgamma₂ : gamma₂ ≠ 0 := by
    simpa only [gamma₂, y₂, main3IntegralTargetLinearForm,
      shiftedSquareCoordinatePointTargetVector, Matrix.cons_val_zero,
      Matrix.cons_val_one, F, sigma] using htargetDen₂
  have hq₁ : q₁ = gammaBar₁ / gamma₁ := by
    simp only [q₁, gammaBar₁, gamma₁, y₁,
      main3EmbeddingTargetRatio, main3IntegralTargetLinearForm,
      shiftedSquareCoordinatePointTargetVector, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  have hq₂ : q₂ = gammaBar₂ / gamma₂ := by
    simp only [q₂, gammaBar₂, gamma₂, y₂,
      main3EmbeddingTargetRatio, main3IntegralTargetLinearForm,
      shiftedSquareCoordinatePointTargetVector, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  have hqReal₁ : q₁ = ((q₁.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]
      simpa only [q₁] using htargetIm₁
  have hqReal₂ : q₂ = ((q₂.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]
      simpa only [q₂] using htargetIm₂
  have hF : 1 ≤ shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v) := by
    have haOne : (1 : ℝ) ≤ |(shiftedSquareA h v : ℝ)| := by
      exact_mod_cast Int.one_le_abs (ne_of_lt ha)
    unfold shiftedSquareEmbeddingScaleLoss
    nlinarith
  have hcentre : 0 < centre := by
    dsimp only [centre, annularMultiplicativeCenter]
    exact mul_pos
      (annularDyadicStart_pos hF cell.1.2.1)
      (pow_pos (by unfold localRatioMeshStep; positivity) _)
  have hMNat : 0 < main3UnbalancedM theta Y :=
    lt_of_lt_of_le (by omega) (six_le_main3UnbalancedM htheta hY)
  have hM : (0 : ℝ) < main3UnbalancedM theta Y := by exact_mod_cast hMNat
  have htargetCell₁ : realSquareMapTargetCell
      (main3UnbalancedM theta Y : ℝ) centre cell.2 q₁.re := by
    simpa only [Prod.snd, q₁, centre] using hcellGeometry₁.2
  have htargetCell₂ : realSquareMapTargetCell
      (main3UnbalancedM theta Y : ℝ) centre cell.2 q₂.re := by
    simpa only [Prod.snd, q₂, centre] using hcellGeometry₂.2
  have hdistRe : |q₁.re - q₂.re| ≤
      centre ^ 2 / (main3UnbalancedM theta Y : ℝ) :=
    abs_sub_le_sq_div_of_mem_realSquareMapTargetCell
      hM hcentre htargetCell₁ htargetCell₂
  have hdist : ‖q₁ - q₂‖ ≤
      centre ^ 2 / (main3UnbalancedM theta Y : ℝ) := by
    rw [hqReal₁, hqReal₂, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    exact hdistRe
  rw [hq₁, hq₂] at hdist
  have hradial₁ : centre ^ 2 * ‖gamma₁‖ ^ 2 ≤
      2 * main3LargeAnalyticFixedKeyTargetScaleUpper Y key := by
    simpa only [centre, gamma₁, y₁, F, sigma] using
      real_targetLinearForm_center_sq_norm_sq_le
        htheta hY hi key cell ha hz₁
  have hradial₂ : centre ^ 2 * ‖gamma₂‖ ^ 2 ≤
      2 * main3LargeAnalyticFixedKeyTargetScaleUpper Y key := by
    simpa only [centre, gamma₂, y₂, F, sigma] using
      real_targetLinearForm_center_sq_norm_sq_le
        htheta hY hi key cell ha hz₂
  have hradialProduct : centre ^ 2 * ‖gamma₁‖ * ‖gamma₂‖ ≤
      2 * main3LargeAnalyticFixedKeyTargetScaleUpper Y key := by
    nlinarith [sq_nonneg (centre * ‖gamma₁‖ - centre * ‖gamma₂‖)]
  have hcross :
      ‖gammaBar₁ * gamma₂ - gammaBar₂ * gamma₁‖ ≤
        2 * main3LargeAnalyticFixedKeyTargetScaleUpper Y key /
          (main3UnbalancedM theta Y : ℝ) := by
    rw [targetLinearForm_cross_eq_ratioDifference_mul
      gammaBar₁ gamma₁ gammaBar₂ gamma₂ hgamma₁ hgamma₂,
      norm_mul, norm_mul]
    calc
      ‖gammaBar₁ / gamma₁ - gammaBar₂ / gamma₂‖ *
            (‖gamma₁‖ * ‖gamma₂‖) ≤
          (centre ^ 2 / (main3UnbalancedM theta Y : ℝ)) *
            (‖gamma₁‖ * ‖gamma₂‖) := by
        gcongr
      _ = (centre ^ 2 * ‖gamma₁‖ * ‖gamma₂‖) /
          (main3UnbalancedM theta Y : ℝ) := by ring
      _ ≤ (2 * main3LargeAnalyticFixedKeyTargetScaleUpper Y key) /
          (main3UnbalancedM theta Y : ℝ) := by
        exact div_le_div_of_nonneg_right hradialProduct hM.le
  have hwedge := norm_main3IntegralTargetLinearForm_wedge_eq F sigma y₁ y₂
  rw [← hwedge]
  simpa only [gammaBar₁, gammaBar₂, gamma₁, gamma₂, y₁, y₂]
    using hcross

/-- In a literal negative-shift fixed cell, any two retained integral target
vectors span a parallelogram of discriminant-weighted area at most
`2 E_gamma^+ / M`. -/
theorem main3LargeAnalyticFixedKeyRealCellTargetVectorImage_wedge_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : RealSquareMapCellPairIndex)
    (ha : shiftedSquareA h v < 0)
    {y₁ y₂ : Fin 2 → ℤ}
    (hy₁ : y₁ ∈ main3LargeAnalyticFixedKeyCellTargetVectorImage
      htheta hY hi key (Sum.inl cell))
    (hy₂ : y₂ ∈ main3LargeAnalyticFixedKeyCellTargetVectorImage
      htheta hY hi key (Sum.inl cell)) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    |(main3IntegralTargetWedge y₁ y₂ : ℝ)| *
        Real.sqrt
          |(NumberField.discr
            (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)| ≤
      2 * main3LargeAnalyticFixedKeyTargetScaleUpper Y key /
        (main3UnbalancedM theta Y : ℝ) := by
  obtain ⟨z₁, hz₁, rfl⟩ :=
    (mem_main3LargeAnalyticFixedKeyCellTargetVectorImage_iff
      htheta hY hi key (Sum.inl cell) y₁).mp hy₁
  obtain ⟨z₂, hz₂, rfl⟩ :=
    (mem_main3LargeAnalyticFixedKeyCellTargetVectorImage_iff
      htheta hY hi key (Sum.inl cell) y₂).mp hy₂
  exact real_coordinatePoint_targetWedge_le
    htheta hY hi key cell ha hz₁ hz₂

end

end PellPaper
