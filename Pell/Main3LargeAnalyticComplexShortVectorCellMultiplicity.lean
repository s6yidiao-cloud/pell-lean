import Pell.ComplexUnitCircleSlopeCellShortVectorMultiplicity
import Pell.ShiftedSquareComplexIntegralLatticeBallGrowth
import Pell.Main3LargeAnalyticComplexCoverShortestVectorBound
import Mathlib.Tactic

/-!
# Main3 complex short-vector cell multiplicity candidate

This file connects the geometric four-chart packing estimate to the literal
quadratic-order direction of a complex target vector.
-/

namespace PellPaper

open scoped ComplexConjugate MatrixGroups

noncomputable section

local instance main3LargeAnalyticComplexShortVectorCellMultiplicity_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- A sharp cross-product bound controls the distance between the two unit
quadratic-order directions.  The asymmetric anchor bounds are exactly those
provided by the complex Main3 radial certificate. -/
theorem norm_anchorDirection_sub_shortVectorDirection_le
    {anchorValue yValue : ℂ} {E M mu : ℝ}
    (hE : 0 < E) (hM : 0 < M) (hmu : 0 ≤ mu)
    (hanchor : anchorValue ≠ 0) (hy : yValue ≠ 0)
    (hanchorLower : E ≤ 2 * ‖anchorValue‖ ^ 2)
    (hanchorUpper : ‖anchorValue‖ ^ 2 ≤ E)
    (hcross : ‖conj anchorValue * yValue -
        conj yValue * anchorValue‖ ≤ 3 * E * mu / M) :
    ‖conj anchorValue / anchorValue - conj yValue / yValue‖ ≤
      6 * Real.sqrt E * mu / (M * ‖yValue‖) := by
  have hanchorNorm : 0 < ‖anchorValue‖ := norm_pos_iff.mpr hanchor
  have hyNorm : 0 < ‖yValue‖ := norm_pos_iff.mpr hy
  have hsqrt : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  have hanchorNorm_le : ‖anchorValue‖ ≤ Real.sqrt E :=
    (Real.le_sqrt (norm_nonneg _) hE.le).2 hanchorUpper
  have hEdiv : E / ‖anchorValue‖ ≤ 2 * Real.sqrt E := by
    apply (div_le_iff₀ hanchorNorm).2
    calc
      E ≤ 2 * ‖anchorValue‖ ^ 2 := hanchorLower
      _ ≤ (2 * Real.sqrt E) * ‖anchorValue‖ := by
        nlinarith [norm_nonneg anchorValue]
  rw [norm_conj_div_self_sub_conj_div_self_eq hanchor hy]
  have hdenom : 0 < ‖anchorValue‖ * ‖yValue‖ :=
    mul_pos hanchorNorm hyNorm
  calc
    ‖conj anchorValue * yValue - conj yValue * anchorValue‖ /
          (‖anchorValue‖ * ‖yValue‖) ≤
        (3 * E * mu / M) / (‖anchorValue‖ * ‖yValue‖) := by
      exact div_le_div_of_nonneg_right hcross hdenom.le
    _ = (3 * mu / (M * ‖yValue‖)) * (E / ‖anchorValue‖) := by
      field_simp [hM.ne', hanchorNorm.ne', hyNorm.ne']
    _ ≤ (3 * mu / (M * ‖yValue‖)) * (2 * Real.sqrt E) := by
      gcongr
    _ = 6 * Real.sqrt E * mu / (M * ‖yValue‖) := by ring

/-- Reciprocal-minimum band form of the preceding direction estimate. -/
theorem norm_anchorDirection_sub_shortVectorDirection_le_of_reciprocalBand
    {anchorValue yValue : ℂ} {E M mu S : ℝ}
    (hE : 0 < E) (hM : 0 < M) (hmu : 0 < mu) (hS : 0 < S)
    (hband : S ≤ 1 / mu)
    (hanchor : anchorValue ≠ 0) (hy : yValue ≠ 0)
    (hanchorLower : E ≤ 2 * ‖anchorValue‖ ^ 2)
    (hanchorUpper : ‖anchorValue‖ ^ 2 ≤ E)
    (hcross : ‖conj anchorValue * yValue -
        conj yValue * anchorValue‖ ≤ 3 * E * mu / M) :
    ‖conj anchorValue / anchorValue - conj yValue / yValue‖ ≤
      (6 * Real.sqrt E / (S * ‖yValue‖)) / M := by
  have hmuUpper : mu ≤ 1 / S := by
    apply (le_div_iff₀ hS).2
    have hprod := (le_div_iff₀ hmu).1 hband
    simpa only [one_mul, mul_comm] using hprod
  have hdirect := norm_anchorDirection_sub_shortVectorDirection_le
    hE hM hmu.le hanchor hy hanchorLower hanchorUpper hcross
  calc
    ‖conj anchorValue / anchorValue - conj yValue / yValue‖ ≤
        6 * Real.sqrt E * mu / (M * ‖yValue‖) := hdirect
    _ ≤ 6 * Real.sqrt E * (1 / S) / (M * ‖yValue‖) := by
      gcongr
    _ = (6 * Real.sqrt E / (S * ‖yValue‖)) / M := by ring

/-- The normalized wedge coordinate of the exact reduced-cover shortest
vector gives the sharper cross-product bound before the mesh-size estimate is
coarsened away. -/
theorem PrimitiveWedgeReducedTargetCoverSpec.complex_shortest_cross_norm_le
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (ha : 0 < a)
    {T : Finset (Fin 2 → ℤ)} {E Mmesh : ℝ}
    (hE : 0 < E) (hMmesh : 0 < Mmesh)
    (cert : PrimitiveWedgeReducedTargetCoverCertificate T E
      ((6 * E / Mmesh) /
        Real.sqrt |(NumberField.discr
          (rationalQuadraticAlgebra (-a)) : ℝ)|) 2)
    {G H : SL(2, ℤ)}
    (hspec : PrimitiveWedgeReducedTargetCoverSpec
      T cert.ell cert.anchor E
        ((6 * E / Mmesh) /
          Real.sqrt |(NumberField.discr
            (rationalQuadraticAlgebra (-a)) : ℝ)|) 2 G H) :
    let Delta := Real.sqrt |(NumberField.discr
      (rationalQuadraticAlgebra (-a)) : ℝ)|
    let K := (6 * E / Mmesh) / Delta
    let rho := cert.ell cert.anchor
    let U := K / 2
    let V := 1 + (2 : ℝ) / 2
    let M₀ := 2 * rho * V / E
    let beta := cert.ell (fun i ↦ G i 1)
    let z := -K * beta / E
    let mu := firstSlopeSupNorm U V M₀ z
    let y := primitiveWedgeReducedTargetCoverShortestVector G H
    let anchorValue := main3IntegralTargetLinearForm
      (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) cert.anchor
    let yValue := main3IntegralTargetLinearForm
      (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y
    ‖conj anchorValue * yValue - conj yValue * anchorValue‖ ≤
      3 * E * mu / Mmesh := by
  dsimp only
  let sigma := shiftedSquareImaginaryPlaceEmbedding a ha
  let Delta := Real.sqrt |(NumberField.discr
    (rationalQuadraticAlgebra (-a)) : ℝ)|
  let K := (6 * E / Mmesh) / Delta
  let rho := cert.ell cert.anchor
  let U := K / 2
  let V := 1 + (2 : ℝ) / 2
  let M₀ := 2 * rho * V / E
  let beta := cert.ell (fun i ↦ G i 1)
  let z := -K * beta / E
  let mu := firstSlopeSupNorm U V M₀ z
  let y := primitiveWedgeReducedTargetCoverShortestVector G H
  let anchorValue := main3IntegralTargetLinearForm (sigma F.omega) cert.anchor
  let yValue := main3IntegralTargetLinearForm (sigma F.omega) y
  have hdiscZ : NumberField.discr (rationalQuadraticAlgebra (-a)) ≠ 0 :=
    NumberField.discr_ne_zero _
  have hdiscR :
      (NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ) ≠ 0 := by
    exact_mod_cast hdiscZ
  have hDelta : 0 < Delta := by
    dsimp only [Delta]
    exact Real.sqrt_pos.2 (abs_pos.mpr hdiscR)
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hshort := hspec.shortest_original_vector
  dsimp only at hshort
  change y ≠ 0 ∧ IsCoprime (y 0) (y 1) ∧
    max |2 * cert.ell y / E|
      |2 * (main3IntegralTargetWedge cert.anchor y : ℝ) / K| = mu at hshort
  have hmu : 0 ≤ mu := by
    rw [← hshort.2.2]
    exact (abs_nonneg _).trans (le_max_left _ _)
  have hwedgeNormalized :
      |2 * (main3IntegralTargetWedge cert.anchor y : ℝ) / K| ≤ mu := by
    rw [← hshort.2.2]
    exact le_max_right _ _
  have hwedge : |(main3IntegralTargetWedge cert.anchor y : ℝ)| ≤
      K * mu / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hK,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hwedgeNormalized
    have hscaled := (div_le_iff₀ hK).mp hwedgeNormalized
    nlinarith
  have hcrossEq :
      ‖conj anchorValue * yValue - conj yValue * anchorValue‖ =
        |(main3IntegralTargetWedge cert.anchor y : ℝ)| * Delta := by
    have hwedgeNorm :=
      norm_main3IntegralTargetLinearForm_wedge_eq F sigma cert.anchor y
    simpa only [sigma, Delta, anchorValue, yValue,
      main3IntegralTargetLinearForm_imaginaryPlace_star_eq_conj] using
        hwedgeNorm
  rw [hcrossEq]
  calc
    |(main3IntegralTargetWedge cert.anchor y : ℝ)| * Delta ≤
        (K * mu / 2) * Delta :=
      mul_le_mul_of_nonneg_right hwedge hDelta.le
    _ = 3 * E * mu / Mmesh := by
      dsimp only [K]
      field_simp [hDelta.ne', hMmesh.ne']
      ring

/-- In a reciprocal-minimum band, the exact shortest vector forces the
anchor's unit target direction into a `delta/Mmesh` neighborhood of the
short-vector direction, with `delta = 6*sqrt(E)/(S*||y||)`. -/
theorem PrimitiveWedgeReducedTargetCoverSpec.complex_shortest_direction_le_of_reciprocalBand
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (ha : 0 < a)
    {T : Finset (Fin 2 → ℤ)} {E Mmesh S : ℝ}
    (hE : 0 < E) (hMmesh : 0 < Mmesh) (hS : 0 < S)
    (cert : PrimitiveWedgeReducedTargetCoverCertificate T E
      ((6 * E / Mmesh) /
        Real.sqrt |(NumberField.discr
          (rationalQuadraticAlgebra (-a)) : ℝ)|) 2)
    (hell : cert.ell = main3AnchorHermitianRadialAddHom 1
      (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) cert.anchor)
    (hrhoLower : E ≤ 2 * cert.ell cert.anchor)
    (hrhoUpper : cert.ell cert.anchor ≤ E)
    {G H : SL(2, ℤ)}
    (hspec : PrimitiveWedgeReducedTargetCoverSpec
      T cert.ell cert.anchor E
        ((6 * E / Mmesh) /
          Real.sqrt |(NumberField.discr
            (rationalQuadraticAlgebra (-a)) : ℝ)|) 2 G H)
    (hband : S ≤ 1 /
      firstSlopeSupNorm
        (((6 * E / Mmesh) /
          Real.sqrt |(NumberField.discr
            (rationalQuadraticAlgebra (-a)) : ℝ)|) / 2)
        (1 + (2 : ℝ) / 2)
        (2 * cert.ell cert.anchor * (1 + (2 : ℝ) / 2) / E)
        (-((6 * E / Mmesh) /
          Real.sqrt |(NumberField.discr
            (rationalQuadraticAlgebra (-a)) : ℝ)|) *
          cert.ell (fun i ↦ G i 1) / E)) :
    let y := primitiveWedgeReducedTargetCoverShortestVector G H
    let anchorValue := main3IntegralTargetLinearForm
      (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) cert.anchor
    let yValue := main3IntegralTargetLinearForm
      (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y
    ‖conj anchorValue / anchorValue - conj yValue / yValue‖ ≤
      (6 * Real.sqrt E / (S * ‖yValue‖)) / Mmesh := by
  dsimp only
  let sigma := shiftedSquareImaginaryPlaceEmbedding a ha
  let Delta := Real.sqrt |(NumberField.discr
    (rationalQuadraticAlgebra (-a)) : ℝ)|
  let K := (6 * E / Mmesh) / Delta
  let rho := cert.ell cert.anchor
  let U := K / 2
  let V := 1 + (2 : ℝ) / 2
  let M₀ := 2 * rho * V / E
  let beta := cert.ell (fun i ↦ G i 1)
  let z := -K * beta / E
  let mu := firstSlopeSupNorm U V M₀ z
  let y := primitiveWedgeReducedTargetCoverShortestVector G H
  let anchorValue := main3IntegralTargetLinearForm (sigma F.omega) cert.anchor
  let yValue := main3IntegralTargetLinearForm (sigma F.omega) y
  have hshort := hspec.shortest_original_vector
  dsimp only at hshort
  change y ≠ 0 ∧ IsCoprime (y 0) (y 1) ∧
    max |2 * cert.ell y / E|
      |2 * (main3IntegralTargetWedge cert.anchor y : ℝ) / K| = mu at hshort
  have hyNormOne :=
    one_le_norm_main3IntegralTargetLinearForm_fixedBasis_imaginaryPlace
      ha F y hshort.1
  have hyValue : yValue ≠ 0 := by
    intro hyzero
    have : ‖yValue‖ = 0 := norm_eq_zero.mpr hyzero
    linarith
  have hellAnchor : cert.ell cert.anchor = ‖anchorValue‖ ^ 2 := by
    calc
      cert.ell cert.anchor =
          main3AnchorHermitianRadialAddHom 1
            (sigma F.omega) cert.anchor cert.anchor := by rw [hell]
      _ = 1 * ‖main3IntegralTargetLinearForm
          (sigma F.omega) cert.anchor‖ ^ 2 :=
        main3AnchorHermitianRadialAddHom_self 1
          (sigma F.omega) cert.anchor
      _ = ‖anchorValue‖ ^ 2 := by simp only [one_mul, anchorValue]
  have hanchorValue : anchorValue ≠ 0 := by
    intro hzero
    have hnormzero : ‖anchorValue‖ = 0 := norm_eq_zero.mpr hzero
    have hpos := cert.anchor_pos
    rw [hellAnchor, hnormzero, zero_pow (by omega : 2 ≠ 0)] at hpos
    exact lt_irrefl 0 hpos
  have hanchorLower : E ≤ 2 * ‖anchorValue‖ ^ 2 := by
    rw [← hellAnchor]
    exact hrhoLower
  have hanchorUpper : ‖anchorValue‖ ^ 2 ≤ E := by
    rw [← hellAnchor]
    exact hrhoUpper
  have hmu : 0 < mu := by
    unfold PrimitiveWedgeReducedTargetCoverSpec at hspec
    dsimp only at hspec
    exact hspec.2.2.2.2.1
  have hcross := hspec.complex_shortest_cross_norm_le
    F ha hE hMmesh cert
  exact norm_anchorDirection_sub_shortVectorDirection_le_of_reciprocalBand
    hE hMmesh hmu hS hband hanchorValue hyValue hanchorLower
      hanchorUpper hcross

/-- Every target vector in a nonempty positive-shift cell has its unit
quadratic-order direction in that cell's literal target tube. -/
theorem main3LargeAnalyticFixedKeyComplexCellTargetVector_direction_mem_tube
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
    let gamma := main3IntegralTargetLinearForm (sigma F.omega) y
    InComplexUnitCircleSquareTargetTube
      (main3UnbalancedM theta Y) cell (conj gamma / gamma) := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquareImaginaryPlaceEmbedding
    (shiftedSquareA h v) ha
  obtain ⟨z, hz, hyz⟩ :=
    (mem_main3LargeAnalyticFixedKeyCellTargetVectorImage_iff
      htheta hY hi key (Sum.inr cell) y).mp hy
  have hg :=
    main3LargeAnalytic_complexCellCoordinatePointImage_embeddingRatio_geometry
      htheta hY hi key cell ha hz
  dsimp only at hg
  have htube := hg.2.2.1.2
  have htarget :
      main3EmbeddingTargetRatio (sigma F.omega) (sigma (star F.omega)) z =
        conj (main3IntegralTargetLinearForm (sigma F.omega) y) /
          main3IntegralTargetLinearForm (sigma F.omega) y := by
    rw [← hyz]
    change
      main3IntegralTargetLinearForm (sigma (star F.omega))
            (shiftedSquareCoordinatePointTargetVector z) /
          main3IntegralTargetLinearForm (sigma F.omega)
            (shiftedSquareCoordinatePointTargetVector z) = _
    rw [main3IntegralTargetLinearForm_imaginaryPlace_star_eq_conj]
  rw [← htarget]
  exact htube

/-! ## Fixed-shortest-vector fibers -/

/-- A family of complex cells whose exact reduced covers have one common
shortest vector has controlled multiplicity in every reciprocal-minimum
band.  This is the finite incidence form of the four-chart packing lemma;
the hypotheses retain the literal certificate and reduced-cover witnesses
for each selected cell. -/
theorem card_complexUnitCircleSlopeCells_with_common_shortestVector_le
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (ha : 0 < a)
    {E S : ℝ} {M : ℕ}
    (hM : 0 < M) (hS : 0 < S)
    (y : Fin 2 → ℤ)
    (J : Finset ComplexUnitCircleSlopeCellIndex)
    (hJ : J ⊆ complexUnitCircleSlopeCellIndices M)
    (T : {i // i ∈ J} → Finset (Fin 2 → ℤ))
    (cert : ∀ c : {i // i ∈ J},
      PrimitiveWedgeReducedTargetCoverCertificate (T c) E
        ((6 * E / (M : ℝ)) /
          Real.sqrt |(NumberField.discr
            (rationalQuadraticAlgebra (-a)) : ℝ)|) 2)
    (hell : ∀ c : {i // i ∈ J},
      (cert c).ell = main3AnchorHermitianRadialAddHom 1
        (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) (cert c).anchor)
    (hrhoLower : ∀ c : {i // i ∈ J},
      E ≤ 2 * (cert c).ell (cert c).anchor)
    (hrhoUpper : ∀ c : {i // i ∈ J},
      (cert c).ell (cert c).anchor ≤ E)
    (G H : {i // i ∈ J} → SL(2, ℤ))
    (hspec : ∀ c : {i // i ∈ J},
      PrimitiveWedgeReducedTargetCoverSpec
        (T c) (cert c).ell (cert c).anchor E
          ((6 * E / (M : ℝ)) /
            Real.sqrt |(NumberField.discr
              (rationalQuadraticAlgebra (-a)) : ℝ)|) 2 (G c) (H c))
    (hband : ∀ c : {i // i ∈ J},
      S ≤ 1 /
        firstSlopeSupNorm
          ((((6 * E / (M : ℝ)) /
            Real.sqrt |(NumberField.discr
              (rationalQuadraticAlgebra (-a)) : ℝ)|)) / 2)
          (1 + (2 : ℝ) / 2)
          (2 * (cert c).ell (cert c).anchor * (1 + (2 : ℝ) / 2) / E)
          (-(((6 * E / (M : ℝ)) /
            Real.sqrt |(NumberField.discr
              (rationalQuadraticAlgebra (-a)) : ℝ)|)) *
            (cert c).ell (fun i ↦ G c i 1) / E))
    (hsame : ∀ c : {i // i ∈ J},
      primitiveWedgeReducedTargetCoverShortestVector (G c) (H c) = y)
    (htube : ∀ c : {i // i ∈ J},
      InComplexUnitCircleSquareTargetTube M c.1
        (conj (main3IntegralTargetLinearForm
            (shiftedSquareImaginaryPlaceEmbedding a ha F.omega)
            (cert c).anchor) /
          main3IntegralTargetLinearForm
            (shiftedSquareImaginaryPlaceEmbedding a ha F.omega)
            (cert c).anchor)) :
    (J.card : ℝ) ≤ 140 +
      768 * Real.sqrt E /
        (S * ‖main3IntegralTargetLinearForm
          (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y‖) := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  let delta := 6 * Real.sqrt E /
    (S * ‖main3IntegralTargetLinearForm
      (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y‖)
  have hdelta : 0 ≤ delta := by
    dsimp only [delta]
    positivity
  have hcount := card_complexUnitCircleSlopeCells_with_target_near_le
    M hM
      (conj (main3IntegralTargetLinearForm
          (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y) /
        main3IntegralTargetLinearForm
          (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y)
      delta hdelta J hJ
      (by
        intro i hi
        let c : {i // i ∈ J} := ⟨i, hi⟩
        let anchorValue := main3IntegralTargetLinearForm
          (shiftedSquareImaginaryPlaceEmbedding a ha F.omega)
          (cert c).anchor
        refine ⟨conj anchorValue / anchorValue, ?_, ?_⟩
        · simpa only [c, anchorValue] using htube c
        · have hdirection :=
            (hspec c).complex_shortest_direction_le_of_reciprocalBand
              F ha (cert c).R_pos hMreal hS (cert c) (hell c)
                (hrhoLower c) (hrhoUpper c) (hband c)
          dsimp only at hdirection
          rw [hsame c] at hdirection
          simpa only [c, anchorValue, delta] using hdirection)
  calc
    (J.card : ℝ) ≤ 140 + 128 * delta := hcount
    _ = 140 + 768 * Real.sqrt E /
        (S * ‖main3IntegralTargetLinearForm
          (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y‖) := by
      dsimp only [delta]
      ring

end


end PellPaper
