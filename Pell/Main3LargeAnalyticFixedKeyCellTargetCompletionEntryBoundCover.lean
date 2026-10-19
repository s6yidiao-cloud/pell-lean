import Pell.Main3LargeAnalyticFixedKeyCellTargetEntryBoundCover

/-!
# Fixed-cell target covers retaining a bounded completion matrix

This module strengthens the existing same-basis entry-bounded fixed-cell
cover by retaining the all-entry estimate on the primitive-anchor completion
matrix `G`.  The old specification is included as a literal conjunct, so the
completion bound and every existing cover conclusion use the same witnesses
`G`, `H`, and `W = G * H`.
-/

namespace PellPaper

open scoped MatrixGroups

noncomputable section

local instance main3LargeAnalyticFixedKeyCellTargetCompletionEntryBoundCover_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-! ## Strong same-witness specification -/

/-- The completion-entry-bounded cover consists of an all-entry estimate for
the primitive-anchor completion `G` and the complete existing entry-bounded
cover specification for the identical pair `G,H`. -/
def PrimitiveWedgeReducedTargetCoverCompletionEntryBoundSpec
    (T : Finset (Fin 2 → ℤ)) (ell : (Fin 2 → ℤ) →+ ℝ)
    (y₀ : Fin 2 → ℤ) (R K C T₀ : ℝ) (G H : SL(2, ℤ)) : Prop :=
  (∀ i j, |((G i j : ℤ) : ℝ)| ≤ T₀ + 1) ∧
  PrimitiveWedgeReducedTargetCoverEntryBoundSpec
    T ell y₀ R K C T₀ G H

/-- A radial input certificate produces one pair `G,H` that simultaneously
has the bounded primitive completion and the complete old same-basis cover
and product-entry estimates. -/
theorem PrimitiveWedgeReducedTargetCoverCertificate.exists_reducedTargetCover_with_completion_entry_bound
    {T : Finset (Fin 2 → ℤ)} {R K C T₀ : ℝ}
    (cert : PrimitiveWedgeReducedTargetCoverCertificate T R K C)
    (hT₀ : 1 ≤ T₀)
    (hanchor : ∀ i, |((cert.anchor i : ℤ) : ℝ)| ≤ T₀) :
    ∃ G H : SL(2, ℤ),
      PrimitiveWedgeReducedTargetCoverCompletionEntryBoundSpec
        T cert.ell cert.anchor R K C T₀ G H := by
  have hcover :=
    exists_primitiveWedge_reducedTargetCover_with_completion_entry_bound
      T cert.ell cert.anchor R K C T₀ cert.anchor_mem cert.primitive
        cert.R_pos cert.K_pos cert.C_pos hT₀ hanchor cert.anchor_pos
        cert.radial cert.wedge cert.radius_le
  dsimp only at hcover
  obtain ⟨G, H, hGentry, hcolumn, hWentry, hrest⟩ := hcover
  refine ⟨G, H, hGentry, ?_⟩
  unfold PrimitiveWedgeReducedTargetCoverEntryBoundSpec
  constructor
  · unfold PrimitiveWedgeReducedTargetCoverSpec
    dsimp only
    exact ⟨hcolumn, hrest⟩
  · exact hWentry

/-- For an exact fixed-cell target image, its common raw coordinate radius
bounds every entry of the completion `G` and is also the parameter in the
existing product-entry cover specification. -/
theorem PrimitiveWedgeReducedTargetCoverCertificate.exists_fixedKeyCellTargetCover_with_completion_entry_bound
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    {R K C : ℝ}
    (cert : PrimitiveWedgeReducedTargetCoverCertificate
      (main3LargeAnalyticFixedKeyCellTargetVectorImage
        htheta hY hi key cell) R K C) :
    ∃ G H : SL(2, ℤ),
      PrimitiveWedgeReducedTargetCoverCompletionEntryBoundSpec
        (main3LargeAnalyticFixedKeyCellTargetVectorImage
          htheta hY hi key cell)
        cert.ell cert.anchor R K C
        (main3LargeAnalyticFixedKeyTargetCoordinateRadius
          (shiftedSquareA h v) Y key) G H := by
  apply cert.exists_reducedTargetCover_with_completion_entry_bound
  · exact
      one_le_main3LargeAnalyticFixedKeyTargetCoordinateRadius_of_targetImage_nonempty
        htheta hY hi key cell ⟨cert.anchor, cert.anchor_mem⟩
  · exact
      main3LargeAnalyticFixedKeyCellTargetVectorImage_abs_coordinate_le
        htheta hY hi key cell cert.anchor_mem

/-! ## Branchwise completion-entry-bounded covers -/

/-- The complex Hermitian radial certificate, bounded completion, and full
entry-bounded target cover are realized by one and the same pair `G,H`. -/
theorem exists_main3LargeAnalyticFixedKeyComplexCellTargetCompletionEntryBoundCover
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
    let T₀ := main3LargeAnalyticFixedKeyTargetCoordinateRadius
      (shiftedSquareA h v) Y key
    ∃ cert : PrimitiveWedgeReducedTargetCoverCertificate T E K 2,
      cert.ell = main3AnchorHermitianRadialAddHom
        1 (sigma F.omega) cert.anchor ∧
      E ≤ 2 * cert.ell cert.anchor ∧
      cert.ell cert.anchor ≤ E ∧
      (let rho := cert.ell cert.anchor
       let U := K / 2
       let V := 1 + (2 : ℝ) / 2
       let M₀ := 2 * rho * V / E
       V = 2 ∧
       M₀ = 4 * rho / E ∧
       2 ≤ M₀ ∧ M₀ ≤ 4 ∧
       4 * (U + V) = 2 * K + 8 ∧
       36 * 2 * K = 432 * E / (Mmesh * Delta)) ∧
      ∃ G H : SL(2, ℤ),
        PrimitiveWedgeReducedTargetCoverCompletionEntryBoundSpec
          T cert.ell cert.anchor E K 2 T₀ G H := by
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
  let T₀ := main3LargeAnalyticFixedKeyTargetCoordinateRadius
    (shiftedSquareA h v) Y key
  obtain ⟨cert, hell, hrhoLower, hrhoUpper, hcalibration⟩ :=
    exists_main3LargeAnalyticFixedKeyComplexCellTargetRadialCoverCertificate
      htheta hY hi key cell ha hnonempty
  have hentry :=
    cert.exists_fixedKeyCellTargetCover_with_completion_entry_bound
      htheta hY hi key (Sum.inr cell)
  refine ⟨cert, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [F, sigma] using hell
  · simpa only [E] using hrhoLower
  · simpa only [E] using hrhoUpper
  · simpa only [E, K, Mmesh, Delta] using hcalibration
  · simpa only [T, E, K, T₀] using hentry

/-- The real signed-centre radial certificate, bounded completion, and full
entry-bounded target cover are realized by one and the same pair `G,H`. -/
theorem exists_main3LargeAnalyticFixedKeyRealCellTargetCompletionEntryBoundCover
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
    let T₀ := main3LargeAnalyticFixedKeyTargetCoordinateRadius
      (shiftedSquareA h v) Y key
    ∃ cert : PrimitiveWedgeReducedTargetCoverCertificate T (2 * E) K 8,
      cert.ell = main3AnchorHermitianRadialAddHom
        (c ^ 2) (sigma F.omega) cert.anchor ∧
      E ≤ 4 * cert.ell cert.anchor ∧
      cert.ell cert.anchor ≤ 2 * E ∧
      (let rho := cert.ell cert.anchor
       let U := K / 2
       let V := 1 + (8 : ℝ) / 2
       let M₀ := 2 * rho * V / (2 * E)
       V = 5 ∧
       M₀ = 5 * rho / E ∧
       (5 / 4 : ℝ) ≤ M₀ ∧ M₀ ≤ 10 ∧
       4 * (U + V) = 2 * K + 20 ∧
       36 * 8 * K = 576 * E / (Mmesh * Delta)) ∧
      ∃ G H : SL(2, ℤ),
        PrimitiveWedgeReducedTargetCoverCompletionEntryBoundSpec
          T cert.ell cert.anchor (2 * E) K 8 T₀ G H := by
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
  let T₀ := main3LargeAnalyticFixedKeyTargetCoordinateRadius
    (shiftedSquareA h v) Y key
  obtain ⟨cert, hell, hrhoLower, hrhoUpper, hcalibration⟩ :=
    exists_main3LargeAnalyticFixedKeyRealCellTargetRadialCoverCertificate
      htheta hY hi key cell ha hnonempty
  have hentry :=
    cert.exists_fixedKeyCellTargetCover_with_completion_entry_bound
      htheta hY hi key (Sum.inl cell)
  refine ⟨cert, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [F, sigma, c] using hell
  · simpa only [E] using hrhoLower
  · simpa only [E] using hrhoUpper
  · simpa only [E, K, Mmesh, Delta] using hcalibration
  · simpa only [T, E, K, T₀] using hentry

end

end PellPaper
