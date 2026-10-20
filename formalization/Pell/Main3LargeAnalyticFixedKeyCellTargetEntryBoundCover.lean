import Pell.Main3LargeAnalyticFixedKeyCellTargetRadialGeometry
import Pell.Main3LargeAnalyticFixedKeyCellCoordinateBounds
import Pell.PrimitiveWedgeReducedTargetCoverEntryBound
import Mathlib.Tactic

/-!
# Entry-bounded reduced covers for one fixed main3 target cell

The literal raw target-coordinate radius bounds the primitive anchor used by
the radial cover.  The entry-bounded primitive-wedge theorem can therefore
choose its determinant-one completion and its reduced slope factor in one
step, retaining the same product basis for all cover and matrix-entry facts.
-/

namespace PellPaper

open scoped MatrixGroups

noncomputable section

local instance main3LargeAnalyticFixedKeyCellTargetEntryBoundCover_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-! ## Raw coordinate bounds on the exact target image -/

/-- Every vector in the exact target projection obeys both raw target
coordinate bounds. -/
theorem main3LargeAnalyticFixedKeyCellTargetVectorImage_abs_coordinate_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    {y : Fin 2 → ℤ}
    (hy : y ∈ main3LargeAnalyticFixedKeyCellTargetVectorImage
      htheta hY hi key cell) :
    ∀ i, |((y i : ℤ) : ℝ)| ≤
      main3LargeAnalyticFixedKeyTargetCoordinateRadius
        (shiftedSquareA h v) Y key := by
  obtain ⟨z, hz, rfl⟩ :=
    (mem_main3LargeAnalyticFixedKeyCellTargetVectorImage_iff
      htheta hY hi key cell y).mp hy
  have hbounds :=
    main3LargeAnalytic_fixedKeyCellCoordinatePointImage_abs_bounds
      htheta hY hi hz
  intro i
  fin_cases i
  · simpa [shiftedSquareCoordinatePointTargetVector] using hbounds.2.1
  · simpa [shiftedSquareCoordinatePointTargetVector] using hbounds.2.2

/-- Nonemptiness of the exact primitive target image forces its common raw
coordinate radius to be at least one. -/
theorem one_le_main3LargeAnalyticFixedKeyTargetCoordinateRadius_of_targetImage_nonempty
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (hnonempty :
      (main3LargeAnalyticFixedKeyCellTargetVectorImage
        htheta hY hi key cell).Nonempty) :
    (1 : ℝ) ≤ main3LargeAnalyticFixedKeyTargetCoordinateRadius
      (shiftedSquareA h v) Y key := by
  obtain ⟨y, hy⟩ := hnonempty
  have hprimitive :=
    main3LargeAnalyticFixedKeyCellTargetVectorImage_primitive
      htheta hY hi key cell hy
  have hbounds :=
    main3LargeAnalyticFixedKeyCellTargetVectorImage_abs_coordinate_le
      htheta hY hi key cell hy
  rcases hprimitive.ne_zero_or_ne_zero with hzero | hone
  · have hcoord : (1 : ℝ) ≤ |((y 0 : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs hzero
    exact hcoord.trans (hbounds 0)
  · have hcoord : (1 : ℝ) ≤ |((y 1 : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs hone
    exact hcoord.trans (hbounds 1)

/-! ## Compact same-basis entry-bounded specification -/

/-- The entry-bounded cover proposition consists of the complete reduced
target-cover specification and the entry estimate for the very same product
basis `W = G * H`. -/
def PrimitiveWedgeReducedTargetCoverEntryBoundSpec
    (T : Finset (Fin 2 → ℤ)) (ell : (Fin 2 → ℤ) →+ ℝ)
    (y₀ : Fin 2 → ℤ) (R K C T₀ : ℝ) (G H : SL(2, ℤ)) : Prop :=
  PrimitiveWedgeReducedTargetCoverSpec T ell y₀ R K C G H ∧
  let rho := ell y₀
  let U := K / 2
  let V := 1 + C / 2
  let M₀ := 2 * rho * V / R
  let beta := ell (fun i ↦ G i 1)
  let z := -K * beta / R
  let W := G * H
  ∀ i j, |((W i j : ℤ) : ℝ)| ≤
    2 * (T₀ + 1) * reducedSlopeMatrixEntryBound U V M₀ z

/-- The generic radial input certificate can invoke the entry-bounded cover
theorem without losing any conclusion of the original reduced-cover spec. -/
theorem PrimitiveWedgeReducedTargetCoverCertificate.exists_reducedTargetCover_with_entry_bound
    {T : Finset (Fin 2 → ℤ)} {R K C T₀ : ℝ}
    (cert : PrimitiveWedgeReducedTargetCoverCertificate T R K C)
    (hT₀ : 1 ≤ T₀)
    (hanchor : ∀ i, |((cert.anchor i : ℤ) : ℝ)| ≤ T₀) :
    ∃ G H : SL(2, ℤ),
      PrimitiveWedgeReducedTargetCoverEntryBoundSpec
        T cert.ell cert.anchor R K C T₀ G H := by
  have hcover := exists_primitiveWedge_reducedTargetCover_with_entry_bound
    T cert.ell cert.anchor R K C T₀ cert.anchor_mem cert.primitive
      cert.R_pos cert.K_pos cert.C_pos hT₀ hanchor cert.anchor_pos
      cert.radial cert.wedge cert.radius_le
  dsimp only at hcover
  obtain ⟨G, H, hcolumn, hentry, hrest⟩ := hcover
  refine ⟨G, H, ?_⟩
  unfold PrimitiveWedgeReducedTargetCoverEntryBoundSpec
  constructor
  · unfold PrimitiveWedgeReducedTargetCoverSpec
    dsimp only
    exact ⟨hcolumn, hrest⟩
  · exact hentry

/-- For an exact fixed-cell target image, the entry parameter can be chosen
to be precisely its common raw target-coordinate radius. -/
theorem PrimitiveWedgeReducedTargetCoverCertificate.exists_fixedKeyCellTargetCover_with_entry_bound
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
      PrimitiveWedgeReducedTargetCoverEntryBoundSpec
        (main3LargeAnalyticFixedKeyCellTargetVectorImage
          htheta hY hi key cell)
        cert.ell cert.anchor R K C
        (main3LargeAnalyticFixedKeyTargetCoordinateRadius
          (shiftedSquareA h v) Y key) G H := by
  apply cert.exists_reducedTargetCover_with_entry_bound
  · exact
      one_le_main3LargeAnalyticFixedKeyTargetCoordinateRadius_of_targetImage_nonempty
        htheta hY hi key cell ⟨cert.anchor, cert.anchor_mem⟩
  · exact
      main3LargeAnalyticFixedKeyCellTargetVectorImage_abs_coordinate_le
        htheta hY hi key cell cert.anchor_mem

/-! ## Branchwise entry-bounded radial covers -/

/-- The complex Hermitian radial certificate and the raw-coordinate entry
bound are realized by one and the same pair `G,H`. -/
theorem exists_main3LargeAnalyticFixedKeyComplexCellTargetEntryBoundCover
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
        PrimitiveWedgeReducedTargetCoverEntryBoundSpec
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
    cert.exists_fixedKeyCellTargetCover_with_entry_bound
      htheta hY hi key (Sum.inr cell)
  refine ⟨cert, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [F, sigma] using hell
  · simpa only [E] using hrhoLower
  · simpa only [E] using hrhoUpper
  · simpa only [E, K, Mmesh, Delta] using hcalibration
  · simpa only [T, E, K, T₀] using hentry

/-- The signed-centre real radial certificate and the raw-coordinate entry
bound are realized by one and the same pair `G,H`. -/
theorem exists_main3LargeAnalyticFixedKeyRealCellTargetEntryBoundCover
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
        PrimitiveWedgeReducedTargetCoverEntryBoundSpec
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
    cert.exists_fixedKeyCellTargetCover_with_entry_bound
      htheta hY hi key (Sum.inl cell)
  refine ⟨cert, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [F, sigma, c] using hell
  · simpa only [E] using hrhoLower
  · simpa only [E] using hrhoUpper
  · simpa only [E, K, Mmesh, Delta] using hcalibration
  · simpa only [T, E, K, T₀] using hentry

end


end PellPaper
