import Pell.Main3LargeAnalyticComplexCompletionProductHeight
import Pell.Main3LargeAnalyticComplexCoverShortestVectorBound
import Mathlib.Tactic

/-!
# Candidate: coherent complex-cell cover selection

For fixed main3 block data and one auxiliary key, this candidate filters the
literal finite complex-cell index family to the cells with nonempty exact
target image.  It then makes one classical choice of the complete complex
cover package on every member of that finite subtype.

The package stores `cert`, `G`, and `H` together.  Every cover, shortest-vector,
entry-height, and logarithmic conclusion therefore refers definitionally to
the same witnesses.
-/

namespace PellPaper

open scoped MatrixGroups ComplexConjugate

noncomputable section

local instance main3LargeAnalyticComplexCellCoverSelection_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-! ## The finite active complex-cell family -/

/-- The literal complex mesh cells whose exact fixed-key target image is
nonempty.  Filtering the production finite mesh keeps finiteness explicit and
also carries the mesh-index membership needed in later cell sums. -/
noncomputable def main3LargeAnalytic_nonemptyComplexCellIndices
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) :
    Finset ComplexUnitCircleSlopeCellIndex := by
  classical
  exact (complexUnitCircleSlopeCellIndices (main3UnbalancedM theta Y)).filter
    (fun cell ↦
      (main3LargeAnalyticFixedKeyCellTargetVectorImage
        htheta hY hi key (Sum.inr cell)).Nonempty)

@[simp]
theorem mem_main3LargeAnalytic_nonemptyComplexCellIndices
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : ComplexUnitCircleSlopeCellIndex) :
    cell ∈ main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key ↔
      cell ∈ complexUnitCircleSlopeCellIndices
        (main3UnbalancedM theta Y) ∧
      (main3LargeAnalyticFixedKeyCellTargetVectorImage
        htheta hY hi key (Sum.inr cell)).Nonempty := by
  classical
  simp [main3LargeAnalytic_nonemptyComplexCellIndices]

theorem card_main3LargeAnalytic_nonemptyComplexCellIndices_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) :
    (main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key).card ≤
      4 * (2 * main3UnbalancedM theta Y + 1) := by
  classical
  calc
    (main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key).card ≤
        (complexUnitCircleSlopeCellIndices
          (main3UnbalancedM theta Y)).card := by
      exact Finset.card_filter_le _ _
    _ = 4 * (2 * main3UnbalancedM theta Y + 1) := by simp

/-! ## A same-witness bundled cover -/

/-- A generic bundle for the exact data used by one complex fixed cell.
The real parameters are explicit so downstream arguments can name the
derived scales without reopening the large existential theorem. -/
structure Main3LargeAnalyticComplexCellCoverSelectionData
    (T : Finset (Fin 2 → ℤ)) (omega : ℂ)
    (E Delta Mmesh K T₀ A Y : ℝ) where
  cert : PrimitiveWedgeReducedTargetCoverCertificate T E K 2
  G : SL(2, ℤ)
  H : SL(2, ℤ)
  ell_eq : cert.ell =
    main3AnchorHermitianRadialAddHom 1 omega cert.anchor
  rho_lower : E ≤ 2 * cert.ell cert.anchor
  rho_upper : cert.ell cert.anchor ≤ E
  calibration :
    let rho := cert.ell cert.anchor
    let U := K / 2
    let V := 1 + (2 : ℝ) / 2
    let M₀ := 2 * rho * V / E
    V = 2 ∧
      M₀ = 4 * rho / E ∧
      2 ≤ M₀ ∧ M₀ ≤ 4 ∧
      4 * (U + V) = 2 * K + 8 ∧
      36 * 2 * K = 432 * E / (Mmesh * Delta)
  completion_spec :
    PrimitiveWedgeReducedTargetCoverCompletionEntryBoundSpec
      T cert.ell cert.anchor E K 2 T₀ G H
  productHeight_le :
    let rho := cert.ell cert.anchor
    let U := K / 2
    let V := 1 + (2 : ℝ) / 2
    let M₀ := 2 * rho * V / E
    let beta := cert.ell (fun i ↦ G i 1)
    let z := -K * beta / E
    let L := 2 * (T₀ + 1) * reducedSlopeMatrixEntryBound U V M₀ z
    L ≤ (2 : ℝ) ^ 26 * Y * A ^ 3 * T₀ ^ 3
  log_productHeight_le :
    let rho := cert.ell cert.anchor
    let U := K / 2
    let V := 1 + (2 : ℝ) / 2
    let M₀ := 2 * rho * V / E
    let beta := cert.ell (fun i ↦ G i 1)
    let z := -K * beta / E
    let L := 2 * (T₀ + 1) * reducedSlopeMatrixEntryBound U V M₀ z
    Real.log (L + 1) ≤ 64 * Real.log Y
  log_scaleSum_le :
    let U := K / 2
    let V := 1 + (2 : ℝ) / 2
    Real.log (4 * (U + V)) ≤ 12 * Real.log Y
  shortest_norm_bounds :
    let rho := cert.ell cert.anchor
    let U := K / 2
    let V := 1 + (2 : ℝ) / 2
    let M₀ := 2 * rho * V / E
    let beta := cert.ell (fun i ↦ G i 1)
    let z := -K * beta / E
    let mu := firstSlopeSupNorm U V M₀ z
    let y := primitiveWedgeReducedTargetCoverShortestVector G H
    ‖main3IntegralTargetLinearForm omega y‖ ^ 2 ≤
        (5 / 8 : ℝ) * E * mu ^ 2 ∧
      (∀ S : ℝ, 0 ≤ S → S ≤ 1 / mu →
        S ^ 2 * ‖main3IntegralTargetLinearForm omega y‖ ^ 2 ≤
          (5 / 8 : ℝ) * E) ∧
      (∀ S : ℝ, 0 < S → S ≤ 1 / mu →
        ‖main3IntegralTargetLinearForm omega y‖ ^ 2 ≤
          ((5 / 8 : ℝ) * E) / S ^ 2)

namespace Main3LargeAnalyticComplexCellCoverSelectionData

variable {T : Finset (Fin 2 → ℤ)} {omega : ℂ}
  {E Delta Mmesh K T₀ A Y : ℝ}

def rho
    (S : Main3LargeAnalyticComplexCellCoverSelectionData
      T omega E Delta Mmesh K T₀ A Y) : ℝ :=
  S.cert.ell S.cert.anchor

def U
    (_S : Main3LargeAnalyticComplexCellCoverSelectionData
      T omega E Delta Mmesh K T₀ A Y) : ℝ :=
  K / 2

def V
    (_S : Main3LargeAnalyticComplexCellCoverSelectionData
      T omega E Delta Mmesh K T₀ A Y) : ℝ :=
  1 + (2 : ℝ) / 2

def M₀
    (S : Main3LargeAnalyticComplexCellCoverSelectionData
      T omega E Delta Mmesh K T₀ A Y) : ℝ :=
  2 * S.rho * S.V / E

def beta
    (S : Main3LargeAnalyticComplexCellCoverSelectionData
      T omega E Delta Mmesh K T₀ A Y) : ℝ :=
  S.cert.ell (fun i ↦ S.G i 1)

def z
    (S : Main3LargeAnalyticComplexCellCoverSelectionData
      T omega E Delta Mmesh K T₀ A Y) : ℝ :=
  -K * S.beta / E

def mu
    (S : Main3LargeAnalyticComplexCellCoverSelectionData
      T omega E Delta Mmesh K T₀ A Y) : ℝ :=
  firstSlopeSupNorm S.U S.V S.M₀ S.z

def shortestVector
    (S : Main3LargeAnalyticComplexCellCoverSelectionData
      T omega E Delta Mmesh K T₀ A Y) : Fin 2 → ℤ :=
  primitiveWedgeReducedTargetCoverShortestVector S.G S.H

def productHeight
    (S : Main3LargeAnalyticComplexCellCoverSelectionData
      T omega E Delta Mmesh K T₀ A Y) : ℝ :=
  2 * (T₀ + 1) * reducedSlopeMatrixEntryBound S.U S.V S.M₀ S.z

/-- The base reduced-cover specification is a projection of the strong
completion specification and therefore uses the stored `cert,G,H`. -/
theorem cover_spec
    (S : Main3LargeAnalyticComplexCellCoverSelectionData
      T omega E Delta Mmesh K T₀ A Y) :
    PrimitiveWedgeReducedTargetCoverSpec
      T S.cert.ell S.cert.anchor E K 2 S.G S.H :=
  S.completion_spec.2.1

theorem completion_entry_le
    (S : Main3LargeAnalyticComplexCellCoverSelectionData
      T omega E Delta Mmesh K T₀ A Y) (i j : Fin 2) :
    |((S.G i j : ℤ) : ℝ)| ≤ T₀ + 1 :=
  S.completion_spec.1 i j

/-- The actual product `G*H`, not a separately selected basis, has the
stored literal product-height bound. -/
theorem product_entry_le
    (S : Main3LargeAnalyticComplexCellCoverSelectionData
      T omega E Delta Mmesh K T₀ A Y) (i j : Fin 2) :
    |((((S.G * S.H) i j : ℤ) : ℝ))| ≤ S.productHeight := by
  simpa only [productHeight, U, V, M₀, rho, z, beta] using
    S.completion_spec.2.2 i j

theorem productHeight_bound
    (S : Main3LargeAnalyticComplexCellCoverSelectionData
      T omega E Delta Mmesh K T₀ A Y) :
    S.productHeight ≤ (2 : ℝ) ^ 26 * Y * A ^ 3 * T₀ ^ 3 := by
  simpa only [productHeight, U, V, M₀, rho, z, beta] using
    S.productHeight_le

theorem log_productHeight_bound
    (S : Main3LargeAnalyticComplexCellCoverSelectionData
      T omega E Delta Mmesh K T₀ A Y) :
    Real.log (S.productHeight + 1) ≤ 64 * Real.log Y := by
  simpa only [productHeight, U, V, M₀, rho, z, beta] using
    S.log_productHeight_le

theorem log_scaleSum_bound
    (S : Main3LargeAnalyticComplexCellCoverSelectionData
      T omega E Delta Mmesh K T₀ A Y) :
    Real.log (4 * (S.U + S.V)) ≤ 12 * Real.log Y := by
  simpa only [U, V] using S.log_scaleSum_le

/-- Exact primitive/nonzero first-column description of the selected shortest
vector, with the same `mu` used in its embedding-norm bound. -/
theorem shortestVector_spec
    (S : Main3LargeAnalyticComplexCellCoverSelectionData
      T omega E Delta Mmesh K T₀ A Y) :
    S.shortestVector ≠ 0 ∧
      IsCoprime (S.shortestVector 0) (S.shortestVector 1) ∧
      max |2 * S.cert.ell S.shortestVector / E|
          |2 * (main3IntegralTargetWedge S.cert.anchor S.shortestVector : ℝ) /
            K| = S.mu := by
  simpa only [shortestVector, mu, U, V, M₀, rho, z, beta] using
    S.cover_spec.shortest_original_vector

theorem mu_pos
    (S : Main3LargeAnalyticComplexCellCoverSelectionData
      T omega E Delta Mmesh K T₀ A Y) :
    0 < S.mu := by
  unfold mu U V M₀ rho z beta
  apply firstSlopeSupNorm_pos
  · exact div_pos S.cert.K_pos (by norm_num)
  · change 0 < 1 + (2 : ℝ) / 2
    norm_num
  · change 0 <
      2 * S.cert.ell S.cert.anchor * (1 + (2 : ℝ) / 2) / E
    exact div_pos
      (mul_pos (mul_pos (by norm_num) S.cert.anchor_pos) (by norm_num))
      S.cert.R_pos

theorem shortestVector_norm_sq_le
    (S : Main3LargeAnalyticComplexCellCoverSelectionData
      T omega E Delta Mmesh K T₀ A Y) :
    ‖main3IntegralTargetLinearForm omega S.shortestVector‖ ^ 2 ≤
      (5 / 8 : ℝ) * E * S.mu ^ 2 := by
  simpa only [shortestVector, mu, U, V, M₀, rho, z, beta] using
    S.shortest_norm_bounds.1

theorem shortestVector_threshold
    (S : Main3LargeAnalyticComplexCellCoverSelectionData
      T omega E Delta Mmesh K T₀ A Y)
    {R : ℝ} (hR : 0 ≤ R) (hRmu : R ≤ 1 / S.mu) :
    R ^ 2 * ‖main3IntegralTargetLinearForm omega S.shortestVector‖ ^ 2 ≤
      (5 / 8 : ℝ) * E := by
  simpa only [shortestVector, mu, U, V, M₀, rho, z, beta] using
    S.shortest_norm_bounds.2.1 R hR hRmu

end Main3LargeAnalyticComplexCellCoverSelectionData

/-! ## Fixed-main3 specialization and choice -/

/-- The specialized type of a coherent cover package for one fixed complex
cell.  The local quadratic-field instance and all scale definitions are kept
inside the abbreviation. -/
abbrev Main3LargeAnalyticFixedKeyComplexCellCoverSelection
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : ComplexUnitCircleSlopeCellIndex)
    (ha : 0 < shiftedSquareA h v) : Type :=
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
  Main3LargeAnalyticComplexCellCoverSelectionData T (sigma F.omega)
    E Delta Mmesh K T₀ |(shiftedSquareA h v : ℝ)| (Y : ℝ)

/-- The production same-witness product-height theorem, together with the
production shortest-vector estimate on those exact witnesses, proves that the
bundled selection type is inhabited.  Keeping this first step in `Prop` avoids
large elimination from an existential proposition. -/
theorem nonempty_main3LargeAnalytic_fixedKeyComplexCellCoverSelection
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
    Nonempty (Main3LargeAnalyticFixedKeyComplexCellCoverSelection
      htheta hY hi key cell ha) := by
  dsimp only [Main3LargeAnalyticFixedKeyComplexCellCoverSelection]
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
  let A := |(shiftedSquareA h v : ℝ)|
  obtain ⟨cert, hell, hrhoLower, hrhoUpper, hcalibration,
      G, H, hcompletion, hheight, hlogHeight, hlogScale⟩ :=
    exists_main3LargeAnalyticFixedKeyComplexCellTargetCompletionEntryBoundCover_with_productHeight
      htheta hY hi key cell ha hnonempty
  have hbase : PrimitiveWedgeReducedTargetCoverSpec
      T cert.ell cert.anchor E K 2 G H := by
    simpa only [T, E, K] using hcompletion.2.1
  have hshort :=
    PrimitiveWedgeReducedTargetCoverSpec.complex_shortest_original_vector_norm_sq_bounds
      F ha (by simpa only [E] using cert.R_pos)
        (by exact_mod_cast six_le_main3UnbalancedM htheta hY)
      cert (by simpa only [F, sigma] using hell)
        (by simpa only [E] using hrhoLower) hbase
  refine ⟨{
    cert := cert
    G := G
    H := H
    ell_eq := ?_
    rho_lower := ?_
    rho_upper := ?_
    calibration := ?_
    completion_spec := ?_
    productHeight_le := ?_
    log_productHeight_le := ?_
    log_scaleSum_le := ?_
    shortest_norm_bounds := ?_ }⟩
  · simpa only [F, sigma] using hell
  · simpa only [E] using hrhoLower
  · simpa only [E] using hrhoUpper
  · simpa only [E, K, Mmesh, Delta] using hcalibration
  · simpa only [T, E, K, T₀] using hcompletion
  · simpa only [E, K, T₀, A] using hheight
  · simpa only [E, K, T₀] using hlogHeight
  · simpa only [K] using hlogScale
  · simpa only [F, sigma, E, K, Mmesh, Delta] using hshort

/-- Choose one coherent package for a single cell once nonemptiness is known. -/
noncomputable def main3LargeAnalytic_fixedKeyComplexCellCoverSelectionOfNonempty
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
    Main3LargeAnalyticFixedKeyComplexCellCoverSelection
      htheta hY hi key cell ha :=
  Classical.choice
    (nonempty_main3LargeAnalytic_fixedKeyComplexCellCoverSelection
      htheta hY hi key cell ha hnonempty)

/-- A choice function on the finite subtype of active complex cells.  The
subtype membership proof supplies nonemptiness, so consumers need no further
choice or proof argument. -/
noncomputable def main3LargeAnalytic_complexCellCoverSelection
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : 0 < shiftedSquareA h v)
    (cell : ↑(main3LargeAnalytic_nonemptyComplexCellIndices
      htheta hY hi key)) :
    Main3LargeAnalyticFixedKeyComplexCellCoverSelection
      htheta hY hi key cell.1 ha := by
  apply main3LargeAnalytic_fixedKeyComplexCellCoverSelectionOfNonempty
  exact (mem_main3LargeAnalytic_nonemptyComplexCellIndices
    htheta hY hi key cell.1).mp cell.2 |>.2

end


end PellPaper
