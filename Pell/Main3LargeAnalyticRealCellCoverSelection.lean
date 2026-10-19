import Pell.Main3LargeAnalyticRealCellCompletionProductHeightLogBudget
import Pell.Main3LargeAnalyticRealCoverShortestVectorBound
import Mathlib.Tactic

/-!
# Candidate: coherent real-cell cover selection

For fixed Main3 block data and one auxiliary key, this workspace filters the
literal finite real-cell family to the cells with nonempty exact target image.
It then chooses one complete package `cert, G, H` for every active cell.

The certificate and matrices are stored together.  Thus the cover,
completion-entry bound, actual product-entry bound, height/logarithmic
budgets, exact shortest-vector identity, and determinant-one two-place norm
bound all refer definitionally to the same witnesses.  No membership of the
shortest vector in the target image is asserted.
-/

namespace PellPaper

open scoped MatrixGroups ComplexConjugate

noncomputable section

local instance main3LargeAnalyticRealCellCoverSelection_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-! ## The finite active real-cell family -/

/-- The literal real square-map cells whose exact fixed-key target image is
nonempty.  The ambient finite family is retained in the filter, so subtype
membership supplies both the literal cell-index condition and nonemptiness. -/
noncomputable def main3LargeAnalytic_nonemptyRealCellIndices
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) :
    Finset RealSquareMapCellPairIndex := by
  classical
  exact (realSquareMapCellPairIndices
      (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
      (main3UnbalancedM theta Y)).filter
    (fun cell ↦
      (main3LargeAnalyticFixedKeyCellTargetVectorImage
        htheta hY hi key (Sum.inl cell)).Nonempty)

@[simp]
theorem mem_main3LargeAnalytic_nonemptyRealCellIndices
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : RealSquareMapCellPairIndex) :
    cell ∈ main3LargeAnalytic_nonemptyRealCellIndices htheta hY hi key ↔
      cell ∈ realSquareMapCellPairIndices
        (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
        (main3UnbalancedM theta Y) ∧
      (main3LargeAnalyticFixedKeyCellTargetVectorImage
        htheta hY hi key (Sum.inl cell)).Nonempty := by
  classical
  simp [main3LargeAnalytic_nonemptyRealCellIndices]

theorem card_main3LargeAnalytic_nonemptyRealCellIndices_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) :
    (main3LargeAnalytic_nonemptyRealCellIndices htheta hY hi key).card ≤
      36 * main3UnbalancedM theta Y *
        annularDyadicScaleCount
          (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v)) := by
  classical
  calc
    (main3LargeAnalytic_nonemptyRealCellIndices htheta hY hi key).card ≤
        (realSquareMapCellPairIndices
          (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
          (main3UnbalancedM theta Y)).card := by
      exact Finset.card_filter_le _ _
    _ = 36 * main3UnbalancedM theta Y *
        annularDyadicScaleCount
          (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v)) := by simp

/-! ## A same-witness bundled real cover -/

/-- A generic bundle for the exact data used by one real fixed cell. -/
structure Main3LargeAnalyticRealCellCoverSelectionData
    (T : Finset (Fin 2 → ℤ)) (omega omegaBar : ℂ)
    (c E Delta Mmesh K T₀ A Y : ℝ) where
  cert : PrimitiveWedgeReducedTargetCoverCertificate T (2 * E) K 8
  G : SL(2, ℤ)
  H : SL(2, ℤ)
  ell_eq : cert.ell =
    main3AnchorHermitianRadialAddHom (c ^ 2) omega cert.anchor
  rho_lower : E ≤ 4 * cert.ell cert.anchor
  rho_upper : cert.ell cert.anchor ≤ 2 * E
  calibration :
    let rho := cert.ell cert.anchor
    let U := K / 2
    let V := 1 + (8 : ℝ) / 2
    let M₀ := 2 * rho * V / (2 * E)
    V = 5 ∧
      M₀ = 5 * rho / E ∧
      (5 / 4 : ℝ) ≤ M₀ ∧ M₀ ≤ 10 ∧
      4 * (U + V) = 2 * K + 20 ∧
      36 * 8 * K = 576 * E / (Mmesh * Delta)
  completion_spec :
    PrimitiveWedgeReducedTargetCoverCompletionEntryBoundSpec
      T cert.ell cert.anchor (2 * E) K 8 T₀ G H
  productHeight_le :
    let rho := cert.ell cert.anchor
    let U := K / 2
    let V := 1 + (8 : ℝ) / 2
    let M₀ := 2 * rho * V / (2 * E)
    let beta := cert.ell (fun i ↦ G i 1)
    let z := -K * beta / (2 * E)
    let L := 2 * (T₀ + 1) * reducedSlopeMatrixEntryBound U V M₀ z
    L ≤ (2 : ℝ) ^ 27 * Y * A ^ 3 * T₀ ^ 3
  log_productHeight_le :
    let rho := cert.ell cert.anchor
    let U := K / 2
    let V := 1 + (8 : ℝ) / 2
    let M₀ := 2 * rho * V / (2 * E)
    let beta := cert.ell (fun i ↦ G i 1)
    let z := -K * beta / (2 * E)
    let L := 2 * (T₀ + 1) * reducedSlopeMatrixEntryBound U V M₀ z
    Real.log (L + 1) ≤ 64 * Real.log Y
  log_scaleSum_le :
    let U := K / 2
    let V := 1 + (8 : ℝ) / 2
    Real.log (4 * (U + V)) ≤ 12 * Real.log Y
  shortest_norm_bounds :
    let rho := cert.ell cert.anchor
    let U := K / 2
    let V := 1 + (8 : ℝ) / 2
    let M₀ := 2 * rho * V / (2 * E)
    let beta := cert.ell (fun i ↦ G i 1)
    let z := -K * beta / (2 * E)
    let mu := firstSlopeSupNorm U V M₀ z
    let y := primitiveWedgeReducedTargetCoverShortestVector G H
    main3RealScaledTwoPlaceTargetSupNorm c omega omegaBar y ≤
        8 * Real.sqrt E * mu ∧
      ∀ S : ℝ, 0 < S → S ≤ 1 / mu →
        main3RealScaledTwoPlaceTargetSupNorm c omega omegaBar y ≤
          8 * Real.sqrt E / S

namespace Main3LargeAnalyticRealCellCoverSelectionData

variable {T : Finset (Fin 2 → ℤ)} {omega omegaBar : ℂ}
  {c E Delta Mmesh K T₀ A Y : ℝ}

def rho
    (S : Main3LargeAnalyticRealCellCoverSelectionData
      T omega omegaBar c E Delta Mmesh K T₀ A Y) : ℝ :=
  S.cert.ell S.cert.anchor

def U
    (_S : Main3LargeAnalyticRealCellCoverSelectionData
      T omega omegaBar c E Delta Mmesh K T₀ A Y) : ℝ :=
  K / 2

def V
    (_S : Main3LargeAnalyticRealCellCoverSelectionData
      T omega omegaBar c E Delta Mmesh K T₀ A Y) : ℝ :=
  1 + (8 : ℝ) / 2

def M₀
    (S : Main3LargeAnalyticRealCellCoverSelectionData
      T omega omegaBar c E Delta Mmesh K T₀ A Y) : ℝ :=
  2 * S.rho * S.V / (2 * E)

def beta
    (S : Main3LargeAnalyticRealCellCoverSelectionData
      T omega omegaBar c E Delta Mmesh K T₀ A Y) : ℝ :=
  S.cert.ell (fun i ↦ S.G i 1)

def z
    (S : Main3LargeAnalyticRealCellCoverSelectionData
      T omega omegaBar c E Delta Mmesh K T₀ A Y) : ℝ :=
  -K * S.beta / (2 * E)

def mu
    (S : Main3LargeAnalyticRealCellCoverSelectionData
      T omega omegaBar c E Delta Mmesh K T₀ A Y) : ℝ :=
  firstSlopeSupNorm S.U S.V S.M₀ S.z

def shortestVector
    (S : Main3LargeAnalyticRealCellCoverSelectionData
      T omega omegaBar c E Delta Mmesh K T₀ A Y) : Fin 2 → ℤ :=
  primitiveWedgeReducedTargetCoverShortestVector S.G S.H

def productHeight
    (S : Main3LargeAnalyticRealCellCoverSelectionData
      T omega omegaBar c E Delta Mmesh K T₀ A Y) : ℝ :=
  2 * (T₀ + 1) * reducedSlopeMatrixEntryBound S.U S.V S.M₀ S.z

/-- The reduced-cover specification uses the stored `cert,G,H`. -/
theorem cover_spec
    (S : Main3LargeAnalyticRealCellCoverSelectionData
      T omega omegaBar c E Delta Mmesh K T₀ A Y) :
    PrimitiveWedgeReducedTargetCoverSpec
      T S.cert.ell S.cert.anchor (2 * E) K 8 S.G S.H :=
  S.completion_spec.2.1

theorem completion_entry_le
    (S : Main3LargeAnalyticRealCellCoverSelectionData
      T omega omegaBar c E Delta Mmesh K T₀ A Y) (i j : Fin 2) :
    |((S.G i j : ℤ) : ℝ)| ≤ T₀ + 1 :=
  S.completion_spec.1 i j

/-- The actual product `G * H` obeys the stored product-height budget. -/
theorem product_entry_le
    (S : Main3LargeAnalyticRealCellCoverSelectionData
      T omega omegaBar c E Delta Mmesh K T₀ A Y) (i j : Fin 2) :
    |((((S.G * S.H) i j : ℤ) : ℝ))| ≤ S.productHeight := by
  simpa only [productHeight, U, V, M₀, rho, z, beta] using
    S.completion_spec.2.2 i j

theorem productHeight_bound
    (S : Main3LargeAnalyticRealCellCoverSelectionData
      T omega omegaBar c E Delta Mmesh K T₀ A Y) :
    S.productHeight ≤ (2 : ℝ) ^ 27 * Y * A ^ 3 * T₀ ^ 3 := by
  simpa only [productHeight, U, V, M₀, rho, z, beta] using
    S.productHeight_le

theorem log_productHeight_bound
    (S : Main3LargeAnalyticRealCellCoverSelectionData
      T omega omegaBar c E Delta Mmesh K T₀ A Y) :
    Real.log (S.productHeight + 1) ≤ 64 * Real.log Y := by
  simpa only [productHeight, U, V, M₀, rho, z, beta] using
    S.log_productHeight_le

theorem log_scaleSum_bound
    (S : Main3LargeAnalyticRealCellCoverSelectionData
      T omega omegaBar c E Delta Mmesh K T₀ A Y) :
    Real.log (4 * (S.U + S.V)) ≤ 12 * Real.log Y := by
  simpa only [U, V] using S.log_scaleSum_le

/-- Exact primitive/nonzero first-column description of the selected shortest
vector.  This says nothing about membership of that vector in `T`. -/
theorem shortestVector_spec
    (S : Main3LargeAnalyticRealCellCoverSelectionData
      T omega omegaBar c E Delta Mmesh K T₀ A Y) :
    S.shortestVector ≠ 0 ∧
      IsCoprime (S.shortestVector 0) (S.shortestVector 1) ∧
      max |2 * S.cert.ell S.shortestVector / (2 * E)|
          |2 * (main3IntegralTargetWedge S.cert.anchor S.shortestVector : ℝ) /
            K| = S.mu := by
  simpa only [shortestVector, mu, U, V, M₀, rho, z, beta] using
    S.cover_spec.shortest_original_vector

theorem mu_pos
    (S : Main3LargeAnalyticRealCellCoverSelectionData
      T omega omegaBar c E Delta Mmesh K T₀ A Y) :
    0 < S.mu := by
  unfold mu U V M₀ rho z beta
  apply firstSlopeSupNorm_pos
  · exact div_pos S.cert.K_pos (by norm_num)
  · change 0 < 1 + (8 : ℝ) / 2
    norm_num
  · change 0 <
      2 * S.cert.ell S.cert.anchor * (1 + (8 : ℝ) / 2) / (2 * E)
    exact div_pos
      (mul_pos (mul_pos (by norm_num) S.cert.anchor_pos) (by norm_num))
      S.cert.R_pos

theorem shortestVector_twoPlace_norm_le
    (S : Main3LargeAnalyticRealCellCoverSelectionData
      T omega omegaBar c E Delta Mmesh K T₀ A Y) :
    main3RealScaledTwoPlaceTargetSupNorm
        c omega omegaBar S.shortestVector ≤
      8 * Real.sqrt E * S.mu := by
  simpa only [shortestVector, mu, U, V, M₀, rho, z, beta] using
    S.shortest_norm_bounds.1

theorem shortestVector_twoPlace_reciprocalBand_le
    (S : Main3LargeAnalyticRealCellCoverSelectionData
      T omega omegaBar c E Delta Mmesh K T₀ A Y)
    {R : ℝ} (hR : 0 < R) (hRmu : R ≤ 1 / S.mu) :
    main3RealScaledTwoPlaceTargetSupNorm
        c omega omegaBar S.shortestVector ≤
      8 * Real.sqrt E / R := by
  simpa only [shortestVector, mu, U, V, M₀, rho, z, beta] using
    S.shortest_norm_bounds.2 R hR hRmu

end Main3LargeAnalyticRealCellCoverSelectionData

/-! ## Fixed-Main3 specialization and choice -/

/-- The specialized type of a coherent cover package for one fixed real
cell. -/
abbrev Main3LargeAnalyticFixedKeyRealCellCoverSelection
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : RealSquareMapCellPairIndex)
    (ha : shiftedSquareA h v < 0) : Type :=
  letI : Fact (rationalQuadraticAlgebraNoRationalRoot
    (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let a := shiftedSquareA h v
  let F := shiftedSquareFixedExplicitIntegralBasisData
    a (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
  let c := main3LargeAnalyticRealCellSignedCentre theta Y h v cell
  let T := main3LargeAnalyticFixedKeyCellTargetVectorImage
    htheta hY hi key (Sum.inl cell)
  let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let Delta := Real.sqrt
    |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)|
  let Mmesh := (main3UnbalancedM theta Y : ℝ)
  let K := (2 * E / Mmesh) / Delta
  let T₀ := main3LargeAnalyticFixedKeyTargetCoordinateRadius a Y key
  Main3LargeAnalyticRealCellCoverSelectionData T
    (sigma F.omega) (sigma (star F.omega)) c
    E Delta Mmesh K T₀ |(a : ℝ)| (Y : ℝ)

/-- The production product-height witnesses also satisfy the production
two-place shortest-vector estimate, on the exact same `cert,G,H`. -/
theorem nonempty_main3LargeAnalytic_fixedKeyRealCellCoverSelection
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
    Nonempty (Main3LargeAnalyticFixedKeyRealCellCoverSelection
      htheta hY hi key cell ha) := by
  dsimp only [Main3LargeAnalyticFixedKeyRealCellCoverSelection]
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let a := shiftedSquareA h v
  let F := shiftedSquareFixedExplicitIntegralBasisData
    a (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
  let c := main3LargeAnalyticRealCellSignedCentre theta Y h v cell
  let T := main3LargeAnalyticFixedKeyCellTargetVectorImage
    htheta hY hi key (Sum.inl cell)
  let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let Delta := Real.sqrt
    |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)|
  let Mmesh := (main3UnbalancedM theta Y : ℝ)
  let K := (2 * E / Mmesh) / Delta
  let T₀ := main3LargeAnalyticFixedKeyTargetCoordinateRadius a Y key
  let A := |(a : ℝ)|
  obtain ⟨cert, hell, hrhoLower, hrhoUpper, hcalibration,
      G, H, hcompletion, _hellBasis, _hbeta, _hzRatio, _hUInv,
      _hUUpper, _hMratio, _hVratio, _hproduct, hheight,
      hlogHeight, hlogScale⟩ :=
    exists_main3LargeAnalyticFixedKeyRealCellTargetCompletionProductHeightLogBudget
      htheta hY hi key cell ha hnonempty
  have hshort :=
    main3LargeAnalyticFixedKeyRealCell_completion_shortestVector_bound
      htheta hY hi key cell ha cert hell hrhoLower G H hcompletion
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
  · simpa only [a, F, sigma, c] using hell
  · simpa only [E] using hrhoLower
  · simpa only [E] using hrhoUpper
  · simpa only [E, K, Mmesh, Delta, a] using hcalibration
  · simpa only [T, E, K, T₀, a] using hcompletion
  · simpa only [E, K, T₀, A, a] using hheight
  · simpa only [E, K, T₀, a] using hlogHeight
  · simpa only [K] using hlogScale
  · simpa only [a, F, sigma, c, T, E, Delta, Mmesh, K, T₀] using hshort

/-- Choose one coherent package for a single real cell once nonemptiness is
known. -/
noncomputable def main3LargeAnalytic_fixedKeyRealCellCoverSelectionOfNonempty
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
    Main3LargeAnalyticFixedKeyRealCellCoverSelection
      htheta hY hi key cell ha :=
  Classical.choice
    (nonempty_main3LargeAnalytic_fixedKeyRealCellCoverSelection
      htheta hY hi key cell ha hnonempty)

/-- A choice function on the finite subtype of active real cells. -/
noncomputable def main3LargeAnalytic_realCellCoverSelection
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : shiftedSquareA h v < 0)
    (cell : ↑(main3LargeAnalytic_nonemptyRealCellIndices
      htheta hY hi key)) :
    Main3LargeAnalyticFixedKeyRealCellCoverSelection
      htheta hY hi key cell.1 ha := by
  apply main3LargeAnalytic_fixedKeyRealCellCoverSelectionOfNonempty
  exact (mem_main3LargeAnalytic_nonemptyRealCellIndices
    htheta hY hi key cell.1).mp cell.2 |>.2

end

end PellPaper
