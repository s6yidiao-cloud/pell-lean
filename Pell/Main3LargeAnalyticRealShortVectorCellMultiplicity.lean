import Pell.Main3LargeAnalyticRealCellCoverSelection
import Pell.Main3LargeAnalyticRealTwoPlaceLatticeBallGrowth
import Pell.FiniteFixedVectorFiberWeightedIncidence
import Pell.Main3RealMultiplicativeCellFixedVectorMultiplicity
import Pell.Main3LargeAnalyticComplexShortVectorRadius
import Mathlib.Tactic

/-!
# Workspace: real-cell shortest-vector multiplicity

This file connects the coherent real-cell cover selection to the fixed-scale
multiplicative packing theorem.  The first lemmas isolate the elementary
anchor/cross-product calculation from all Main3 bookkeeping.
-/

namespace PellPaper

open scoped ComplexConjugate MatrixGroups

noncomputable section

local instance main3LargeAnalyticRealShortVectorCellMultiplicity_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- The normalized wedge coordinate of the exact real reduced-cover shortest
vector retains the sharp factor `1 / Mmesh` in the cross product. -/
theorem PrimitiveWedgeReducedTargetCoverSpec.real_shortest_cross_norm_le
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (ha : a < 0) {T : Finset (Fin 2 → ℤ)} {E Mmesh : ℝ}
    (hE : 0 < E) (hMmesh : 0 < Mmesh)
    (cert : PrimitiveWedgeReducedTargetCoverCertificate T (2 * E)
      ((2 * E / Mmesh) /
        Real.sqrt |(NumberField.discr
          (rationalQuadraticAlgebra (-a)) : ℝ)|) 8)
    {G H : SL(2, ℤ)}
    (hspec : PrimitiveWedgeReducedTargetCoverSpec
      T cert.ell cert.anchor (2 * E)
        ((2 * E / Mmesh) /
          Real.sqrt |(NumberField.discr
            (rationalQuadraticAlgebra (-a)) : ℝ)|) 8 G H) :
    let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
    let Delta := Real.sqrt |(NumberField.discr
      (rationalQuadraticAlgebra (-a)) : ℝ)|
    let K := (2 * E / Mmesh) / Delta
    let rho := cert.ell cert.anchor
    let U := K / 2
    let V := 1 + (8 : ℝ) / 2
    let M₀ := 2 * rho * V / (2 * E)
    let beta := cert.ell (fun i ↦ G i 1)
    let z := -K * beta / (2 * E)
    let mu := firstSlopeSupNorm U V M₀ z
    let y := primitiveWedgeReducedTargetCoverShortestVector G H
    let anchorValue := main3IntegralTargetLinearForm (sigma F.omega) cert.anchor
    let anchorBarValue :=
      main3IntegralTargetLinearForm (sigma (star F.omega)) cert.anchor
    let yValue := main3IntegralTargetLinearForm (sigma F.omega) y
    let yBarValue := main3IntegralTargetLinearForm (sigma (star F.omega)) y
    ‖anchorBarValue * yValue - yBarValue * anchorValue‖ ≤
      E * mu / Mmesh := by
  dsimp only
  let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
  let Delta := Real.sqrt |(NumberField.discr
    (rationalQuadraticAlgebra (-a)) : ℝ)|
  let K := (2 * E / Mmesh) / Delta
  let rho := cert.ell cert.anchor
  let U := K / 2
  let V := 1 + (8 : ℝ) / 2
  let M₀ := 2 * rho * V / (2 * E)
  let beta := cert.ell (fun i ↦ G i 1)
  let z := -K * beta / (2 * E)
  let mu := firstSlopeSupNorm U V M₀ z
  let y := primitiveWedgeReducedTargetCoverShortestVector G H
  let anchorValue := main3IntegralTargetLinearForm (sigma F.omega) cert.anchor
  let anchorBarValue :=
    main3IntegralTargetLinearForm (sigma (star F.omega)) cert.anchor
  let yValue := main3IntegralTargetLinearForm (sigma F.omega) y
  let yBarValue := main3IntegralTargetLinearForm (sigma (star F.omega)) y
  have hdiscZ : NumberField.discr (rationalQuadraticAlgebra (-a)) ≠ 0 :=
    NumberField.discr_ne_zero _
  have hdiscR :
      (NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ) ≠ 0 := by
    exact_mod_cast hdiscZ
  have hDelta : 0 < Delta := by
    dsimp only [Delta]
    exact Real.sqrt_pos.2 (abs_pos.mpr hdiscR)
  have hK : 0 < K := by dsimp only [K]; positivity
  have hshort := hspec.shortest_original_vector
  dsimp only at hshort
  change y ≠ 0 ∧ IsCoprime (y 0) (y 1) ∧
    max |2 * cert.ell y / (2 * E)|
      |2 * (main3IntegralTargetWedge cert.anchor y : ℝ) / K| = mu at hshort
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
      ‖anchorBarValue * yValue - yBarValue * anchorValue‖ =
        |(main3IntegralTargetWedge cert.anchor y : ℝ)| * Delta := by
    have hwedgeNorm :=
      norm_main3IntegralTargetLinearForm_wedge_eq F sigma cert.anchor y
    simpa only [anchorBarValue, anchorValue, yBarValue, yValue,
      sigma, Delta] using hwedgeNorm
  rw [hcrossEq]
  calc
    |(main3IntegralTargetWedge cert.anchor y : ℝ)| * Delta ≤
        (K * mu / 2) * Delta :=
      mul_le_mul_of_nonneg_right hwedge hDelta.le
    _ = E * mu / Mmesh := by
      dsimp only [K]
      field_simp [hDelta.ne', hMmesh.ne']

/-- A lower bound for a real anchor, a wedge/cross-product bound, and one
literal target-cell endpoint bound control the shortest vector relative to
that endpoint. -/
theorem norm_yBar_sub_realEndpoint_mul_y_le_of_anchor_cross
    {anchorValue anchorBarValue yValue yBarValue : ℂ}
    {E M mu S s p tau : ℝ}
    (hE : 0 < E) (hM : 0 < M) (hmu : 0 < mu)
    (hS : 0 < S) (hband : S ≤ 1 / mu) (hs : 0 < s)
    (hanchorScale : Real.sqrt E / 2 ≤ s * ‖anchorValue‖)
    (hanchorRatio : anchorBarValue / anchorValue = (p : ℂ))
    (hcross : ‖anchorBarValue * yValue - yBarValue * anchorValue‖ ≤
      E * mu / M)
    (hendpoint : |p - tau * s ^ 2| ≤ s ^ 2 / M)
    (hyScaled : s * ‖yValue‖ ≤ 8 * Real.sqrt E / S) :
    ‖yBarValue - ((tau * s ^ 2 : ℝ) : ℂ) * yValue‖ ≤
      10 * Real.sqrt E / S * s / M := by
  have hsqrt : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  have hanchorNorm : 0 < ‖anchorValue‖ := by
    by_contra hnot
    have hzero : ‖anchorValue‖ = 0 :=
      le_antisymm (le_of_not_gt hnot) (norm_nonneg anchorValue)
    rw [hzero, mul_zero] at hanchorScale
    nlinarith
  have hanchor : anchorValue ≠ 0 := norm_pos_iff.mp hanchorNorm
  have hanchorBar : anchorBarValue = (p : ℂ) * anchorValue :=
    (div_eq_iff hanchor).mp hanchorRatio
  have hcrossFactor :
      ‖anchorBarValue * yValue - yBarValue * anchorValue‖ =
        ‖anchorValue‖ * ‖(p : ℂ) * yValue - yBarValue‖ := by
    rw [hanchorBar]
    have hid :
        (p : ℂ) * anchorValue * yValue - yBarValue * anchorValue =
          anchorValue * ((p : ℂ) * yValue - yBarValue) := by ring
    rw [hid, norm_mul]
  have hdiffCross : ‖(p : ℂ) * yValue - yBarValue‖ ≤
      E * mu / (M * ‖anchorValue‖) := by
    apply (le_div_iff₀ (mul_pos hM hanchorNorm)).2
    calc
      ‖(p : ℂ) * yValue - yBarValue‖ * (M * ‖anchorValue‖) =
          M * (‖anchorValue‖ *
            ‖(p : ℂ) * yValue - yBarValue‖) := by ring
      _ = M *
          ‖anchorBarValue * yValue - yBarValue * anchorValue‖ := by
        rw [hcrossFactor]
      _ ≤ M * (E * mu / M) :=
        mul_le_mul_of_nonneg_left hcross hM.le
      _ = E * mu := by field_simp [hM.ne']
  have hanchorSqrt : Real.sqrt E ≤ 2 * s * ‖anchorValue‖ := by
    nlinarith
  have hEdiv : E / ‖anchorValue‖ ≤ 2 * Real.sqrt E * s := by
    apply (div_le_iff₀ hanchorNorm).2
    calc
      E = Real.sqrt E * Real.sqrt E := by
        nlinarith [Real.sq_sqrt hE.le]
      _ ≤ Real.sqrt E * (2 * s * ‖anchorValue‖) :=
        mul_le_mul_of_nonneg_left hanchorSqrt hsqrt.le
      _ = (2 * Real.sqrt E * s) * ‖anchorValue‖ := by ring
  have hmuUpper : mu ≤ 1 / S := by
    apply (le_div_iff₀ hS).2
    have hprod := (le_div_iff₀ hmu).1 hband
    simpa only [one_mul, mul_comm] using hprod
  have hdiffAnchor :
      ‖yBarValue - (p : ℂ) * yValue‖ ≤
        2 * Real.sqrt E / S * s / M := by
    rw [show yBarValue - (p : ℂ) * yValue =
        -((p : ℂ) * yValue - yBarValue) by ring, norm_neg]
    calc
      ‖(p : ℂ) * yValue - yBarValue‖ ≤
          E * mu / (M * ‖anchorValue‖) := hdiffCross
      _ = (E / ‖anchorValue‖) * (mu / M) := by
        field_simp [hM.ne', hanchorNorm.ne']
      _ ≤ (2 * Real.sqrt E * s) * (mu / M) := by
        gcongr
      _ ≤ (2 * Real.sqrt E * s) * ((1 / S) / M) := by
        gcongr
      _ = 2 * Real.sqrt E / S * s / M := by ring
  have hendpointTerm :
      ‖((p - tau * s ^ 2 : ℝ) : ℂ) * yValue‖ ≤
        8 * Real.sqrt E / S * s / M := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |p - tau * s ^ 2| * ‖yValue‖ ≤
          (s ^ 2 / M) * ‖yValue‖ :=
        mul_le_mul_of_nonneg_right hendpoint (norm_nonneg yValue)
      _ = (s / M) * (s * ‖yValue‖) := by ring
      _ ≤ (s / M) * (8 * Real.sqrt E / S) :=
        mul_le_mul_of_nonneg_left hyScaled (by positivity)
      _ = 8 * Real.sqrt E / S * s / M := by ring
  calc
    ‖yBarValue - ((tau * s ^ 2 : ℝ) : ℂ) * yValue‖ =
        ‖(yBarValue - (p : ℂ) * yValue) +
          ((p - tau * s ^ 2 : ℝ) : ℂ) * yValue‖ := by
      congr 1
      push_cast
      ring
    _ ≤ ‖yBarValue - (p : ℂ) * yValue‖ +
          ‖((p - tau * s ^ 2 : ℝ) : ℂ) * yValue‖ := norm_add_le _ _
    _ ≤ 2 * Real.sqrt E / S * s / M +
          8 * Real.sqrt E / S * s / M :=
      add_le_add hdiffAnchor hendpointTerm
    _ = 10 * Real.sqrt E / S * s / M := by ring

/-- Dividing a quadratic endpoint estimate by the positive cell centre gives
the linearized form used by multiplicative mesh packing. -/
theorem abs_norm_linearized_le_of_norm_quadratic_near
    {yValue yBarValue : ℂ} {H M s tau : ℝ}
    (hs : 0 < s) (htau : 0 ≤ tau)
    (hnear :
      ‖yBarValue - ((tau * s ^ 2 : ℝ) : ℂ) * yValue‖ ≤
        H * s / M) :
    |tau * (s * ‖yValue‖) - ‖yBarValue‖ / s| ≤ H / M := by
  have hscalar :
      ‖((tau * s ^ 2 : ℝ) : ℂ) * yValue‖ =
        tau * s ^ 2 * ‖yValue‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg htau (sq_nonneg s))]
  have hreverse :
      |tau * s ^ 2 * ‖yValue‖ - ‖yBarValue‖| ≤ H * s / M := by
    rw [abs_sub_comm]
    calc
      |‖yBarValue‖ - tau * s ^ 2 * ‖yValue‖| =
          |‖yBarValue‖ -
            ‖((tau * s ^ 2 : ℝ) : ℂ) * yValue‖| := by rw [hscalar]
      _ ≤ ‖yBarValue - ((tau * s ^ 2 : ℝ) : ℂ) * yValue‖ :=
        abs_norm_sub_norm_le _ _
      _ ≤ H * s / M := hnear
  have hid :
      |tau * (s * ‖yValue‖) - ‖yBarValue‖ / s| =
        |tau * s ^ 2 * ‖yValue‖ - ‖yBarValue‖| / s := by
    have hinner : tau * (s * ‖yValue‖) - ‖yBarValue‖ / s =
        (tau * s ^ 2 * ‖yValue‖ - ‖yBarValue‖) / s := by
      field_simp [hs.ne']
    rw [hinner, abs_div, abs_of_pos hs]
  rw [hid]
  apply (div_le_iff₀ hs).2
  calc
    |tau * s ^ 2 * ‖yValue‖ - ‖yBarValue‖| ≤ H * s / M := hreverse
    _ = (H / M) * s := by ring

/-- On an ambient real cell index, the absolute signed centre is the positive
annular multiplicative centre. -/
theorem abs_main3LargeAnalyticRealCellSignedCentre_eq_center
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v : ℕ}
    (cell : RealSquareMapCellPairIndex)
    (hcell : cell ∈ realSquareMapCellPairIndices
      (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
      (main3UnbalancedM theta Y)) :
    |main3LargeAnalyticRealCellSignedCentre theta Y h v cell| =
      annularMultiplicativeCenter
        (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
        (main3UnbalancedM theta Y) cell.1.2.1 cell.1.2.2 := by
  have heps : cell.1.1 ∈ annularSigns :=
    (mem_annularMultiplicativeCellIndices.mp
      (Finset.mem_product.mp hcell).1).1
  have hepsCases : cell.1.1 = -1 ∨ cell.1.1 = 1 := by
    simpa only [annularSigns, Finset.mem_insert, Finset.mem_singleton] using heps
  have hcenterNonneg : 0 ≤ annularMultiplicativeCenter
      (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
      (main3UnbalancedM theta Y) cell.1.2.1 cell.1.2.2 := by
    unfold annularMultiplicativeCenter annularDyadicStart annularLowerRadius
      localRatioMeshStep
    positivity
  rcases hepsCases with heps | heps <;>
    simp [main3LargeAnalyticRealCellSignedCentre, heps,
      abs_of_nonneg hcenterNonneg]

/-- For one coherent active real-cell cover, a reciprocal-minimum band forces
its shortest vector into the quadratic neighborhood of the literal target
right endpoint.  Only the certificate anchor is converted back to an actual
coordinate point. -/
theorem Main3LargeAnalyticRealCellCoverSelectionData.shortestVector_quadraticEndpoint_near
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) (cell : RealSquareMapCellPairIndex)
    (ha : shiftedSquareA h v < 0)
    (hcell : cell ∈ realSquareMapCellPairIndices
      (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
      (main3UnbalancedM theta Y))
    (Q : Main3LargeAnalyticFixedKeyRealCellCoverSelection
      htheta hY hi key cell ha)
    {S : ℝ} (hS : 0 < S) (hband : S ≤ 1 / Q.mu) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let a := shiftedSquareA h v
    let F := shiftedSquareFixedExplicitIntegralBasisData
      a (main3LargeAnalytic_shift_squarefree hi)
    let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
    let M := main3UnbalancedM theta Y
    let s := annularMultiplicativeCenter
      (shiftedSquareEmbeddingScaleLoss a) M cell.1.2.1 cell.1.2.2
    let tau := 1 + (cell.2 : ℝ) / (M : ℝ)
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    let y := Q.shortestVector
    let yValue := main3IntegralTargetLinearForm (sigma F.omega) y
    let yBarValue := main3IntegralTargetLinearForm (sigma (star F.omega)) y
    ‖yBarValue - ((tau * s ^ 2 : ℝ) : ℂ) * yValue‖ ≤
      10 * Real.sqrt E / S * s / (M : ℝ) := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let a := shiftedSquareA h v
  let F := shiftedSquareFixedExplicitIntegralBasisData
    a (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
  let M := main3UnbalancedM theta Y
  let s := annularMultiplicativeCenter
    (shiftedSquareEmbeddingScaleLoss a) M cell.1.2.1 cell.1.2.2
  let c := main3LargeAnalyticRealCellSignedCentre theta Y h v cell
  let tau := 1 + (cell.2 : ℝ) / (M : ℝ)
  let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let y := Q.shortestVector
  let anchorValue := main3IntegralTargetLinearForm
    (sigma F.omega) Q.cert.anchor
  let anchorBarValue := main3IntegralTargetLinearForm
    (sigma (star F.omega)) Q.cert.anchor
  let yValue := main3IntegralTargetLinearForm (sigma F.omega) y
  let yBarValue := main3IntegralTargetLinearForm (sigma (star F.omega)) y
  have hFscale : 1 ≤ shiftedSquareEmbeddingScaleLoss a := by
    have haOne : (1 : ℝ) ≤ |(a : ℝ)| := by
      exact_mod_cast Int.one_le_abs (by dsimp only [a]; exact ne_of_lt ha)
    unfold shiftedSquareEmbeddingScaleLoss
    nlinarith
  have hs : 0 < s := by
    dsimp only [s, annularMultiplicativeCenter]
    exact mul_pos (annularDyadicStart_pos hFscale cell.1.2.1)
      (pow_pos (by unfold localRatioMeshStep; positivity) _)
  have habsC : |c| = s := by
    simpa only [a, M, c, s] using
      abs_main3LargeAnalyticRealCellSignedCentre_eq_center cell hcell
  have hE : 0 < E := by
    dsimp only [E]
    exact main3LargeAnalyticFixedKeyTargetScaleUpper_pos_of_mem
      htheta hY hi key (Sum.inl cell) Q.cert.anchor_mem
  have hMnat : 6 ≤ M := by
    dsimp only [M]
    exact six_le_main3UnbalancedM htheta hY
  have hMreal : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le (by omega) hMnat)
  have hmu : 0 < Q.mu := Q.mu_pos
  obtain ⟨anchorPoint, hanchorPoint, hanchorEq⟩ :=
    (mem_main3LargeAnalyticFixedKeyCellTargetVectorImage_iff
      htheta hY hi key (Sum.inl cell) Q.cert.anchor).mp Q.cert.anchor_mem
  let target := main3EmbeddingTargetRatio
    (sigma F.omega) (sigma (star F.omega)) anchorPoint
  have hgeometry :=
    main3LargeAnalytic_realCellCoordinatePointImage_embeddingRatio_geometry
      htheta hY hi key cell ha hanchorPoint
  dsimp only at hgeometry
  have htargetIm : target.im = 0 := by
    simpa only [target, a, F, sigma] using hgeometry.1.2.2.2.1
  have htargetPos : 0 < target.re := by
    simpa only [target, a, F, sigma] using hgeometry.1.2.2.2.2.2
  have htargetCell : realSquareMapTargetCell (M : ℝ) s cell.2 target.re := by
    simpa only [target, a, F, sigma, M, s] using hgeometry.2.2
  have hanchorRatio : anchorBarValue / anchorValue = (target.re : ℂ) := by
    have htargetEq : target = anchorBarValue / anchorValue := by
      dsimp only [target]
      change
        main3IntegralTargetLinearForm (sigma (star F.omega))
              (shiftedSquareCoordinatePointTargetVector anchorPoint) /
            main3IntegralTargetLinearForm (sigma F.omega)
              (shiftedSquareCoordinatePointTargetVector anchorPoint) =
          anchorBarValue / anchorValue
      rw [hanchorEq]
    calc
      anchorBarValue / anchorValue = target := htargetEq.symm
      _ = (target.re : ℂ) := by
        apply Complex.ext
        · simp
        · simpa only [Complex.ofReal_im] using htargetIm
  have hellAnchor : Q.cert.ell Q.cert.anchor =
      c ^ 2 * ‖anchorValue‖ ^ 2 := by
    calc
      Q.cert.ell Q.cert.anchor =
          main3AnchorHermitianRadialAddHom (c ^ 2)
            (sigma F.omega) Q.cert.anchor Q.cert.anchor := by
        simpa only [a, F, sigma, c] using
          congrArg (fun ell : (Fin 2 → ℤ) →+ ℝ ↦ ell Q.cert.anchor) Q.ell_eq
      _ = c ^ 2 * ‖main3IntegralTargetLinearForm
          (sigma F.omega) Q.cert.anchor‖ ^ 2 :=
        main3AnchorHermitianRadialAddHom_self (c ^ 2)
          (sigma F.omega) Q.cert.anchor
      _ = c ^ 2 * ‖anchorValue‖ ^ 2 := by rfl
  have hanchorScaleSq :
      E ≤ 4 * (s * ‖anchorValue‖) ^ 2 := by
    calc
      E ≤ 4 * Q.cert.ell Q.cert.anchor := by
        simpa only [E] using Q.rho_lower
      _ = 4 * (s * ‖anchorValue‖) ^ 2 := by
        rw [hellAnchor, ← sq_abs, habsC]
        ring
  have hanchorScale : Real.sqrt E / 2 ≤ s * ‖anchorValue‖ := by
    have hsqrtSq : (Real.sqrt E) ^ 2 = E := Real.sq_sqrt hE.le
    have hnonneg : 0 ≤ s * ‖anchorValue‖ := by positivity
    have htwice : Real.sqrt E ≤ 2 * (s * ‖anchorValue‖) := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg E) (by positivity)).mp
      rw [hsqrtSq]
      nlinarith
    linarith
  have hcross :
      ‖anchorBarValue * yValue - yBarValue * anchorValue‖ ≤
        E * Q.mu / (M : ℝ) := by
    have hc := Q.cover_spec.real_shortest_cross_norm_le F ha hE hMreal Q.cert
    simpa only [a, F, sigma, M, E, y, anchorValue, anchorBarValue,
      yValue, yBarValue, Main3LargeAnalyticRealCellCoverSelectionData.mu,
      Main3LargeAnalyticRealCellCoverSelectionData.U,
      Main3LargeAnalyticRealCellCoverSelectionData.V,
      Main3LargeAnalyticRealCellCoverSelectionData.M₀,
      Main3LargeAnalyticRealCellCoverSelectionData.rho,
      Main3LargeAnalyticRealCellCoverSelectionData.z,
      Main3LargeAnalyticRealCellCoverSelectionData.beta,
      Main3LargeAnalyticRealCellCoverSelectionData.shortestVector] using hc
  have hendpoint : |target.re - tau * s ^ 2| ≤ s ^ 2 / (M : ℝ) := by
    simpa only [tau] using
      abs_sub_realSquareMapTargetCell_rightEndpoint_mul_sq_le
        hMreal hs htargetCell
  have hyScaled : s * ‖yValue‖ ≤ 8 * Real.sqrt E / S := by
    have hy := Q.shortestVector_twoPlace_reciprocalBand_le hS hband
    calc
      s * ‖yValue‖ = |c| * ‖main3IntegralTargetLinearForm
          (sigma F.omega) Q.shortestVector‖ := by
        rw [habsC]
      _ ≤ main3RealScaledTwoPlaceTargetSupNorm c
          (sigma F.omega) (sigma (star F.omega)) Q.shortestVector :=
        le_max_left _ _
      _ ≤ 8 * Real.sqrt E / S := by
        simpa only [a, F, sigma, c, E] using hy
  exact norm_yBar_sub_realEndpoint_mul_y_le_of_anchor_cross
    hE hMreal hmu hS hband hs hanchorScale hanchorRatio hcross
      hendpoint hyScaled

set_option maxHeartbeats 800000 in
/-- The preceding quadratic endpoint estimate in the exact normalized form
consumed by fixed-scale multiplicative mesh packing. -/
theorem Main3LargeAnalyticRealCellCoverSelectionData.shortestVector_fixedScale_linearized_near
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) (cell : RealSquareMapCellPairIndex)
    (ha : shiftedSquareA h v < 0)
    (hcell : cell ∈ realSquareMapCellPairIndices
      (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
      (main3UnbalancedM theta Y))
    (Q : Main3LargeAnalyticFixedKeyRealCellCoverSelection
      htheta hY hi key cell ha)
    {S : ℝ} (hS : 0 < S) (hband : S ≤ 1 / Q.mu) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let a := shiftedSquareA h v
    let F := shiftedSquareFixedExplicitIntegralBasisData
      a (main3LargeAnalytic_shift_squarefree hi)
    let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
    let M := main3UnbalancedM theta Y
    let b := annularDyadicStart
      (shiftedSquareEmbeddingScaleLoss a) cell.1.2.1
    let t := localRatioMeshStep M
    let tau := 1 + (cell.2 : ℝ) / (M : ℝ)
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    let y := Q.shortestVector
    let yValue := main3IntegralTargetLinearForm (sigma F.omega) y
    let yBarValue := main3IntegralTargetLinearForm (sigma (star F.omega)) y
    |tau * (t ^ cell.1.2.2 * (b * ‖yValue‖)) -
        (‖yBarValue‖ / b) / t ^ cell.1.2.2| ≤
      (10 * Real.sqrt E / S) / (M : ℝ) := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let a := shiftedSquareA h v
  let F := shiftedSquareFixedExplicitIntegralBasisData
    a (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
  let M := main3UnbalancedM theta Y
  let b := annularDyadicStart
    (shiftedSquareEmbeddingScaleLoss a) cell.1.2.1
  let t := localRatioMeshStep M
  let s := annularMultiplicativeCenter
    (shiftedSquareEmbeddingScaleLoss a) M cell.1.2.1 cell.1.2.2
  let tau := 1 + (cell.2 : ℝ) / (M : ℝ)
  let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let y := Q.shortestVector
  let yValue := main3IntegralTargetLinearForm (sigma F.omega) y
  let yBarValue := main3IntegralTargetLinearForm (sigma (star F.omega)) y
  have hFscale : 1 ≤ shiftedSquareEmbeddingScaleLoss a := by
    have haOne : (1 : ℝ) ≤ |(a : ℝ)| := by
      exact_mod_cast Int.one_le_abs (by dsimp only [a]; exact ne_of_lt ha)
    unfold shiftedSquareEmbeddingScaleLoss
    nlinarith
  have hs : 0 < s := by
    dsimp only [s, annularMultiplicativeCenter]
    exact mul_pos (annularDyadicStart_pos hFscale cell.1.2.1)
      (pow_pos (by unfold localRatioMeshStep; positivity) _)
  have hMnat : 6 ≤ M := by
    dsimp only [M]
    exact six_le_main3UnbalancedM htheta hY
  have hMreal : (0 : ℝ) < M := by
    exact_mod_cast (lt_of_lt_of_le (by omega) hMnat)
  have hoffset : cell.2 ∈ realSquareMapTargetOffsets :=
    (Finset.mem_product.mp hcell).2
  have hoffsetLower : (-1 : ℤ) ≤ cell.2 :=
    (Finset.mem_Icc.mp (by
      simpa only [realSquareMapTargetOffsets] using hoffset)).1
  have hoffsetLowerReal : (-1 : ℝ) ≤ (cell.2 : ℝ) := by
    exact_mod_cast hoffsetLower
  have htau : 0 ≤ tau := by
    have hMge : (6 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMnat
    dsimp only [tau]
    rw [show 1 + (cell.2 : ℝ) / (M : ℝ) =
        ((M : ℝ) + (cell.2 : ℝ)) / (M : ℝ) by
      field_simp [hMreal.ne']]
    exact div_nonneg (by linarith) hMreal.le
  have hquad := Q.shortestVector_quadraticEndpoint_near
    htheta hY hi key cell ha hcell hS hband
  dsimp only at hquad
  have hlinear := abs_norm_linearized_le_of_norm_quadratic_near
    hs htau hquad
  simpa only [s, annularMultiplicativeCenter, b, t, tau, M, a,
    div_eq_mul_inv,
    mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using hlinear

set_option maxHeartbeats 1000000 in
/-- At one fixed annular dyadic scale, active real cells whose coherent covers
have one common shortest vector have multiplicity bounded independently of
the mesh size. -/
theorem card_main3RealCells_with_common_shortestVector_at_scale_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : shiftedSquareA h v < 0) {S : ℝ} (hS : 0 < S)
    (j : ℕ) (y : Fin 2 → ℤ)
    (J : Finset RealSquareMapCellPairIndex)
    (hJ : J ⊆ main3LargeAnalytic_nonemptyRealCellIndices htheta hY hi key)
    (hscale : ∀ cell ∈ J, cell.1.2.1 = j)
    (Q : ∀ c : {cell // cell ∈ J},
      Main3LargeAnalyticFixedKeyRealCellCoverSelection
        htheta hY hi key c.1 ha)
    (hband : ∀ c : {cell // cell ∈ J}, S ≤ 1 / (Q c).mu)
    (hsame : ∀ c : {cell // cell ∈ J}, (Q c).shortestVector = y) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let a := shiftedSquareA h v
    let F := shiftedSquareFixedExplicitIntegralBasisData
      a (main3LargeAnalytic_shift_squarefree hi)
    let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
    let b := annularDyadicStart
      (shiftedSquareEmbeddingScaleLoss a) j
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    let r := main3RealScaledTwoPlaceTargetSupNorm b
      (sigma F.omega) (sigma (star F.omega)) y
    (J.card : ℝ) ≤ 18 + 1620000 * Real.sqrt E / (S * r) := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let a := shiftedSquareA h v
  let F := shiftedSquareFixedExplicitIntegralBasisData
    a (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
  let M := main3UnbalancedM theta Y
  let b := annularDyadicStart
    (shiftedSquareEmbeddingScaleLoss a) j
  let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let yValue := main3IntegralTargetLinearForm (sigma F.omega) y
  let yBarValue := main3IntegralTargetLinearForm (sigma (star F.omega)) y
  let A := b * ‖yValue‖
  let B := ‖yBarValue‖ / b
  let r := main3RealScaledTwoPlaceTargetSupNorm b
    (sigma F.omega) (sigma (star F.omega)) y
  by_cases hJempty : J = ∅
  · subst J
    simp only [Finset.card_empty, Nat.cast_zero]
    have hrNonneg : 0 ≤ r := by
      dsimp only [r, main3RealScaledTwoPlaceTargetSupNorm]
      exact (mul_nonneg (abs_nonneg b) (norm_nonneg _)).trans
        (le_max_left _ _)
    have : 0 ≤ 1620000 * Real.sqrt E / (S * r) :=
      div_nonneg (by positivity) (mul_nonneg hS.le hrNonneg)
    linarith
  · obtain ⟨cell₀, hcell₀⟩ := Finset.nonempty_iff_ne_empty.mpr hJempty
    let c₀ : {cell // cell ∈ J} := ⟨cell₀, hcell₀⟩
    have hyNonzero : y ≠ 0 := by
      rw [← hsame c₀]
      exact (Q c₀).shortestVector_spec.1
    have hFscale : 1 ≤ shiftedSquareEmbeddingScaleLoss a := by
      have haOne : (1 : ℝ) ≤ |(a : ℝ)| := by
        exact_mod_cast Int.one_le_abs (by dsimp only [a]; exact ne_of_lt ha)
      unfold shiftedSquareEmbeddingScaleLoss
      nlinarith
    have hb : 0 < b := by
      dsimp only [b]
      exact annularDyadicStart_pos hFscale j
    have hproduct : 1 ≤ ‖yValue‖ * ‖yBarValue‖ := by
      simpa only [yValue, yBarValue, a, F, sigma] using
        one_le_mul_norm_main3IntegralTargetLinearForm_fixedBasis_positiveRealPlaces
          ha F y hyNonzero
    have hyValuePos : 0 < ‖yValue‖ := by
      by_contra hnot
      have hzero : ‖yValue‖ = 0 :=
        le_antisymm (le_of_not_gt hnot) (norm_nonneg yValue)
      rw [hzero, zero_mul] at hproduct
      norm_num at hproduct
    have hA : 0 < A := by dsimp only [A]; positivity
    have hB : 0 ≤ B := by dsimp only [B]; positivity
    have hrScalar : 0 < max |A| |B| := by
      exact (abs_pos.mpr hA.ne').trans_le (le_max_left _ _)
    have hrEq : max |A| |B| = r := by
      dsimp only [A, B, r, main3RealScaledTwoPlaceTargetSupNorm,
        yValue, yBarValue]
      rw [abs_of_pos hb, abs_of_nonneg (mul_nonneg hb.le (norm_nonneg _)),
        abs_of_nonneg (div_nonneg (norm_nonneg _) hb.le)]
    have hMnat : 6 ≤ M := by
      dsimp only [M]
      exact six_le_main3UnbalancedM htheta hY
    have hJambient : J ⊆ realSquareMapCellPairIndices
        (shiftedSquareEmbeddingScaleLoss a) M := by
      intro cell hcell
      have hactive :=
        (mem_main3LargeAnalytic_nonemptyRealCellIndices
          htheta hY hi key cell).mp (hJ hcell)
      simpa only [a, M] using hactive.1
    have hnear : ∀ cell ∈ J,
        |(1 + (cell.2 : ℝ) / (M : ℝ)) *
            (localRatioMeshStep M ^ cell.1.2.2 * A) -
          B / localRatioMeshStep M ^ cell.1.2.2| ≤
        (10 * Real.sqrt E / S) / (M : ℝ) := by
      intro cell hcell
      let c : {cell // cell ∈ J} := ⟨cell, hcell⟩
      have hnearCell := (Q c).shortestVector_fixedScale_linearized_near
        htheta hY hi key cell ha (hJambient hcell) hS (hband c)
      dsimp only at hnearCell
      rw [hsame c, hscale cell hcell] at hnearCell
      simpa only [a, F, sigma, M, b, E, yValue, yBarValue, A, B] using
        hnearCell
    have hcount := card_realSquareMapCellPairs_fixedVectorNear_at_scale_le
      hMnat (by positivity : 0 ≤ 10 * Real.sqrt E / S) hrScalar
        J hJambient hscale hnear
    rw [hrEq] at hcount
    calc
      (J.card : ℝ) ≤ 18 + 162000 * (10 * Real.sqrt E / S) / r := hcount
      _ = 18 + 1620000 * Real.sqrt E / (S * r) := by ring

/-- Changing a positive two-place determinant-one scale from `s` to a left
endpoint `b` with `b ≤ s ≤ 9b` costs at most a factor nine. -/
theorem main3RealScaledTwoPlaceTargetSupNorm_leftEndpoint_le_nine_mul
    (b s : ℝ) (omega omegaBar : ℂ) (y : Fin 2 → ℤ)
    (hb : 0 < b) (hs : 0 < s) (hbs : b ≤ s) (hsb : s ≤ 9 * b) :
    main3RealScaledTwoPlaceTargetSupNorm b omega omegaBar y ≤
      9 * main3RealScaledTwoPlaceTargetSupNorm s omega omegaBar y := by
  let r := main3RealScaledTwoPlaceTargetSupNorm s omega omegaBar y
  have hrNonneg : 0 ≤ r := by
    dsimp only [r, main3RealScaledTwoPlaceTargetSupNorm]
    exact (mul_nonneg (abs_nonneg s) (norm_nonneg _)).trans
      (le_max_left _ _)
  have hfirstS : s * ‖main3IntegralTargetLinearForm omega y‖ ≤ r := by
    dsimp only [r, main3RealScaledTwoPlaceTargetSupNorm]
    rw [abs_of_pos hs]
    exact le_max_left _ _
  have hsecondS :
      ‖main3IntegralTargetLinearForm omegaBar y‖ / s ≤ r := by
    dsimp only [r, main3RealScaledTwoPlaceTargetSupNorm]
    rw [abs_of_pos hs]
    exact le_max_right _ _
  have hfirst : b * ‖main3IntegralTargetLinearForm omega y‖ ≤ 9 * r := by
    calc
      b * ‖main3IntegralTargetLinearForm omega y‖ ≤
          s * ‖main3IntegralTargetLinearForm omega y‖ :=
        mul_le_mul_of_nonneg_right hbs (norm_nonneg _)
      _ ≤ r := hfirstS
      _ ≤ 9 * r := by nlinarith
  have hratio : s / b ≤ 9 := by
    exact (div_le_iff₀ hb).2 (by simpa only [mul_comm] using hsb)
  have hsecond :
      ‖main3IntegralTargetLinearForm omegaBar y‖ / b ≤ 9 * r := by
    have hid : ‖main3IntegralTargetLinearForm omegaBar y‖ / b =
        (s / b) *
          (‖main3IntegralTargetLinearForm omegaBar y‖ / s) := by
      field_simp [hb.ne', hs.ne']
    rw [hid]
    calc
      (s / b) * (‖main3IntegralTargetLinearForm omegaBar y‖ / s) ≤
          9 * (‖main3IntegralTargetLinearForm omegaBar y‖ / s) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ ≤ 9 * r := mul_le_mul_of_nonneg_left hsecondS (by norm_num)
  unfold main3RealScaledTwoPlaceTargetSupNorm
  rw [abs_of_pos hb]
  exact max_le hfirst hsecond

/-- The real-cover determinant relation supplies the same strong
`sqrt(K)/2` reciprocal-minimum cutoff as in the complex branch. -/
theorem Main3LargeAnalyticRealCellCoverSelectionData.sqrt_K_div_two_le_reciprocal_mu
    {T : Finset (Fin 2 → ℤ)} {omega omegaBar : ℂ}
    {c E Delta Mmesh K T₀ A Y : ℝ}
    (Q : Main3LargeAnalyticRealCellCoverSelectionData
      T omega omegaBar c E Delta Mmesh K T₀ A Y) :
    Real.sqrt K / 2 ≤ 1 / Q.mu := by
  have hspec := Q.cover_spec
  unfold PrimitiveWedgeReducedTargetCoverSpec at hspec
  dsimp only at hspec
  rcases hspec with
    ⟨_hcolumn, _hminimum, _hall, _hM₀one, _hmu, _hdelta,
      _hdeltaEq, hmuSq, _hratioEq, _hratioLe, _hproduct,
      _huniversal, _hcard, _hprimitive, _hrecover, _hsubset,
      _hAtwo, _hA, _hB, _hthin, _hfull⟩
  have hmuSqQ : Q.mu ^ 2 ≤ Q.M₀ / (Q.U * Q.V) := by
    simpa only [Main3LargeAnalyticRealCellCoverSelectionData.mu,
      Main3LargeAnalyticRealCellCoverSelectionData.U,
      Main3LargeAnalyticRealCellCoverSelectionData.V,
      Main3LargeAnalyticRealCellCoverSelectionData.M₀,
      Main3LargeAnalyticRealCellCoverSelectionData.rho,
      Main3LargeAnalyticRealCellCoverSelectionData.z,
      Main3LargeAnalyticRealCellCoverSelectionData.beta] using hmuSq
  have hK : 0 < K := Q.cert.K_pos
  have hUV : Q.U * Q.V = 5 * K / 2 := by
    dsimp only [Main3LargeAnalyticRealCellCoverSelectionData.U,
      Main3LargeAnalyticRealCellCoverSelectionData.V]
    ring
  have hM₀Upper : Q.M₀ ≤ 10 := by
    simpa only [Main3LargeAnalyticRealCellCoverSelectionData.M₀,
      Main3LargeAnalyticRealCellCoverSelectionData.rho,
      Main3LargeAnalyticRealCellCoverSelectionData.V] using
        Q.calibration.2.2.2.1
  have hKmuSq : K * Q.mu ^ 2 ≤ 4 := by
    calc
      K * Q.mu ^ 2 ≤ K * (Q.M₀ / (Q.U * Q.V)) := by gcongr
      _ = (2 / 5 : ℝ) * Q.M₀ := by
        rw [hUV]
        field_simp [hK.ne']
      _ ≤ 4 := by nlinarith
  have hsqrtK : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have hprodNonneg : 0 ≤ Real.sqrt K * Q.mu :=
    mul_nonneg hsqrtK.le Q.mu_pos.le
  have hprodSq : (Real.sqrt K * Q.mu) ^ 2 ≤ 2 ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hK.le]
    norm_num
    exact hKmuSq
  have hprod : Real.sqrt K * Q.mu ≤ 2 :=
    (sq_le_sq₀ hprodNonneg (by norm_num)).mp hprodSq
  apply (le_div_iff₀ Q.mu_pos).2
  nlinarith

/-- A mesh centre with index below `2M` lies between its dyadic left endpoint
and nine times that endpoint. -/
theorem annularMultiplicativeCenter_between_start_and_nine
    {F : ℝ} {M j k : ℕ} (hF : 1 ≤ F) (hM : 0 < M)
    (hk : k < 2 * M) :
    annularDyadicStart F j ≤ annularMultiplicativeCenter F M j k ∧
      annularMultiplicativeCenter F M j k ≤ 9 * annularDyadicStart F j := by
  have hb : 0 ≤ annularDyadicStart F j := (annularDyadicStart_pos hF j).le
  have ht : 1 ≤ localRatioMeshStep M := by
    unfold localRatioMeshStep
    have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
    have : (0 : ℝ) ≤ 1 / (M : ℝ) := (one_div_pos.mpr hMreal).le
    linarith
  have htPow : 1 ≤ localRatioMeshStep M ^ k := one_le_pow₀ ht
  have htNine : localRatioMeshStep M ^ k ≤ 9 :=
    localRatioMeshStep_pow_le_nine_of_lt_two_mul hM hk
  unfold annularMultiplicativeCenter
  constructor
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left htPow hb
  · calc
      annularDyadicStart F j * localRatioMeshStep M ^ k ≤
          annularDyadicStart F j * 9 :=
        mul_le_mul_of_nonneg_left htNine hb
      _ = 9 * annularDyadicStart F j := by ring

/-! ## Exact selected real-cell data and fixed-scale bands -/

/-- The selected shortest-vector label on active real cells, extended by zero
outside the active family. -/
noncomputable def main3LargeAnalytic_selectedRealCellShortestVector
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : shiftedSquareA h v < 0)
    (cell : RealSquareMapCellPairIndex) : Fin 2 → ℤ :=
  if hcell : cell ∈
      main3LargeAnalytic_nonemptyRealCellIndices htheta hY hi key then
    (main3LargeAnalytic_realCellCoverSelection
      htheta hY hi key ha ⟨cell, hcell⟩).shortestVector
  else 0

/-- The selected real-cell first minimum, extended by one outside the active
family. -/
noncomputable def main3LargeAnalytic_selectedRealCellMu
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : shiftedSquareA h v < 0)
    (cell : RealSquareMapCellPairIndex) : ℝ :=
  if hcell : cell ∈
      main3LargeAnalytic_nonemptyRealCellIndices htheta hY hi key then
    (main3LargeAnalytic_realCellCoverSelection
      htheta hY hi key ha ⟨cell, hcell⟩).mu
  else 1

/-- Active real cells at one fixed annular dyadic scale in a reciprocal-
minimum tail. -/
noncomputable def main3LargeAnalytic_realCellReciprocalMinimumBandAtScale
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : shiftedSquareA h v < 0) (j : ℕ) (S : ℝ) :
    Finset RealSquareMapCellPairIndex :=
  (main3LargeAnalytic_nonemptyRealCellIndices htheta hY hi key).filter
    fun cell ↦ cell.1.2.1 = j ∧
      S ≤ 1 / main3LargeAnalytic_selectedRealCellMu
        htheta hY hi key ha cell

@[simp]
theorem mem_main3LargeAnalytic_realCellReciprocalMinimumBandAtScale
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : shiftedSquareA h v < 0) (j : ℕ) (S : ℝ)
    (cell : RealSquareMapCellPairIndex) :
    cell ∈ main3LargeAnalytic_realCellReciprocalMinimumBandAtScale
        htheta hY hi key ha j S ↔
      cell ∈ main3LargeAnalytic_nonemptyRealCellIndices htheta hY hi key ∧
      cell.1.2.1 = j ∧
      S ≤ 1 / main3LargeAnalytic_selectedRealCellMu
        htheta hY hi key ha cell := by
  classical
  simp [main3LargeAnalytic_realCellReciprocalMinimumBandAtScale]

set_option maxHeartbeats 1500000 in
/-- Fixed-scale real reciprocal-minimum bands satisfy the weighted two-place
lattice-incidence bound. -/
theorem card_main3LargeAnalytic_realCellReciprocalMinimumBandAtScale_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : shiftedSquareA h v < 0)
    (j : ℕ) (S : ℝ) (hS : 0 < S)
    (hH : 1 ≤ 72 * Real.sqrt
      (main3LargeAnalyticFixedKeyTargetScaleUpper Y key) / S) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    let Delta := Real.sqrt
      |(NumberField.discr
        (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
    let Hrad := 72 * Real.sqrt E / S
    ((main3LargeAnalytic_realCellReciprocalMinimumBandAtScale
      htheta hY hi key ha j S).card : ℝ) ≤
      540000 * Hrad * (2 + Real.log Hrad) +
        9720000 * Hrad ^ 2 / Delta := by
  dsimp only
  classical
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let a := shiftedSquareA h v
  let F := shiftedSquareFixedExplicitIntegralBasisData
    a (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
  let f : RealSquareMapCellPairIndex → Fin 2 → ℤ :=
    main3LargeAnalytic_selectedRealCellShortestVector
      htheta hY hi key ha
  let J := main3LargeAnalytic_realCellReciprocalMinimumBandAtScale
    htheta hY hi key ha j S
  let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let Delta := Real.sqrt
    |(NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
  let b := annularDyadicStart (shiftedSquareEmbeddingScaleLoss a) j
  let Hrad := 72 * Real.sqrt E / S
  let r : (Fin 2 → ℤ) → ℝ := fun y ↦
    main3RealScaledTwoPlaceTargetSupNorm b
      (sigma F.omega) (sigma (star F.omega)) y
  have hM : 0 < main3UnbalancedM theta Y :=
    lt_of_lt_of_le (by omega) (six_le_main3UnbalancedM htheta hY)
  have hFscale : 1 ≤ shiftedSquareEmbeddingScaleLoss a := by
    have haOne : (1 : ℝ) ≤ |(a : ℝ)| := by
      exact_mod_cast Int.one_le_abs (by dsimp only [a]; exact ne_of_lt ha)
    unfold shiftedSquareEmbeddingScaleLoss
    nlinarith
  have hb : 0 < b := by
    dsimp only [b]
    exact annularDyadicStart_pos hFscale j
  have hdiscZ : NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) ≠ 0 :=
    NumberField.discr_ne_zero _
  have hdiscR : (NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ) ≠ 0 := by
    exact_mod_cast hdiscZ
  have hDelta : 0 < Delta := by
    dsimp only [Delta]
    exact Real.sqrt_pos.2 (abs_pos.mpr hdiscR)
  have hJI : J ⊆
      main3LargeAnalytic_nonemptyRealCellIndices htheta hY hi key := by
    intro cell hcell
    exact (mem_main3LargeAnalytic_realCellReciprocalMinimumBandAtScale
      htheta hY hi key ha j S cell).mp hcell |>.1
  have hnonzero : ∀ cell ∈ J, f cell ≠ 0 := by
    intro cell hcell
    have hcellI := hJI hcell
    let c : ↑(main3LargeAnalytic_nonemptyRealCellIndices
      htheta hY hi key) := ⟨cell, hcellI⟩
    let Q := main3LargeAnalytic_realCellCoverSelection
      htheta hY hi key ha c
    simpa only [f, main3LargeAnalytic_selectedRealCellShortestVector,
      dif_pos hcellI, c, Q] using Q.shortestVector_spec.1
  have hrLower : ∀ y ∈ J.image f, 1 ≤ r y := by
    intro y hy
    obtain ⟨cell, hcell, hfcell⟩ := Finset.mem_image.mp hy
    rw [← hfcell]
    simpa only [r, a, F, sigma] using
      one_le_main3RealScaledTwoPlaceTargetSupNorm_fixedBasis_positiveRealPlaces
        ha F b hb.ne' (f cell) (hnonzero cell hcell)
  have hrUpper : ∀ y ∈ J.image f, r y ≤ Hrad := by
    intro y hy
    obtain ⟨cell, hcell, hfcell⟩ := Finset.mem_image.mp hy
    have hcellBand :=
      (mem_main3LargeAnalytic_realCellReciprocalMinimumBandAtScale
        htheta hY hi key ha j S cell).mp hcell
    have hcellI := hcellBand.1
    have hcellScale := hcellBand.2.1
    have hcellAmbient :=
      (mem_main3LargeAnalytic_nonemptyRealCellIndices
        htheta hY hi key cell).mp hcellI |>.1
    have hk : cell.1.2.2 < 2 * main3UnbalancedM theta Y :=
      (mem_annularMultiplicativeCellIndices.mp
        (Finset.mem_product.mp hcellAmbient).1).2.2
    let c : ↑(main3LargeAnalytic_nonemptyRealCellIndices
      htheta hY hi key) := ⟨cell, hcellI⟩
    let Q := main3LargeAnalytic_realCellCoverSelection
      htheta hY hi key ha c
    let signedCentre :=
      main3LargeAnalyticRealCellSignedCentre theta Y h v cell
    let s := annularMultiplicativeCenter
      (shiftedSquareEmbeddingScaleLoss a)
      (main3UnbalancedM theta Y) j cell.1.2.2
    have hbandQ : S ≤ 1 / Q.mu := by
      simpa only [main3LargeAnalytic_selectedRealCellMu,
        dif_pos hcellI, c, Q] using hcellBand.2.2
    have hselected := Q.shortestVector_twoPlace_reciprocalBand_le hS hbandQ
    have hwindow := annularMultiplicativeCenter_between_start_and_nine
      (j := cell.1.2.1) (k := cell.1.2.2) hFscale hM hk
    have hs : 0 < s := by
      dsimp only [s, annularMultiplicativeCenter]
      exact mul_pos hb
        (pow_pos (by unfold localRatioMeshStep; positivity) _)
    have hbs : b ≤ s := by
      simpa only [b, s, hcellScale] using hwindow.1
    have hsb : s ≤ 9 * b := by
      simpa only [b, s, hcellScale] using hwindow.2
    have habsCentre : |signedCentre| = s := by
      have habs :=
        abs_main3LargeAnalyticRealCellSignedCentre_eq_center cell hcellAmbient
      simpa only [signedCentre, s, a, hcellScale] using habs
    have hscaleCompare :=
      main3RealScaledTwoPlaceTargetSupNorm_leftEndpoint_le_nine_mul
        b s (sigma F.omega) (sigma (star F.omega)) Q.shortestVector
          hb hs hbs hsb
    have hnormEq :
        main3RealScaledTwoPlaceTargetSupNorm s
            (sigma F.omega) (sigma (star F.omega)) Q.shortestVector =
          main3RealScaledTwoPlaceTargetSupNorm signedCentre
            (sigma F.omega) (sigma (star F.omega)) Q.shortestVector := by
      unfold main3RealScaledTwoPlaceTargetSupNorm
      rw [abs_of_pos hs, habsCentre]
    rw [hnormEq] at hscaleCompare
    rw [← hfcell]
    calc
      r (f cell) ≤ 9 * main3RealScaledTwoPlaceTargetSupNorm signedCentre
          (sigma F.omega) (sigma (star F.omega)) Q.shortestVector := by
        simpa only [r, f, main3LargeAnalytic_selectedRealCellShortestVector,
          dif_pos hcellI, c, Q, signedCentre, a, F, sigma] using hscaleCompare
      _ ≤ 9 * (8 * Real.sqrt E / S) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [signedCentre, a, F, sigma, E] using hselected)
          (by norm_num)
      _ = Hrad := by dsimp only [Hrad]; ring
  have hball : ∀ t : ℝ, 1 ≤ t → t ≤ Hrad →
      ((((J.image f).filter fun y ↦ r y ≤ t).card : ℕ) : ℝ) ≤
        24 * t + (144 / Delta) * t ^ 2 := by
    intro t ht _htH
    simpa only [r, Delta, a, F, sigma] using
      card_fixedBasisVectorImage_filter_scaledTwoPlace_norm_le_linear_add_area
        F ha J f hnonzero b t hb.ne' ht
  have hfiber : ∀ y ∈ J.image f,
      (((J.filter fun cell ↦ f cell = y).card : ℕ) : ℝ) ≤
        18 + 22500 * Hrad / r y := by
    intro y hy
    let C := J.filter fun cell ↦ f cell = y
    have hCI : C ⊆
        main3LargeAnalytic_nonemptyRealCellIndices htheta hY hi key := by
      intro cell hcell
      exact hJI (Finset.mem_filter.mp hcell).1
    let active : ↑C →
        ↑(main3LargeAnalytic_nonemptyRealCellIndices
          htheta hY hi key) := fun c ↦ ⟨c.1, hCI c.2⟩
    let Q : (c : ↑C) →
        Main3LargeAnalyticFixedKeyRealCellCoverSelection
          htheta hY hi key c.1 ha := fun c ↦
      main3LargeAnalytic_realCellCoverSelection
        htheta hY hi key ha (active c)
    have hCscale : ∀ cell ∈ C, cell.1.2.1 = j := by
      intro cell hcell
      have hcJ := (Finset.mem_filter.mp hcell).1
      exact (mem_main3LargeAnalytic_realCellReciprocalMinimumBandAtScale
        htheta hY hi key ha j S cell).mp hcJ |>.2.1
    have hcommon := card_main3RealCells_with_common_shortestVector_at_scale_le
      htheta hY hi key ha hS j y C hCI hCscale Q
        (fun c ↦ by
          have hcJ := (Finset.mem_filter.mp c.2).1
          have hcBand :=
            (mem_main3LargeAnalytic_realCellReciprocalMinimumBandAtScale
              htheta hY hi key ha j S c.1).mp hcJ
          simpa only [main3LargeAnalytic_selectedRealCellMu,
            dif_pos (hCI c.2), active, Q] using hcBand.2.2)
        (fun c ↦ by
          have hcy := (Finset.mem_filter.mp c.2).2
          simpa only [f, main3LargeAnalytic_selectedRealCellShortestVector,
            dif_pos (hCI c.2), active, Q] using hcy)
    calc
      (((J.filter fun cell ↦ f cell = y).card : ℕ) : ℝ) ≤
          18 + 1620000 * Real.sqrt E / (S * r y) := by
        simpa only [C, r, b, E, a, F, sigma] using hcommon
      _ = 18 + 22500 * Hrad / r y := by
        dsimp only [Hrad]
        ring
  have hincidence :=
    card_le_coeff_mul_linear_square_radialWeightedImage_of_fiber_bound
      J f r Hrad 24 (144 / Delta) 18 22500 hH
        (by norm_num) (by positivity) (by norm_num) (by norm_num)
        hrLower hrUpper hball hfiber
  calc
    (J.card : ℝ) ≤
        22500 * (24 * Hrad * (2 + Real.log Hrad) +
          3 * (144 / Delta) * Hrad ^ 2) := hincidence
    _ = 540000 * Hrad * (2 + Real.log Hrad) +
        9720000 * Hrad ^ 2 / Delta := by ring

/-- All active real cells in a reciprocal-minimum tail, before splitting by
annular dyadic scale. -/
noncomputable def main3LargeAnalytic_realCellReciprocalMinimumBand
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : shiftedSquareA h v < 0) (S : ℝ) :
    Finset RealSquareMapCellPairIndex :=
  (main3LargeAnalytic_nonemptyRealCellIndices htheta hY hi key).filter
    fun cell ↦ S ≤ 1 / main3LargeAnalytic_selectedRealCellMu
      htheta hY hi key ha cell

@[simp]
theorem mem_main3LargeAnalytic_realCellReciprocalMinimumBand
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : shiftedSquareA h v < 0) (S : ℝ)
    (cell : RealSquareMapCellPairIndex) :
    cell ∈ main3LargeAnalytic_realCellReciprocalMinimumBand
        htheta hY hi key ha S ↔
      cell ∈ main3LargeAnalytic_nonemptyRealCellIndices htheta hY hi key ∧
      S ≤ 1 / main3LargeAnalytic_selectedRealCellMu
        htheta hY hi key ha cell := by
  classical
  simp [main3LargeAnalytic_realCellReciprocalMinimumBand]

set_option maxHeartbeats 800000 in
/-- Summing the fixed-scale incidence estimate over the literal annular scale
range gives the global real reciprocal-minimum band count. -/
theorem card_main3LargeAnalytic_realCellReciprocalMinimumBand_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : shiftedSquareA h v < 0)
    (S : ℝ) (hS : 0 < S)
    (hH : 1 ≤ 72 * Real.sqrt
      (main3LargeAnalyticFixedKeyTargetScaleUpper Y key) / S) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let Fscale := shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v)
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    let Delta := Real.sqrt
      |(NumberField.discr
        (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
    let Hrad := 72 * Real.sqrt E / S
    ((main3LargeAnalytic_realCellReciprocalMinimumBand
      htheta hY hi key ha S).card : ℝ) ≤
      (annularDyadicScaleCount Fscale : ℝ) *
        (540000 * Hrad * (2 + Real.log Hrad) +
          9720000 * Hrad ^ 2 / Delta) := by
  dsimp only
  classical
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let I := main3LargeAnalytic_realCellReciprocalMinimumBand
    htheta hY hi key ha S
  let scales := Finset.range (annularDyadicScaleCount
    (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v)))
  let bands : ℕ → Finset RealSquareMapCellPairIndex := fun j ↦
    main3LargeAnalytic_realCellReciprocalMinimumBandAtScale
      htheta hY hi key ha j S
  let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let Delta := Real.sqrt
    |(NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
  let Hrad := 72 * Real.sqrt E / S
  let R := 540000 * Hrad * (2 + Real.log Hrad) +
    9720000 * Hrad ^ 2 / Delta
  have hcover : I ⊆ scales.biUnion bands := by
    intro cell hcell
    have hband :=
      (mem_main3LargeAnalytic_realCellReciprocalMinimumBand
        htheta hY hi key ha S cell).mp hcell
    have hambient :=
      (mem_main3LargeAnalytic_nonemptyRealCellIndices
        htheta hY hi key cell).mp hband.1 |>.1
    have hscale : cell.1.2.1 < annularDyadicScaleCount
        (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v)) :=
      (mem_annularMultiplicativeCellIndices.mp
        (Finset.mem_product.mp hambient).1).2.1
    apply Finset.mem_biUnion.mpr
    refine ⟨cell.1.2.1, Finset.mem_range.mpr hscale, ?_⟩
    exact (mem_main3LargeAnalytic_realCellReciprocalMinimumBandAtScale
      htheta hY hi key ha cell.1.2.1 S cell).mpr
        ⟨hband.1, rfl, hband.2⟩
  have hcardNat : I.card ≤ ∑ j ∈ scales, (bands j).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hcardReal : (I.card : ℝ) ≤
      ∑ j ∈ scales, ((bands j).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((main3LargeAnalytic_realCellReciprocalMinimumBand
        htheta hY hi key ha S).card : ℝ) = (I.card : ℝ) := by rfl
    _ ≤ ∑ j ∈ scales, ((bands j).card : ℝ) := hcardReal
    _ ≤ ∑ _j ∈ scales, R := by
      apply Finset.sum_le_sum
      intro j hj
      have hcount :=
        card_main3LargeAnalytic_realCellReciprocalMinimumBandAtScale_le
          htheta hY hi key ha j S hS hH
      simpa only [bands, R, E, Delta, Hrad] using hcount
    _ = (annularDyadicScaleCount
          (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v)) : ℝ) * R := by
      simp only [scales, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
    _ = _ := by rfl

set_option maxHeartbeats 1200000 in
/-- Weak reciprocal-linear plus reciprocal-square tail bound for the full
active real-cell family.  The annular scale count appears once, from summing
the fixed-scale incidence estimates. -/
theorem card_main3LargeAnalytic_realCellReciprocalMinimumBand_le_weakTail
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : shiftedSquareA h v < 0)
    (hE : 0 < main3LargeAnalyticFixedKeyTargetScaleUpper Y key)
    (hH₀ : 1 ≤ 144 * Real.sqrt
      (main3LargeAnalyticFixedKeyTargetScaleUpper Y key))
    (T : ℝ) (hT : (1 / 2 : ℝ) ≤ T) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let Fscale := shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v)
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    let Delta := Real.sqrt
      |(NumberField.discr
        (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
    let Lscale := (annularDyadicScaleCount Fscale : ℝ)
    let H₀ := 144 * Real.sqrt E
    let A := 38880000 * Lscale * Real.sqrt E * (2 + Real.log H₀)
    let B := 50388480000 * Lscale * E / Delta
    ((main3LargeAnalytic_realCellReciprocalMinimumBand
      htheta hY hi key ha T).card : ℝ) ≤ A / T + B / T ^ 2 := by
  dsimp only
  classical
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let a := shiftedSquareA h v
  let F := shiftedSquareFixedExplicitIntegralBasisData
    a (main3LargeAnalytic_shift_squarefree hi)
  let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let Delta := Real.sqrt
    |(NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
  let Lscale := (annularDyadicScaleCount
    (shiftedSquareEmbeddingScaleLoss a) : ℝ)
  let H₀ := 144 * Real.sqrt E
  let Hrad := 72 * Real.sqrt E / T
  let Acoef := 38880000 * Lscale * Real.sqrt E * (2 + Real.log H₀)
  let Bcoef := 50388480000 * Lscale * E / Delta
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hdiscZ : NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) ≠ 0 :=
    NumberField.discr_ne_zero _
  have hdiscR : (NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ) ≠ 0 := by
    exact_mod_cast hdiscZ
  have hDelta : 0 < Delta := by
    dsimp only [Delta]
    exact Real.sqrt_pos.2 (abs_pos.mpr hdiscR)
  have hHradUpper : Hrad ≤ H₀ := by
    dsimp only [Hrad, H₀]
    apply (div_le_iff₀ hTpos).2
    have hsqrt := Real.sqrt_nonneg E
    nlinarith
  have hH₀pos : 0 < H₀ :=
    zero_lt_one.trans_le (by simpa only [H₀, E] using hH₀)
  have hlogH₀ : 0 ≤ Real.log H₀ := Real.log_nonneg
    (by simpa only [H₀, E] using hH₀)
  have hLscale : 0 ≤ Lscale := by dsimp only [Lscale]; positivity
  have hAcoef : 0 ≤ Acoef := by dsimp only [Acoef]; positivity
  have hBcoef : 0 ≤ Bcoef := by dsimp only [Bcoef]; positivity
  by_cases hHrad : 1 ≤ Hrad
  · have hcount := card_main3LargeAnalytic_realCellReciprocalMinimumBand_le
      htheta hY hi key ha T hTpos (by simpa only [Hrad, E] using hHrad)
    have hlog : Real.log Hrad ≤ Real.log H₀ :=
      Real.log_le_log (zero_lt_one.trans_le hHrad) hHradUpper
    calc
      ((main3LargeAnalytic_realCellReciprocalMinimumBand
          htheta hY hi key ha T).card : ℝ) ≤
          Lscale * (540000 * Hrad * (2 + Real.log Hrad) +
            9720000 * Hrad ^ 2 / Delta) := by
        simpa only [a, E, Delta, Lscale, Hrad] using hcount
      _ ≤ Lscale * (540000 * Hrad * (2 + Real.log H₀) +
            9720000 * Hrad ^ 2 / Delta) := by
        gcongr
      _ = Acoef / T + Bcoef / T ^ 2 := by
        dsimp only [Hrad, Acoef, Bcoef]
        rw [div_pow, show (72 * Real.sqrt E) ^ 2 = 5184 * E by
          rw [mul_pow, Real.sq_sqrt (by simpa only [E] using hE.le)]
          norm_num]
        field_simp [hTpos.ne', hDelta.ne']
        ring
  · have hempty : main3LargeAnalytic_realCellReciprocalMinimumBand
        htheta hY hi key ha T = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hnonempty
      obtain ⟨cell, hcell⟩ := hnonempty
      have hcellBand :=
        (mem_main3LargeAnalytic_realCellReciprocalMinimumBand
          htheta hY hi key ha T cell).mp hcell
      have hcellI := hcellBand.1
      have hcellAmbient :=
        (mem_main3LargeAnalytic_nonemptyRealCellIndices
          htheta hY hi key cell).mp hcellI |>.1
      let c : ↑(main3LargeAnalytic_nonemptyRealCellIndices
        htheta hY hi key) := ⟨cell, hcellI⟩
      let Q := main3LargeAnalytic_realCellCoverSelection
        htheta hY hi key ha c
      let signedCentre :=
        main3LargeAnalyticRealCellSignedCentre theta Y h v cell
      have hbandQ : T ≤ 1 / Q.mu := by
        simpa only [main3LargeAnalytic_selectedRealCellMu,
          dif_pos hcellI, c, Q] using hcellBand.2
      have habsCentre :=
        abs_main3LargeAnalyticRealCellSignedCentre_eq_center cell hcellAmbient
      have hcentrePos : 0 < annularMultiplicativeCenter
          (shiftedSquareEmbeddingScaleLoss a)
          (main3UnbalancedM theta Y) cell.1.2.1 cell.1.2.2 := by
        have hFscale : 1 ≤ shiftedSquareEmbeddingScaleLoss a := by
          have haOne : (1 : ℝ) ≤ |(a : ℝ)| := by
            exact_mod_cast Int.one_le_abs
              (by dsimp only [a]; exact ne_of_lt ha)
          unfold shiftedSquareEmbeddingScaleLoss
          nlinarith
        dsimp only [annularMultiplicativeCenter]
        exact mul_pos (annularDyadicStart_pos hFscale cell.1.2.1)
          (pow_pos (by unfold localRatioMeshStep; positivity) _)
      have hsignedCentre : signedCentre ≠ 0 := by
        apply abs_ne_zero.mp
        simpa only [signedCentre, a] using
          (habsCentre.trans_ne hcentrePos.ne')
      have hlower :=
        one_le_main3RealScaledTwoPlaceTargetSupNorm_fixedBasis_positiveRealPlaces
          ha F signedCentre hsignedCentre Q.shortestVector
            Q.shortestVector_spec.1
      have hupper := Q.shortestVector_twoPlace_reciprocalBand_le hTpos hbandQ
      have hone : (1 : ℝ) ≤ Hrad := by
        calc
          (1 : ℝ) ≤ main3RealScaledTwoPlaceTargetSupNorm signedCentre
              (shiftedSquarePositiveRealPlaceEmbedding a ha F.omega)
              (shiftedSquarePositiveRealPlaceEmbedding a ha (star F.omega))
              Q.shortestVector := by
            simpa only [a, F, signedCentre] using hlower
          _ ≤ 8 * Real.sqrt E / T := by
            simpa only [a, F, signedCentre, E] using hupper
          _ ≤ Hrad := by
            have hbase : 0 ≤ Real.sqrt E / T := by positivity
            calc
              8 * Real.sqrt E / T = 8 * (Real.sqrt E / T) := by ring
              _ ≤ 72 * (Real.sqrt E / T) := by nlinarith
              _ = Hrad := by dsimp only [Hrad]; ring
      exact hHrad hone
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact add_nonneg (div_nonneg hAcoef hTpos.le)
      (div_nonneg hBcoef (sq_nonneg T))

set_option maxHeartbeats 1500000 in
/-- Summing the reciprocal first minima over all active real cells gives the
exact two-log tail-completion budget, with one annular-scale-count factor. -/
theorem sum_main3LargeAnalytic_nonemptyRealCell_reciprocalMinimum_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : shiftedSquareA h v < 0)
    (hnonempty :
      (main3LargeAnalytic_nonemptyRealCellIndices
        htheta hY hi key).Nonempty) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let Fscale := shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v)
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    let Delta := Real.sqrt
      |(NumberField.discr
        (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
    let K := (2 * E / (main3UnbalancedM theta Y : ℝ)) / Delta
    let S₀ := max (1 / 2 : ℝ) (Real.sqrt K / 2)
    let L := K / 2 + 5
    let H₀ := 144 * Real.sqrt E
    let Lscale := (annularDyadicScaleCount Fscale : ℝ)
    let A := 38880000 * Lscale * Real.sqrt E * (2 + Real.log H₀)
    let B := 50388480000 * Lscale * E / Delta
    (∑ cell ∈ main3LargeAnalytic_nonemptyRealCellIndices
        htheta hY hi key,
      1 / main3LargeAnalytic_selectedRealCellMu
        htheta hY hi key ha cell) ≤
      A * (1 + Real.log (L / S₀)) + 2 * B / S₀ := by
  dsimp only
  classical
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let a := shiftedSquareA h v
  let F := shiftedSquareFixedExplicitIntegralBasisData
    a (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
  let I := main3LargeAnalytic_nonemptyRealCellIndices htheta hY hi key
  let r : RealSquareMapCellPairIndex → ℝ := fun cell =>
    1 / main3LargeAnalytic_selectedRealCellMu
      htheta hY hi key ha cell
  let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let Delta := Real.sqrt
    |(NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
  let K := (2 * E / (main3UnbalancedM theta Y : ℝ)) / Delta
  let S₀ := max (1 / 2 : ℝ) (Real.sqrt K / 2)
  let L := K / 2 + 5
  let H₀ := 144 * Real.sqrt E
  let Lscale := (annularDyadicScaleCount
    (shiftedSquareEmbeddingScaleLoss a) : ℝ)
  let Acoef := 38880000 * Lscale * Real.sqrt E * (2 + Real.log H₀)
  let Bcoef := 50388480000 * Lscale * E / Delta
  obtain ⟨cell₀, hcell₀⟩ := hnonempty
  let c₀ : ↑I := ⟨cell₀, by simpa only [I] using hcell₀⟩
  let Q₀ := main3LargeAnalytic_realCellCoverSelection
    htheta hY hi key ha c₀
  have hE : 0 < E := by
    have htwoE : 0 < 2 * E := Q₀.cert.R_pos
    nlinarith
  have hdiscZ : NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) ≠ 0 :=
    NumberField.discr_ne_zero _
  have hdiscR : (NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ) ≠ 0 := by
    exact_mod_cast hdiscZ
  have hDelta : 0 < Delta := by
    dsimp only [Delta]
    exact Real.sqrt_pos.2 (abs_pos.mpr hdiscR)
  have hend₀ := Q₀.cover_spec.reciprocal_firstSlopeSupNorm_mem_interval
  have hhalf₀ : (1 / 2 : ℝ) ≤ 1 / Q₀.mu := by
    simpa only [Main3LargeAnalyticRealCellCoverSelectionData.mu,
      Main3LargeAnalyticRealCellCoverSelectionData.U,
      Main3LargeAnalyticRealCellCoverSelectionData.V,
      Main3LargeAnalyticRealCellCoverSelectionData.M₀,
      Main3LargeAnalyticRealCellCoverSelectionData.rho,
      Main3LargeAnalyticRealCellCoverSelectionData.z,
      Main3LargeAnalyticRealCellCoverSelectionData.beta] using hend₀.1
  have hsqrt₀ : Real.sqrt K / 2 ≤ 1 / Q₀.mu := by
    simpa only [K, E, Delta] using Q₀.sqrt_K_div_two_le_reciprocal_mu
  have hS₀r₀ : S₀ ≤ 1 / Q₀.mu := max_le hhalf₀ hsqrt₀
  have hrL₀ : 1 / Q₀.mu ≤ L := by
    have hupper : 1 / Q₀.mu ≤ Q₀.U + Q₀.V := by
      simpa only [Main3LargeAnalyticRealCellCoverSelectionData.mu,
        Main3LargeAnalyticRealCellCoverSelectionData.U,
        Main3LargeAnalyticRealCellCoverSelectionData.V,
        Main3LargeAnalyticRealCellCoverSelectionData.M₀,
        Main3LargeAnalyticRealCellCoverSelectionData.rho,
        Main3LargeAnalyticRealCellCoverSelectionData.z,
        Main3LargeAnalyticRealCellCoverSelectionData.beta] using hend₀.2
    calc
      1 / Q₀.mu ≤ Q₀.U + Q₀.V := hupper
      _ = L := by
        dsimp only [Main3LargeAnalyticRealCellCoverSelectionData.U,
          Main3LargeAnalyticRealCellCoverSelectionData.V, L, K, E, Delta]
        norm_num
  have hcellAmbient₀ :=
    (mem_main3LargeAnalytic_nonemptyRealCellIndices
      htheta hY hi key cell₀).mp hcell₀ |>.1
  let signedCentre₀ :=
    main3LargeAnalyticRealCellSignedCentre theta Y h v cell₀
  have hFscale : 1 ≤ shiftedSquareEmbeddingScaleLoss a := by
    have haOne : (1 : ℝ) ≤ |(a : ℝ)| := by
      exact_mod_cast Int.one_le_abs (by dsimp only [a]; exact ne_of_lt ha)
    unfold shiftedSquareEmbeddingScaleLoss
    nlinarith
  have hcentrePos₀ : 0 < annularMultiplicativeCenter
      (shiftedSquareEmbeddingScaleLoss a)
      (main3UnbalancedM theta Y) cell₀.1.2.1 cell₀.1.2.2 := by
    dsimp only [annularMultiplicativeCenter]
    exact mul_pos (annularDyadicStart_pos hFscale cell₀.1.2.1)
      (pow_pos (by unfold localRatioMeshStep; positivity) _)
  have habsCentre₀ : |signedCentre₀| =
      annularMultiplicativeCenter
        (shiftedSquareEmbeddingScaleLoss a)
        (main3UnbalancedM theta Y) cell₀.1.2.1 cell₀.1.2.2 := by
    simpa only [signedCentre₀, a] using
      abs_main3LargeAnalyticRealCellSignedCentre_eq_center
        cell₀ hcellAmbient₀
  have hsignedCentre₀ : signedCentre₀ ≠ 0 := by
    apply abs_ne_zero.mp
    exact habsCentre₀.trans_ne hcentrePos₀.ne'
  have hlower₀ :=
    one_le_main3RealScaledTwoPlaceTargetSupNorm_fixedBasis_positiveRealPlaces
      ha F signedCentre₀ hsignedCentre₀ Q₀.shortestVector
        Q₀.shortestVector_spec.1
  have hupper₀ := Q₀.shortestVector_twoPlace_reciprocalBand_le
    (by norm_num : (0 : ℝ) < 1 / 2) hhalf₀
  have hH₀ : 1 ≤ H₀ := by
    calc
      (1 : ℝ) ≤ main3RealScaledTwoPlaceTargetSupNorm signedCentre₀
          (sigma F.omega) (sigma (star F.omega)) Q₀.shortestVector := by
        simpa only [a, F, sigma, signedCentre₀] using hlower₀
      _ ≤ 8 * Real.sqrt E / (1 / 2 : ℝ) := by
        simpa only [a, F, sigma, signedCentre₀, E] using hupper₀
      _ ≤ H₀ := by
        dsimp only [H₀]
        have hsqrt := Real.sqrt_nonneg E
        nlinarith
  have hS₀pos : 0 < S₀ :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hSL : S₀ ≤ L := hS₀r₀.trans hrL₀
  have hAcoef : 0 ≤ Acoef := by
    have hlog : 0 ≤ Real.log H₀ := Real.log_nonneg hH₀
    dsimp only [Acoef, Lscale]
    positivity
  have hBcoef : 0 ≤ Bcoef := by
    dsimp only [Bcoef, Lscale]
    positivity
  have hSr : ∀ cell ∈ I, S₀ ≤ r cell := by
    intro cell hcell
    have hcell' : cell ∈ main3LargeAnalytic_nonemptyRealCellIndices
        htheta hY hi key := by simpa only [I] using hcell
    let c : ↑I := ⟨cell, hcell⟩
    let Q := main3LargeAnalytic_realCellCoverSelection
      htheta hY hi key ha c
    have hend := Q.cover_spec.reciprocal_firstSlopeSupNorm_mem_interval
    have hlower : (1 / 2 : ℝ) ≤ 1 / Q.mu := by
      simpa only [Main3LargeAnalyticRealCellCoverSelectionData.mu,
        Main3LargeAnalyticRealCellCoverSelectionData.U,
        Main3LargeAnalyticRealCellCoverSelectionData.V,
        Main3LargeAnalyticRealCellCoverSelectionData.M₀,
        Main3LargeAnalyticRealCellCoverSelectionData.rho,
        Main3LargeAnalyticRealCellCoverSelectionData.z,
        Main3LargeAnalyticRealCellCoverSelectionData.beta] using hend.1
    have hsqrt : Real.sqrt K / 2 ≤ 1 / Q.mu := by
      simpa only [K, E, Delta] using Q.sqrt_K_div_two_le_reciprocal_mu
    have hcutoff : S₀ ≤ 1 / Q.mu := max_le hlower hsqrt
    simpa only [r, main3LargeAnalytic_selectedRealCellMu,
      dif_pos hcell', c, Q] using hcutoff
  have hrL : ∀ cell ∈ I, r cell ≤ L := by
    intro cell hcell
    have hcell' : cell ∈ main3LargeAnalytic_nonemptyRealCellIndices
        htheta hY hi key := by simpa only [I] using hcell
    let c : ↑I := ⟨cell, hcell⟩
    let Q := main3LargeAnalytic_realCellCoverSelection
      htheta hY hi key ha c
    have hend := Q.cover_spec.reciprocal_firstSlopeSupNorm_mem_interval
    have hupper : 1 / Q.mu ≤ Q.U + Q.V := by
      simpa only [Main3LargeAnalyticRealCellCoverSelectionData.mu,
        Main3LargeAnalyticRealCellCoverSelectionData.U,
        Main3LargeAnalyticRealCellCoverSelectionData.V,
        Main3LargeAnalyticRealCellCoverSelectionData.M₀,
        Main3LargeAnalyticRealCellCoverSelectionData.rho,
        Main3LargeAnalyticRealCellCoverSelectionData.z,
        Main3LargeAnalyticRealCellCoverSelectionData.beta] using hend.2
    calc
      r cell = 1 / Q.mu := by
        simp only [r, main3LargeAnalytic_selectedRealCellMu,
          dif_pos hcell', c, Q]
      _ ≤ Q.U + Q.V := hupper
      _ = L := by
        dsimp only [Main3LargeAnalyticRealCellCoverSelectionData.U,
          Main3LargeAnalyticRealCellCoverSelectionData.V, L, K, E, Delta]
        norm_num
  have htail : ∀ T : ℝ, S₀ ≤ T →
      ((I.filter fun cell => T ≤ r cell).card : ℝ) ≤
        Acoef / T + Bcoef / T ^ 2 := by
    intro T hT
    have hhalfT : (1 / 2 : ℝ) ≤ T := (le_max_left _ _).trans hT
    have hband :=
      card_main3LargeAnalytic_realCellReciprocalMinimumBand_le_weakTail
        htheta hY hi key ha (by simpa only [E] using hE)
          (by simpa only [E, H₀] using hH₀) T hhalfT
    simpa only [I, r, Acoef, Bcoef, Lscale, E, Delta,
      main3LargeAnalytic_realCellReciprocalMinimumBand] using hband
  have hsum := sum_le_linear_square_tail_completion
    I r S₀ L Acoef Bcoef hS₀pos hSL hAcoef hBcoef hSr hrL htail
  calc
    (∑ cell ∈ main3LargeAnalytic_nonemptyRealCellIndices
        htheta hY hi key,
      1 / main3LargeAnalytic_selectedRealCellMu
        htheta hY hi key ha cell) = ∑ cell ∈ I, r cell := by rfl
    _ ≤ Acoef * (1 + Real.log (L / S₀)) +
        2 * Bcoef / S₀ := hsum

/-- Elementary square-root algebra for the real-place area contribution
after using the cutoff `sqrt(2E/(M*Delta))/2`. -/
theorem div_sqrt_two_scaled_ratio_le_sqrt_product
    {E M Delta : ℝ} (hE : 0 < E) (hM : 0 < M)
    (hDelta : 0 < Delta) :
    E / Delta / Real.sqrt (2 * E / (M * Delta)) ≤
      Real.sqrt (E * M / Delta) := by
  have hK : 0 < 2 * E / (M * Delta) := by positivity
  have hX : 0 ≤ E * M / Delta := by positivity
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [div_pow, div_pow, Real.sq_sqrt hK.le, Real.sq_sqrt hX]
  field_simp [hE.ne', hM.ne', hDelta.ne']
  nlinarith

set_option maxHeartbeats 1200000 in
/-- Coarse manuscript-shaped real reciprocal-minimum sum.  The annular
scale count multiplies both the radial logarithmic term and the lattice-area
term; the stronger Minkowski cutoff gives the square-root area scale. -/
theorem sum_main3LargeAnalytic_nonemptyRealCell_reciprocalMinimum_le_intrinsicShape
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : shiftedSquareA h v < 0)
    (hnonempty :
      (main3LargeAnalytic_nonemptyRealCellIndices
        htheta hY hi key).Nonempty) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let Fscale := shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v)
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    let Delta := Real.sqrt
      |(NumberField.discr
        (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
    let K := (2 * E / (main3UnbalancedM theta Y : ℝ)) / Delta
    let L := K / 2 + 5
    let Lscale := (annularDyadicScaleCount Fscale : ℝ)
    let H₀ := 144 * Real.sqrt E
    (∑ cell ∈ main3LargeAnalytic_nonemptyRealCellIndices
        htheta hY hi key,
      1 / main3LargeAnalytic_selectedRealCellMu
        htheta hY hi key ha cell) ≤
      38880000 * Lscale * Real.sqrt E * (2 + Real.log H₀) *
          (1 + Real.log (2 * L)) +
        201553920000 * Lscale * Real.sqrt
          (E * (main3UnbalancedM theta Y : ℝ) / Delta) := by
  dsimp only
  classical
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let I := main3LargeAnalytic_nonemptyRealCellIndices htheta hY hi key
  let Fscale := shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v)
  let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let Delta := Real.sqrt
    |(NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
  let Mmesh := (main3UnbalancedM theta Y : ℝ)
  let K := (2 * E / Mmesh) / Delta
  let S₀ := max (1 / 2 : ℝ) (Real.sqrt K / 2)
  let L := K / 2 + 5
  let Lscale := (annularDyadicScaleCount Fscale : ℝ)
  let H₀ := 144 * Real.sqrt E
  let Acoef := 38880000 * Lscale * Real.sqrt E * (2 + Real.log H₀)
  let Bcoef := 50388480000 * Lscale * E / Delta
  have hsum :=
    sum_main3LargeAnalytic_nonemptyRealCell_reciprocalMinimum_le
      htheta hY hi key ha hnonempty
  obtain ⟨cell₀, hcell₀⟩ := hnonempty
  let c₀ : ↑I := ⟨cell₀, by simpa only [I] using hcell₀⟩
  let Q₀ := main3LargeAnalytic_realCellCoverSelection
    htheta hY hi key ha c₀
  have hE : 0 < E := by
    have htwoE : 0 < 2 * E := Q₀.cert.R_pos
    nlinarith
  have hMmesh : 0 < Mmesh := by
    dsimp only [Mmesh]
    exact_mod_cast (lt_of_lt_of_le (by omega)
      (six_le_main3UnbalancedM htheta hY))
  have hdiscZ : NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) ≠ 0 :=
    NumberField.discr_ne_zero _
  have hdiscR : (NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ) ≠ 0 := by
    exact_mod_cast hdiscZ
  have hDelta : 0 < Delta := by
    dsimp only [Delta]
    exact Real.sqrt_pos.2 (abs_pos.mpr hdiscR)
  have hK : 0 < K := by dsimp only [K]; positivity
  have hS₀pos : 0 < S₀ :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hS₀half : (1 / 2 : ℝ) ≤ S₀ := le_max_left _ _
  have hS₀sqrt : Real.sqrt K / 2 ≤ S₀ := le_max_right _ _
  have hLpos : 0 < L := by dsimp only [L]; positivity
  have hratioPos : 0 < L / S₀ := div_pos hLpos hS₀pos
  have hratioUpper : L / S₀ ≤ 2 * L := by
    apply (div_le_iff₀ hS₀pos).2
    nlinarith
  have hlogUpper : Real.log (L / S₀) ≤ Real.log (2 * L) :=
    Real.log_le_log hratioPos hratioUpper
  have hLscale : 0 ≤ Lscale := by dsimp only [Lscale, Fscale]; positivity
  have hAcoef : 0 ≤ Acoef := by
    have hcellAmbient :=
      (mem_main3LargeAnalytic_nonemptyRealCellIndices
        htheta hY hi key cell₀).mp hcell₀ |>.1
    let a := shiftedSquareA h v
    let F := shiftedSquareFixedExplicitIntegralBasisData
      a (main3LargeAnalytic_shift_squarefree hi)
    let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
    let signedCentre :=
      main3LargeAnalyticRealCellSignedCentre theta Y h v cell₀
    have hFscale' : 1 ≤ shiftedSquareEmbeddingScaleLoss a := by
      have haOne : (1 : ℝ) ≤ |(a : ℝ)| := by
        exact_mod_cast Int.one_le_abs
          (by dsimp only [a]; exact ne_of_lt ha)
      unfold shiftedSquareEmbeddingScaleLoss
      nlinarith
    have hcentrePos : 0 < annularMultiplicativeCenter
        (shiftedSquareEmbeddingScaleLoss a)
        (main3UnbalancedM theta Y) cell₀.1.2.1 cell₀.1.2.2 := by
      dsimp only [annularMultiplicativeCenter]
      exact mul_pos
        (annularDyadicStart_pos hFscale' cell₀.1.2.1)
        (pow_pos (by unfold localRatioMeshStep; positivity) _)
    have habsCentre :=
      abs_main3LargeAnalyticRealCellSignedCentre_eq_center cell₀ hcellAmbient
    have hsignedCentre : signedCentre ≠ 0 := by
      apply abs_ne_zero.mp
      simpa only [signedCentre, a] using
        (habsCentre.trans_ne hcentrePos.ne')
    have hend := Q₀.cover_spec.reciprocal_firstSlopeSupNorm_mem_interval
    have hhalf : (1 / 2 : ℝ) ≤ 1 / Q₀.mu := by
      simpa only [Main3LargeAnalyticRealCellCoverSelectionData.mu,
        Main3LargeAnalyticRealCellCoverSelectionData.U,
        Main3LargeAnalyticRealCellCoverSelectionData.V,
        Main3LargeAnalyticRealCellCoverSelectionData.M₀,
        Main3LargeAnalyticRealCellCoverSelectionData.rho,
        Main3LargeAnalyticRealCellCoverSelectionData.z,
        Main3LargeAnalyticRealCellCoverSelectionData.beta] using hend.1
    have hradius := Q₀.shortestVector_twoPlace_reciprocalBand_le
      (by norm_num : (0 : ℝ) < 1 / 2) hhalf
    have hnorm :=
      one_le_main3RealScaledTwoPlaceTargetSupNorm_fixedBasis_positiveRealPlaces
        ha F signedCentre hsignedCentre Q₀.shortestVector
          Q₀.shortestVector_spec.1
    have hH₀ : 1 ≤ H₀ := by
      calc
        (1 : ℝ) ≤ main3RealScaledTwoPlaceTargetSupNorm signedCentre
            (sigma F.omega) (sigma (star F.omega)) Q₀.shortestVector := by
          simpa only [a, F, sigma, signedCentre] using hnorm
        _ ≤ 8 * Real.sqrt E / (1 / 2 : ℝ) := by
          simpa only [a, F, sigma, signedCentre, E] using hradius
        _ ≤ H₀ := by
          dsimp only [H₀]
          have hsqrt := Real.sqrt_nonneg E
          nlinarith
    have hlog : 0 ≤ Real.log H₀ := Real.log_nonneg hH₀
    dsimp only [Acoef]
    positivity
  have hlinear : Acoef * (1 + Real.log (L / S₀)) ≤
      Acoef * (1 + Real.log (2 * L)) := by
    gcongr
  have hinv : 1 / S₀ ≤ 2 / Real.sqrt K := by
    have hinv' := one_div_le_one_div_of_le
      (div_pos (Real.sqrt_pos.2 hK) (by norm_num)) hS₀sqrt
    simpa only [one_div_div] using hinv'
  have hBcoef : 0 ≤ Bcoef := by dsimp only [Bcoef]; positivity
  have harea : 2 * Bcoef / S₀ ≤
      201553920000 * Lscale * Real.sqrt (E * Mmesh / Delta) := by
    have hscaled := div_sqrt_two_scaled_ratio_le_sqrt_product
      hE hMmesh hDelta
    have hKform : K = 2 * E / (Mmesh * Delta) := by
      dsimp only [K]
      ring
    calc
      2 * Bcoef / S₀ = 2 * Bcoef * (1 / S₀) := by ring
      _ ≤ 2 * Bcoef * (2 / Real.sqrt K) := by gcongr
      _ = 201553920000 * Lscale * (E / Delta / Real.sqrt K) := by
        dsimp only [Bcoef]
        ring
      _ = 201553920000 * Lscale *
          (E / Delta / Real.sqrt (2 * E / (Mmesh * Delta))) := by
        rw [hKform]
      _ ≤ 201553920000 * Lscale * Real.sqrt (E * Mmesh / Delta) := by
        gcongr
  calc
    (∑ cell ∈ main3LargeAnalytic_nonemptyRealCellIndices
        htheta hY hi key,
      1 / main3LargeAnalytic_selectedRealCellMu
        htheta hY hi key ha cell) ≤
        Acoef * (1 + Real.log (L / S₀)) + 2 * Bcoef / S₀ := by
      simpa only [Fscale, E, Delta, Mmesh, K, S₀, L, Lscale, H₀,
        Acoef, Bcoef] using hsum
    _ ≤ Acoef * (1 + Real.log (2 * L)) +
        201553920000 * Lscale * Real.sqrt (E * Mmesh / Delta) :=
      add_le_add hlinear harea

end

end PellPaper
