import Pell.Main3LargeAnalyticRealCellNormalizedTargetBounds
import Pell.Main3LargeAnalyticFixedKeyCellTargetCompletionEntryBoundCover
import Pell.PrimitiveWedgeCompletionSlopeHeight
import Pell.Main3FixedBasisEmbeddingStandardVectorBound
import Pell.Main3LargeAnalyticTargetImageRadiusLogBound
import Mathlib.Tactic

/-!
# Real-cell completion and product-basis logarithmic height

For one nonempty real fixed-key cell, the completion cover supplies the same
certificate and matrices `G,H` used by the reduced target cover.  The
normalized target lower bound controls the signed-centre Hermitian functional
on the two standard vectors.  The bounded completion then controls its second
column and hence the unrestricted signed slope centre.

The sign-free expanded reduced-matrix estimate gives the concrete product
height

`L ≤ 2^27 * Y * |a|^3 * T₀^3`.

The theta-free radius logarithm subsequently yields exactly the two logarithmic
hypotheses consumed by the uniform intrinsic-eliminant sieve budget.  No sieve
estimate, character-sum input, or Weil interface is used here.
-/

namespace PellPaper

open scoped MatrixGroups

noncomputable section

local instance main3LargeAnalyticRealCellCompletionProductHeightLogBudget_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

private theorem norm_main3IntegralTargetLinearForm_le_four_mul_sqrt_abs_mul
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha0 : a ≠ 0) (omega : ℂ) (T : ℝ) (hT : 0 ≤ T)
    (homega : ‖omega‖ ≤ 2 * Real.sqrt |(a : ℝ)|)
    (y : Fin 2 → ℤ) (hy : ∀ i, |((y i : ℤ) : ℝ)| ≤ T) :
    ‖main3IntegralTargetLinearForm omega y‖ ≤
      4 * Real.sqrt |(a : ℝ)| * T := by
  have hsqrtOne : 1 ≤ Real.sqrt |(a : ℝ)| := by
    exact Real.one_le_sqrt.mpr (by exact_mod_cast Int.one_le_abs ha0)
  have hsqrt0 : 0 ≤ Real.sqrt |(a : ℝ)| := Real.sqrt_nonneg _
  calc
    ‖main3IntegralTargetLinearForm omega y‖ ≤
        ‖(y 0 : ℂ)‖ + ‖omega * (y 1 : ℂ)‖ := by
      exact norm_add_le _ _
    _ = |((y 0 : ℤ) : ℝ)| + ‖omega‖ * |((y 1 : ℤ) : ℝ)| := by
      rw [norm_mul, Complex.norm_intCast, Complex.norm_intCast]
    _ ≤ T + (2 * Real.sqrt |(a : ℝ)|) * T := by
      exact add_le_add (hy 0)
        (mul_le_mul homega (hy 1) (by positivity) (by positivity))
    _ ≤ 4 * Real.sqrt |(a : ℝ)| * T := by
      have hfactor : 0 ≤ 2 * Real.sqrt |(a : ℝ)| - 1 := by linarith
      nlinarith [mul_nonneg hT hfactor]

private theorem main3LargeAnalytic_realCellHermitian_standardBasis_bound
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) (cell : RealSquareMapCellPairIndex)
    (ha : shiftedSquareA h v < 0) {y : Fin 2 → ℤ}
    (hy : y ∈ main3LargeAnalyticFixedKeyCellTargetVectorImage
      htheta hY hi key (Sum.inl cell))
    (ell : (Fin 2 → ℤ) →+ ℝ) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let a := shiftedSquareA h v
    let F := shiftedSquareFixedExplicitIntegralBasisData
      a (main3LargeAnalytic_shift_squarefree hi)
    let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
    let c := main3LargeAnalyticRealCellSignedCentre theta Y h v cell
    let T₀ := main3LargeAnalyticFixedKeyTargetCoordinateRadius a Y key
    let Ashift := |(a : ℝ)|
    ell = main3AnchorHermitianRadialAddHom (c ^ 2) (sigma F.omega) y →
      ∀ i, |ell (Pi.single i (1 : ℤ))| ≤ 32 * Ashift * T₀ := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let a := shiftedSquareA h v
  let F := shiftedSquareFixedExplicitIntegralBasisData
    a (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
  let c := main3LargeAnalyticRealCellSignedCentre theta Y h v cell
  let T₀ := main3LargeAnalyticFixedKeyTargetCoordinateRadius a Y key
  let Ashift := |(a : ℝ)|
  intro hell
  have ha0 : a ≠ 0 := by dsimp only [a]; exact ne_of_lt ha
  have hT₀one : 1 ≤ T₀ := by
    dsimp only [T₀, a]
    exact one_le_main3LargeAnalyticFixedKeyTargetCoordinateRadius_of_targetImage_nonempty
      htheta hY hi key (Sum.inl cell) ⟨y, hy⟩
  have hT₀nonneg : 0 ≤ T₀ := zero_le_one.trans hT₀one
  have hyCoordinates : ∀ i, |((y i : ℤ) : ℝ)| ≤ T₀ := by
    intro i
    simpa only [T₀, a] using
      main3LargeAnalyticFixedKeyCellTargetVectorImage_abs_coordinate_le
        htheta hY hi key (Sum.inl cell) hy i
  obtain ⟨anchorPoint, hanchorPoint, hanchorEq⟩ :=
    (mem_main3LargeAnalyticFixedKeyCellTargetVectorImage_iff
      htheta hY hi key (Sum.inl cell) y).mp hy
  let gamma := main3IntegralTargetLinearForm (sigma F.omega) y
  let gammaBar := main3IntegralTargetLinearForm (sigma (star F.omega)) y
  let targetNormalized :=
    main3LargeAnalyticRealCellNormalizedTarget hi ha cell anchorPoint
  have htargetBounds :=
    main3LargeAnalytic_realCellCoordinatePointImage_normalizedTarget_bounds
      htheta hY hi key cell ha hanchorPoint
  have htargetLower : (1 / 2 : ℝ) ≤ targetNormalized := by
    simpa only [targetNormalized] using htargetBounds.1
  have htargetPos : 0 < targetNormalized := by linarith
  have hgeometry :=
    main3LargeAnalytic_realCellCoordinatePointImage_normalized_geometry
      htheta hY hi key cell ha hanchorPoint
  dsimp only at hgeometry
  have hc : c ≠ 0 := by simpa only [c] using hgeometry.1
  have hgamma : gamma ≠ 0 := by
    have hden :=
      (main3LargeAnalytic_realCellCoordinatePointImage_embeddingRatio_geometry
        htheta hY hi key cell ha hanchorPoint).1.2.1
    dsimp only [gamma]
    rw [← hanchorEq]
    simpa only [main3IntegralTargetLinearForm,
      shiftedSquareCoordinatePointTargetVector, Matrix.cons_val_zero,
      Matrix.cons_val_one, F, sigma, a] using hden
  have hratio : gammaBar / gamma =
      ((c ^ 2 * targetNormalized : ℝ) : ℂ) := by
    have htargetEq := hgeometry.2.2.2.2.2
    dsimp only [gamma, gammaBar]
    rw [← hanchorEq]
    simpa only [targetNormalized, main3EmbeddingTargetRatio,
      main3LargeAnalyticRealCellTargetRatio, main3IntegralTargetLinearForm,
      shiftedSquareCoordinatePointTargetVector, Matrix.cons_val_zero,
      Matrix.cons_val_one, a, F, sigma, c] using htargetEq
  have hratioNorm := congrArg norm hratio
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (sq_pos_of_ne_zero hc) htargetPos)] at hratioNorm
  have hgammaNorm : ‖gamma‖ ≠ 0 := norm_ne_zero_iff.mpr hgamma
  have hgammaBarMul :
      ‖gammaBar‖ = c ^ 2 * targetNormalized * ‖gamma‖ := by
    apply (div_eq_iff hgammaNorm).mp
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hratioNorm
  have hweightedGamma : c ^ 2 * ‖gamma‖ ≤ 2 * ‖gammaBar‖ := by
    calc
      c ^ 2 * ‖gamma‖ =
          2 * ((1 / 2 : ℝ) * (c ^ 2 * ‖gamma‖)) := by ring
      _ ≤ 2 * (targetNormalized * (c ^ 2 * ‖gamma‖)) := by gcongr
      _ = 2 * ‖gammaBar‖ := by rw [hgammaBarMul]; ring
  have homegaBar :=
    shiftedSquareFixedBasis_embeddingStarGenerator_norm_le_two_mul_sqrt_abs
      ha0 F sigma
  have hgammaBar : ‖gammaBar‖ ≤ 4 * Real.sqrt Ashift * T₀ := by
    exact norm_main3IntegralTargetLinearForm_le_four_mul_sqrt_abs_mul
      ha0 (sigma (star F.omega)) T₀ hT₀nonneg homegaBar y hyCoordinates
  have hweightedGammaCoarse :
      c ^ 2 * ‖gamma‖ ≤ 8 * Real.sqrt Ashift * T₀ := by
    linarith
  intro i
  rw [hell]
  have hCauchy := abs_main3AnchorHermitianRadialAddHom_le_of_nonneg
    (sq_nonneg c) (sigma F.omega) y (Pi.single i (1 : ℤ))
  have hstandard :=
    norm_main3IntegralTargetLinearForm_standardVector_le_two_mul_sqrt_abs
      ha0 F sigma i
  have hsqrtSq : (Real.sqrt Ashift) ^ 2 = Ashift :=
    Real.sq_sqrt (abs_nonneg (a : ℝ))
  calc
    |main3AnchorHermitianRadialAddHom
        (c ^ 2) (sigma F.omega) y (Pi.single i (1 : ℤ))| ≤
        c ^ 2 * ‖gamma‖ *
          ‖main3IntegralTargetLinearForm (sigma F.omega)
            (Pi.single i (1 : ℤ))‖ := by
      simpa only [gamma] using hCauchy
    _ ≤ (8 * Real.sqrt Ashift * T₀) * (2 * Real.sqrt Ashift) := by
      exact mul_le_mul hweightedGammaCoarse hstandard
        (norm_nonneg _) (by positivity)
    _ = 16 * Ashift * T₀ := by
      rw [show (8 * Real.sqrt Ashift * T₀) * (2 * Real.sqrt Ashift) =
          16 * (Real.sqrt Ashift) ^ 2 * T₀ by ring, hsqrtSq]
    _ ≤ 32 * Ashift * T₀ := by
      nlinarith only [mul_nonneg (abs_nonneg (a : ℝ)) hT₀nonneg]

private theorem log_productHeight_le_sixtyfour_mul_log
    {Y : ℕ} (hY : 65536 ≤ Y) (A T L : ℝ)
    (hA : 1 ≤ A) (hT : 1 ≤ T) (hL0 : 0 ≤ L)
    (hlogA : Real.log A ≤ 2 * Real.log (Y : ℝ))
    (hlogT : Real.log T ≤ 5 * Real.log (Y : ℝ))
    (hL : L ≤ 2 ^ (27 : ℕ) * (Y : ℝ) * A ^ 3 * T ^ 3) :
    Real.log (L + 1) ≤ 64 * Real.log (Y : ℝ) := by
  have hYone : (1 : ℝ) ≤ Y := by exact_mod_cast (show 1 ≤ Y by omega)
  have hYpos : (0 : ℝ) < Y := zero_lt_one.trans_le hYone
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hA3 : 1 ≤ A ^ 3 := one_le_pow₀ hA
  have hT3 : 1 ≤ T ^ 3 := one_le_pow₀ hT
  have hmajorOne :
      (1 : ℝ) ≤ 2 ^ (27 : ℕ) * (Y : ℝ) * A ^ 3 * T ^ 3 := by
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by norm_num) hYone) hA3) hT3
  have hplus :
      L + 1 ≤ 2 ^ (28 : ℕ) * (Y : ℝ) * A ^ 3 * T ^ 3 := by
    calc
      L + 1 ≤
          2 ^ (27 : ℕ) * (Y : ℝ) * A ^ 3 * T ^ 3 + 1 :=
        by simpa only [add_comm] using add_le_add_right hL 1
      _ ≤ 2 * (2 ^ (27 : ℕ) * (Y : ℝ) * A ^ 3 * T ^ 3) := by
        linarith
      _ = 2 ^ (28 : ℕ) * (Y : ℝ) * A ^ 3 * T ^ 3 := by ring
  have hlog := Real.log_le_log (by positivity : 0 < L + 1) hplus
  have hlogTwo : Real.log 2 ≤ Real.log (Y : ℝ) :=
    Real.log_le_log (by norm_num) (by
      exact_mod_cast (show 2 ≤ Y by omega))
  have hlogY0 : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg hYone
  rw [Real.log_mul
      (mul_ne_zero
        (mul_ne_zero (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)) hYpos.ne')
        (pow_ne_zero _ hApos.ne'))
      (pow_ne_zero _ hTpos.ne'),
    Real.log_mul
      (mul_ne_zero (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)) hYpos.ne')
      (pow_ne_zero _ hApos.ne'),
    Real.log_mul (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)) hYpos.ne',
    Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog
  linarith

private theorem log_four_mul_scaleSum_le_twelve_mul_log
    {Y : ℕ} (hY : 65536 ≤ Y) (U T : ℝ)
    (hU0 : 0 ≤ U) (hU : U ≤ T ^ 2) (hT : 1 ≤ T)
    (hlogT : Real.log T ≤ 5 * Real.log (Y : ℝ)) :
    Real.log (4 * (U + 5)) ≤ 12 * Real.log (Y : ℝ) := by
  have hYone : (1 : ℝ) ≤ Y := by exact_mod_cast (show 1 ≤ Y by omega)
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hT2one : (1 : ℝ) ≤ T ^ 2 := by nlinarith
  have hupper : 4 * (U + 5) ≤ 24 * T ^ 2 := by nlinarith
  have hlog := Real.log_le_log (by positivity : 0 < 4 * (U + 5)) hupper
  have hlog24 : Real.log 24 ≤ Real.log (Y : ℝ) :=
    Real.log_le_log (by norm_num) (by
      exact_mod_cast (show 24 ≤ Y by omega))
  have hlogY0 : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg hYone
  rw [Real.log_mul (by norm_num : (24 : ℝ) ≠ 0)
      (pow_ne_zero _ hTpos.ne'), Real.log_pow] at hlog
  norm_num at hlog
  linarith

/-- A nonempty real fixed-key cell has one completion and one product basis
whose actual reduced-slope height satisfies both uniform logarithmic budgets.
The returned completion specification is the original strong specification,
so all cover conclusions and every bound below concern the identical
certificate and matrices `G,H`. -/
theorem exists_main3LargeAnalyticFixedKeyRealCellTargetCompletionProductHeightLogBudget
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
    let Ashift := |(shiftedSquareA h v : ℝ)|
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
          T cert.ell cert.anchor (2 * E) K 8 T₀ G H ∧
        (let rho := cert.ell cert.anchor
         let U := K / 2
         let V := 1 + (8 : ℝ) / 2
         let M₀ := 2 * rho * V / (2 * E)
         let beta := cert.ell (fun i ↦ G i 1)
         let z := -K * beta / (2 * E)
         let L := 2 * (T₀ + 1) *
           reducedSlopeMatrixEntryBound U V M₀ z
         (∀ i, |cert.ell (Pi.single i (1 : ℤ))| ≤ 32 * Ashift * T₀) ∧
         |beta| ≤ 128 * Ashift * T₀ ^ 2 ∧
         |z| / U ≤ 2 ^ (27 : ℕ) * Ashift ^ 3 ∧
         1 / U ≤ 2 ^ (21 : ℕ) * (Y : ℝ) * Ashift ^ 3 / T₀ ^ 2 ∧
         U ≤ T₀ ^ 2 ∧
         M₀ / V ≤ 2 ∧ V / M₀ ≤ 4 ∧
         (∀ i j, |((((G * H) i j : ℤ) : ℝ))| ≤ L) ∧
         L ≤ 2 ^ (27 : ℕ) * (Y : ℝ) * Ashift ^ 3 * T₀ ^ 3 ∧
         Real.log (L + 1) ≤ 64 * Real.log (Y : ℝ) ∧
         Real.log (4 * (U + V)) ≤ 12 * Real.log (Y : ℝ)) := by
  dsimp only
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
  let Ashift := |(a : ℝ)|
  obtain ⟨cert, hell, hrhoLower, hrhoUpper, hcalibration, G, H, hcompletion⟩ :=
    exists_main3LargeAnalyticFixedKeyRealCellTargetCompletionEntryBoundCover
      htheta hY hi key cell ha hnonempty
  refine ⟨cert, ?_, ?_, ?_, ?_, G, H, ?_, ?_⟩
  · simpa only [F, sigma, c, a] using hell
  · simpa only [E] using hrhoLower
  · simpa only [E] using hrhoUpper
  · simpa only [E, K, Mmesh, Delta, a] using hcalibration
  · simpa only [T, E, K, T₀, a] using hcompletion
  · let rho := cert.ell cert.anchor
    let U := K / 2
    let V := 1 + (8 : ℝ) / 2
    let M₀ := 2 * rho * V / (2 * E)
    let beta := cert.ell (fun i ↦ G i 1)
    let z := -K * beta / (2 * E)
    let L := 2 * (T₀ + 1) * reducedSlopeMatrixEntryBound U V M₀ z
    have hAone : 1 ≤ Ashift := by
      dsimp only [Ashift, a]
      exact_mod_cast Int.one_le_abs (ne_of_lt ha)
    have hApos : 0 < Ashift := zero_lt_one.trans_le hAone
    have hsqrtAOne : 1 ≤ Real.sqrt Ashift := Real.one_le_sqrt.mpr hAone
    have hE : 0 < E := by
      dsimp only [E]
      exact main3LargeAnalyticFixedKeyTargetScaleUpper_pos_of_mem
        htheta hY hi key (Sum.inl cell) cert.anchor_mem
    have hT₀one : 1 ≤ T₀ := by
      dsimp only [T₀, a]
      exact one_le_main3LargeAnalyticFixedKeyTargetCoordinateRadius_of_targetImage_nonempty
        htheta hY hi key (Sum.inl cell) hnonempty
    have hT₀pos : 0 < T₀ := zero_lt_one.trans_le hT₀one
    have hDelta : 0 < Delta := by
      dsimp only [Delta]
      exact Real.sqrt_pos.2 (abs_pos.mpr (by
        exact_mod_cast NumberField.discr_ne_zero
          (rationalQuadraticAlgebra (-a))))
    have hMmesh : 0 < Mmesh := by
      dsimp only [Mmesh]
      exact_mod_cast (main3UnbalancedM_parameter_package theta Y htheta
        (by omega : 2 ≤ Y)).1
    have hMmeshLe : Mmesh ≤ (Y : ℝ) := by
      dsimp only [Mmesh]
      exact_mod_cast (main3UnbalancedM_parameter_package theta Y htheta
        (by omega : 2 ≤ Y)).2.1
    have hK : 0 < K := by dsimp only [K]; positivity
    have hU : 0 < U := by dsimp only [U]; positivity
    have hV : 0 < V := by dsimp only [V]; norm_num
    have hT₀nonneg : 0 ≤ T₀ := hT₀pos.le
    have hellBasis : ∀ i,
        |cert.ell (Pi.single i (1 : ℤ))| ≤ 32 * Ashift * T₀ := by
      simpa only [a, F, sigma, c, T₀, Ashift] using
        main3LargeAnalytic_realCellHermitian_standardBasis_bound
          htheta hY hi key cell ha cert.anchor_mem cert.ell
            (by simpa only [a, F, sigma, c] using hell)
    have hGentry := hcompletion.1
    have hbeta : |beta| ≤ 128 * Ashift * T₀ ^ 2 := by
      have hcolumn := abs_addHom_sl2_column_le cert.ell G
        (T₀ + 1) (32 * Ashift * T₀) (by positivity) hGentry hellBasis 1
      calc
        |beta| ≤ 2 * (T₀ + 1) * (32 * Ashift * T₀) := by
          simpa only [beta] using hcolumn
        _ ≤ 2 * (2 * T₀) * (32 * Ashift * T₀) := by
          gcongr
          linarith
        _ = 128 * Ashift * T₀ ^ 2 := by ring
    have hT₀sq : T₀ ^ 2 = 2 ^ (20 : ℕ) * Ashift ^ 2 * E := by
      dsimp only [T₀, main3LargeAnalyticFixedKeyTargetCoordinateRadius,
        shiftedSquareRawCoordinateScaleLoss, Ashift]
      change (1024 * |(a : ℝ)| * Real.sqrt E) ^ 2 =
        2 ^ (20 : ℕ) * |(a : ℝ)| ^ 2 * E
      calc
        (1024 * |(a : ℝ)| * Real.sqrt E) ^ 2 =
            2 ^ (20 : ℕ) * |(a : ℝ)| ^ 2 * (Real.sqrt E) ^ 2 := by
          ring
        _ = 2 ^ (20 : ℕ) * |(a : ℝ)| ^ 2 * E := by
          rw [Real.sq_sqrt hE.le]
    have hDeltaLower : Real.sqrt Ashift ≤ Delta := by
      dsimp only [Delta, Ashift]
      exact Real.sqrt_le_sqrt (by
        exact_mod_cast
          abs_le_abs_rationalQuadraticAlgebra_neg_fieldDiscriminant_of_squarefree
            a (main3LargeAnalytic_shift_squarefree hi))
    have hDeltaUpper : Delta ≤ 2 * Real.sqrt Ashift := by
      dsimp only [Delta, Ashift]
      exact sqrt_abs_rationalQuadraticAlgebra_neg_fieldDiscriminant_le a
    have hsqrtALeA : Real.sqrt Ashift ≤ Ashift := by
      nlinarith [Real.sq_sqrt (zero_le_one.trans hAone)]
    have hDeltaA : Delta ≤ 2 * Ashift := hDeltaUpper.trans (by linarith)
    have hUEq : U = E / (Mmesh * Delta) := by
      dsimp only [U, K]
      field_simp [hMmesh.ne', hDelta.ne']
    have hzRatioEq : |z| / U = |beta| / E := by
      dsimp only [z, U]
      rw [abs_div, abs_mul, abs_neg, abs_of_pos hK,
        abs_of_pos (mul_pos (by norm_num) hE)]
      field_simp [hK.ne', hE.ne']
    have hzRatio : |z| / U ≤ 2 ^ (27 : ℕ) * Ashift ^ 3 := by
      rw [hzRatioEq]
      apply (div_le_iff₀ hE).2
      calc
        |beta| ≤ 128 * Ashift * T₀ ^ 2 := hbeta
        _ = 2 ^ (27 : ℕ) * Ashift ^ 3 * E := by
          rw [hT₀sq]
          norm_num
          ring
    have hmeshDelta : Mmesh * Delta ≤ 2 * (Y : ℝ) * Ashift := by
      calc
        Mmesh * Delta ≤ (Y : ℝ) * (2 * Ashift) := by
          exact mul_le_mul hMmeshLe hDeltaA hDelta.le (by positivity)
        _ = 2 * (Y : ℝ) * Ashift := by ring
    have hInvUEq : 1 / U = Mmesh * Delta / E := by
      rw [hUEq]
      field_simp [hMmesh.ne', hDelta.ne', hE.ne']
    have hInvU :
        1 / U ≤ 2 ^ (21 : ℕ) * (Y : ℝ) * Ashift ^ 3 / T₀ ^ 2 := by
      rw [hInvUEq]
      have hleft : Mmesh * Delta / E ≤
          (2 * (Y : ℝ) * Ashift) / E :=
        div_le_div_of_nonneg_right hmeshDelta hE.le
      calc
        Mmesh * Delta / E ≤ (2 * (Y : ℝ) * Ashift) / E := hleft
        _ = 2 ^ (21 : ℕ) * (Y : ℝ) * Ashift ^ 3 / T₀ ^ 2 := by
          rw [hT₀sq]
          field_simp [hApos.ne', hE.ne']
    have hdenOne : 1 ≤ Mmesh * Delta := by
      have hMmeshOne : 1 ≤ Mmesh := by
        dsimp only [Mmesh]
        exact_mod_cast (show 1 ≤ main3UnbalancedM theta Y by
          have := (main3UnbalancedM_parameter_package theta Y htheta
            (by omega : 2 ≤ Y)).1
          omega)
      exact one_le_mul_of_one_le_of_one_le
        hMmeshOne
        (hsqrtAOne.trans hDeltaLower)
    have hUleE : U ≤ E := by
      rw [hUEq]
      exact div_le_self hE.le hdenOne
    have hEleT₀sq : E ≤ T₀ ^ 2 := by
      rw [hT₀sq]
      have hA2 : 1 ≤ Ashift ^ 2 := one_le_pow₀ hAone
      nlinarith [mul_nonneg (sub_nonneg.mpr hA2) hE.le]
    have hUle : U ≤ T₀ ^ 2 := hUleE.trans hEleT₀sq
    have hU0 : 0 ≤ U := hU.le
    have hcal :
        V = 5 ∧ M₀ = 5 * rho / E ∧
          (5 / 4 : ℝ) ≤ M₀ ∧ M₀ ≤ 10 ∧
          4 * (U + V) = 2 * K + 20 ∧
          36 * 8 * K = 576 * E / (Mmesh * Delta) := by
      simpa only [rho, U, V, M₀, E, K, Mmesh, Delta, a] using hcalibration
    have hM₀pos : 0 < M₀ := by linarith [hcal.2.2.1]
    have hM₀divV : M₀ / V ≤ 2 := by
      rw [hcal.1]
      exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 5)).2 (by
        linarith [hcal.2.2.2.1])
    have hVdivM₀ : V / M₀ ≤ 4 := by
      apply (div_le_iff₀ hM₀pos).2
      rw [hcal.1]
      linarith [hcal.2.2.1]
    have hWentry : ∀ i j, |((((G * H) i j : ℤ) : ℝ))| ≤ L := by
      intro i j
      exact hcompletion.2.2 i j
    have hInvUCoarse : 1 / U ≤ 2 ^ (21 : ℕ) * (Y : ℝ) * Ashift ^ 3 := by
      have hnumerator0 :
          0 ≤ 2 ^ (21 : ℕ) * (Y : ℝ) * Ashift ^ 3 := by positivity
      have hT₀sqOne : 1 ≤ T₀ ^ 2 := one_le_pow₀ hT₀one
      calc
        1 / U ≤
            2 ^ (21 : ℕ) * (Y : ℝ) * Ashift ^ 3 / T₀ ^ 2 := hInvU
        _ ≤ 2 ^ (21 : ℕ) * (Y : ℝ) * Ashift ^ 3 := by
          exact div_le_self hnumerator0 hT₀sqOne
    let Q := (Y : ℝ) * Ashift ^ 3
    have hQ : (65536 : ℝ) ≤ Q := by
      dsimp only [Q]
      have hA3 : 1 ≤ Ashift ^ 3 := one_le_pow₀ hAone
      calc
        (65536 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
        _ = (Y : ℝ) * 1 := by ring
        _ ≤ (Y : ℝ) * Ashift ^ 3 := by gcongr
    have hQ0 : 0 ≤ Q := by positivity
    have hzRatioQ : |z| / U ≤ 2048 * Q := by
      calc
        |z| / U ≤ 2 ^ (27 : ℕ) * Ashift ^ 3 := hzRatio
        _ = 2048 * 65536 * Ashift ^ 3 := by norm_num
        _ ≤ 2048 * (Y : ℝ) * Ashift ^ 3 := by
          gcongr
          exact_mod_cast hY
        _ = 2048 * Q := by dsimp only [Q]; ring
    have hInvUQ : 1 / U ≤ 2 ^ (21 : ℕ) * Q := by
      simpa only [Q, mul_assoc] using hInvUCoarse
    have hbracket :
        M₀ / V + |z| / U + 1 / U ≤ 3 * 2 ^ (20 : ℕ) * Q := by
      have hMpart : M₀ / V ≤ Q := hM₀divV.trans (by linarith)
      norm_num at hzRatioQ hInvUQ ⊢
      linarith
    have hsecond : U + V / M₀ ≤ 5 * T₀ ^ 2 := by
      have hT₀sqOne : 1 ≤ T₀ ^ 2 := one_le_pow₀ hT₀one
      calc
        U + V / M₀ ≤ T₀ ^ 2 + 4 := add_le_add hUle hVdivM₀
        _ ≤ 5 * T₀ ^ 2 := by linarith only [hT₀sqOne]
    have hLnonneg : 0 ≤ L := by
      have hradius0 : 0 ≤ slopeStandardBasisRadius U V M₀ z := by
        exact (div_nonneg hM₀pos.le hV.le).trans (le_max_left _ _)
      have hcolumn0 : 0 ≤ max U (V / M₀) :=
        hU0.trans (le_max_left _ _)
      have hentry0 : 0 ≤ reducedSlopeMatrixEntryBound U V M₀ z := by
        rw [reducedSlopeMatrixEntryBound]
        exact mul_nonneg (mul_nonneg (by norm_num) hradius0) hcolumn0
      dsimp only [L]
      exact mul_nonneg (mul_nonneg (by norm_num) (by linarith only [hT₀nonneg]))
        hentry0
    have hL : L ≤ 2 ^ (27 : ℕ) * (Y : ℝ) * Ashift ^ 3 * T₀ ^ 3 := by
      have hexpanded : L ≤ 4 * (T₀ + 1) *
          (M₀ / V + |z| / U + 1 / U) * (U + V / M₀) := by
        dsimp only [L]
        exact primitiveWedgeProductEntryHeight_le_expanded
          T₀ U V M₀ z hT₀nonneg hU hV hM₀pos
      have hTone : T₀ + 1 ≤ 2 * T₀ := by linarith only [hT₀one]
      have hbracket0 : 0 ≤ M₀ / V + |z| / U + 1 / U := by
        exact add_nonneg
          (add_nonneg (div_nonneg hM₀pos.le hV.le)
            (div_nonneg (abs_nonneg z) hU.le))
          (div_nonneg (by norm_num) hU.le)
      have hsecond0 : 0 ≤ U + V / M₀ :=
        add_nonneg hU.le (div_nonneg hV.le hM₀pos.le)
      have hlargeBracket0 : 0 ≤ 3 * 2 ^ (20 : ℕ) * Q := by
        exact mul_nonneg (by norm_num) hQ0
      have hlargeFirst0 : 0 ≤ 4 * (2 * T₀) := by positivity
      have hfirstProduct :
          4 * (T₀ + 1) * (M₀ / V + |z| / U + 1 / U) ≤
            4 * (2 * T₀) * (3 * 2 ^ (20 : ℕ) * Q) := by
        calc
          4 * (T₀ + 1) * (M₀ / V + |z| / U + 1 / U) ≤
              4 * (2 * T₀) * (M₀ / V + |z| / U + 1 / U) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hTone (by norm_num)) hbracket0
          _ ≤ 4 * (2 * T₀) * (3 * 2 ^ (20 : ℕ) * Q) :=
            mul_le_mul_of_nonneg_left hbracket hlargeFirst0
      calc
        L ≤ 4 * (T₀ + 1) *
            (M₀ / V + |z| / U + 1 / U) * (U + V / M₀) := hexpanded
        _ ≤ 4 * (2 * T₀) * (3 * 2 ^ (20 : ℕ) * Q) *
            (5 * T₀ ^ 2) := by
          calc
            4 * (T₀ + 1) * (M₀ / V + |z| / U + 1 / U) *
                (U + V / M₀) ≤
                (4 * (2 * T₀) * (3 * 2 ^ (20 : ℕ) * Q)) *
                  (U + V / M₀) :=
              mul_le_mul_of_nonneg_right hfirstProduct hsecond0
            _ ≤ (4 * (2 * T₀) * (3 * 2 ^ (20 : ℕ) * Q)) *
                  (5 * T₀ ^ 2) :=
              mul_le_mul_of_nonneg_left hsecond
                (mul_nonneg hlargeFirst0 hlargeBracket0)
        _ = (120 * 2 ^ (20 : ℕ)) * Q * T₀ ^ 3 := by ring
        _ ≤ 2 ^ (27 : ℕ) * Q * T₀ ^ 3 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by norm_num) hQ0)
            (pow_nonneg hT₀nonneg 3)
        _ = 2 ^ (27 : ℕ) * (Y : ℝ) * Ashift ^ 3 * T₀ ^ 3 := by
          dsimp only [Q]
          ring
    have hlogA := main3LargeAnalytic_log_abs_shift_le_two_mul_log
      htheta hY hi
    have hlogT₀ :=
      log_main3LargeAnalyticFixedKeyTargetCoordinateRadius_le_five_mul
        htheta hY hi key (Sum.inl cell) hnonempty
    have hlogL := log_productHeight_le_sixtyfour_mul_log
      hY Ashift T₀ L hAone hT₀one hLnonneg
        (by simpa only [Ashift, a] using hlogA)
        (by simpa only [T₀, a] using hlogT₀) hL
    have hlogUVraw := log_four_mul_scaleSum_le_twelve_mul_log
      hY U T₀ hU0 hUle hT₀one
        (by simpa only [T₀, a] using hlogT₀)
    have hlogUV : Real.log (4 * (U + V)) ≤
        12 * Real.log (Y : ℝ) := by
      norm_num [V]
      exact hlogUVraw
    exact ⟨hellBasis, hbeta, hzRatio, hInvU, hUle,
      hM₀divV, hVdivM₀, hWentry, hL, hlogL, hlogUV⟩

end

end PellPaper
