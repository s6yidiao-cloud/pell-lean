import Pell.Main3LargeAnalyticRealCellNormalizedTargetBounds
import Pell.Main3LargeAnalyticFixedKeyCellTargetCompletionEntryBoundCover
import Pell.PrimitiveWedgeReducedTargetCoverShortVector
import Mathlib.Tactic

/-!
# The real-cover shortest vector in a determinant-one norm

This workspace keeps the completion-cover witnesses `cert`, `G`, and `H`
fixed.  It bounds the first column of `G * H` by using the radial and wedge
coordinates of that column, while using target-image geometry only for the
certificate anchor.  In particular, it never asserts that the shortest
column itself belongs to the finite target image.
-/

namespace PellPaper

open scoped MatrixGroups ComplexConjugate

noncomputable section

local instance main3LargeAnalyticRealCoverShortestVectorBound_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- The determinant-one max norm on the two real embeddings. -/
def main3RealScaledTwoPlaceTargetSupNorm
    (c : ℝ) (omega omegaBar : ℂ) (y : Fin 2 → ℤ) : ℝ :=
  max (|c| * ‖main3IntegralTargetLinearForm omega y‖)
    (‖main3IntegralTargetLinearForm omegaBar y‖ / |c|)

/-- Compact downstream form of the direct and reciprocal-band real-place
short-vector estimates. -/
def Main3LargeAnalyticRealCoverShortestVectorBoundSpec
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (F : ShiftedSquareFixedExplicitIntegralBasisData a) (ha : a < 0)
    (c E K : ℝ)
    {Tset : Finset (Fin 2 → ℤ)}
    (cert : PrimitiveWedgeReducedTargetCoverCertificate Tset (2 * E) K 8)
    (G H : SL(2, ℤ)) : Prop :=
  let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
  let rho := cert.ell cert.anchor
  let U := K / 2
  let V := 1 + (8 : ℝ) / 2
  let M₀ := 2 * rho * V / (2 * E)
  let beta := cert.ell (fun i ↦ G i 1)
  let z := -K * beta / (2 * E)
  let mu := firstSlopeSupNorm U V M₀ z
  let y := primitiveWedgeReducedTargetCoverShortestVector G H
  main3RealScaledTwoPlaceTargetSupNorm c
      (sigma F.omega) (sigma (star F.omega)) y ≤
        8 * Real.sqrt E * mu ∧
    ∀ S : ℝ, 0 < S → S ≤ 1 / mu →
      main3RealScaledTwoPlaceTargetSupNorm c
          (sigma F.omega) (sigma (star F.omega)) y ≤
        8 * Real.sqrt E / S

/-- Every integral target linear form at the selected positive real place is
fixed by complex conjugation. -/
private theorem main3IntegralTargetLinearForm_positiveRealPlace_conj
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : a < 0) (omega : rationalQuadraticAlgebra (-a))
    (y : Fin 2 → ℤ) :
    conj (main3IntegralTargetLinearForm
      (shiftedSquarePositiveRealPlaceEmbedding a ha omega) y) =
      main3IntegralTargetLinearForm
        (shiftedSquarePositiveRealPlaceEmbedding a ha omega) y := by
  simp [main3IntegralTargetLinearForm]

/-- On the real line, the absolute Hermitian pairing is the product of
norms. -/
private theorem abs_conj_mul_re_eq_norm_mul_of_fixed
    (u v : ℂ) (hu : conj u = u) (hv : conj v = v) :
    |(conj u * v).re| = ‖u‖ * ‖v‖ := by
  have huIm : u.im = 0 := Complex.conj_eq_iff_im.mp hu
  have hvIm : v.im = 0 := Complex.conj_eq_iff_im.mp hv
  calc
    |(conj u * v).re| = ‖conj u * v‖ :=
      Complex.abs_re_eq_norm.mpr (by simp [huIm, hvIm])
    _ = ‖u‖ * ‖v‖ := by rw [norm_mul, Complex.norm_conj]

/-- The exact radial/wedge coordinates of the reduced first column control
both real embeddings after determinant-one rescaling.  The normalized target
bounds are required only for the anchor ratio. -/
theorem real_shortest_original_vector_scaledTwoPlace_norm_bounds
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (ha : a < 0) {Tset : Finset (Fin 2 → ℤ)}
    {E Mmesh c targetNormalized : ℝ}
    (hE : 0 < E) (hMmesh : 6 ≤ Mmesh) (hc : c ≠ 0)
    (htargetLower : (1 / 2 : ℝ) ≤ targetNormalized)
    (htargetUpper : targetNormalized ≤ 2)
    (cert : PrimitiveWedgeReducedTargetCoverCertificate Tset (2 * E)
      ((2 * E / Mmesh) /
        Real.sqrt |(NumberField.discr
          (rationalQuadraticAlgebra (-a)) : ℝ)|) 8)
    (hell : cert.ell = main3AnchorHermitianRadialAddHom (c ^ 2)
      (shiftedSquarePositiveRealPlaceEmbedding a ha F.omega) cert.anchor)
    (hrhoLower : E ≤ 4 * cert.ell cert.anchor)
    (hanchorRatio :
      main3IntegralTargetLinearForm
          (shiftedSquarePositiveRealPlaceEmbedding a ha (star F.omega))
          cert.anchor /
        main3IntegralTargetLinearForm
          (shiftedSquarePositiveRealPlaceEmbedding a ha F.omega)
          cert.anchor =
        ((c ^ 2 * targetNormalized : ℝ) : ℂ))
    {G H : SL(2, ℤ)}
    (hspec : PrimitiveWedgeReducedTargetCoverSpec
      Tset cert.ell cert.anchor (2 * E)
        ((2 * E / Mmesh) /
          Real.sqrt |(NumberField.discr
            (rationalQuadraticAlgebra (-a)) : ℝ)|) 8 G H) :
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
    main3RealScaledTwoPlaceTargetSupNorm c
        (shiftedSquarePositiveRealPlaceEmbedding a ha F.omega)
        (shiftedSquarePositiveRealPlaceEmbedding a ha (star F.omega)) y ≤
          8 * Real.sqrt E * mu ∧
      ∀ S : ℝ, 0 < S → S ≤ 1 / mu →
        main3RealScaledTwoPlaceTargetSupNorm c
            (shiftedSquarePositiveRealPlaceEmbedding a ha F.omega)
            (shiftedSquarePositiveRealPlaceEmbedding a ha (star F.omega)) y ≤
          8 * Real.sqrt E / S := by
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
  change main3RealScaledTwoPlaceTargetSupNorm c (sigma F.omega)
        (sigma (star F.omega)) y ≤ 8 * Real.sqrt E * mu ∧
    ∀ S : ℝ, 0 < S → S ≤ 1 / mu →
      main3RealScaledTwoPlaceTargetSupNorm c (sigma F.omega)
          (sigma (star F.omega)) y ≤ 8 * Real.sqrt E / S
  have hdiscZ : NumberField.discr (rationalQuadraticAlgebra (-a)) ≠ 0 :=
    NumberField.discr_ne_zero _
  have hdiscR :
      (NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ) ≠ 0 := by
    exact_mod_cast hdiscZ
  have hDelta : 0 < Delta := by
    dsimp only [Delta]
    exact Real.sqrt_pos.2 (abs_pos.mpr hdiscR)
  have hMmeshPos : 0 < Mmesh := lt_of_lt_of_le (by norm_num) hMmesh
  have hK : 0 < K := by dsimp only [K]; positivity
  have hrhoPos : 0 < rho := by
    dsimp only [rho]
    nlinarith
  have hU : 0 < U := by dsimp only [U]; positivity
  have hV : 0 < V := by dsimp only [V]; norm_num
  have hM₀ : 0 < M₀ := by dsimp only [M₀]; positivity
  have hmuPos : 0 < mu := by
    dsimp only [mu]
    exact firstSlopeSupNorm_pos U V M₀ z hU hV hM₀
  have hmu : 0 ≤ mu := hmuPos.le
  have hshort := hspec.shortest_original_vector
  dsimp only at hshort
  change y ≠ 0 ∧ IsCoprime (y 0) (y 1) ∧
    max |2 * cert.ell y / (2 * E)|
      |2 * (main3IntegralTargetWedge cert.anchor y : ℝ) / K| = mu at hshort
  have hminimum := hshort.2.2
  have hradialNormalized : |2 * cert.ell y / (2 * E)| ≤ mu := by
    rw [← hminimum]
    exact le_max_left _ _
  have hwedgeNormalized :
      |2 * (main3IntegralTargetWedge cert.anchor y : ℝ) / K| ≤ mu := by
    rw [← hminimum]
    exact le_max_right _ _
  have hradial : |cert.ell y| ≤ E * mu := by
    rw [abs_div, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hradialNormalized
    rw [abs_of_pos hE] at hradialNormalized
    have hden : 0 < 2 * E := mul_pos (by norm_num) hE
    have hscaled := (div_le_iff₀ hden).mp hradialNormalized
    nlinarith
  have hwedge : |(main3IntegralTargetWedge cert.anchor y : ℝ)| ≤
      K * mu / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hK,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hwedgeNormalized
    have hscaled := (div_le_iff₀ hK).mp hwedgeNormalized
    nlinarith
  have hanchorReal : conj anchorValue = anchorValue := by
    simpa only [anchorValue, sigma] using
      main3IntegralTargetLinearForm_positiveRealPlace_conj ha F.omega cert.anchor
  have hanchorBarReal : conj anchorBarValue = anchorBarValue := by
    simpa only [anchorBarValue, sigma] using
      main3IntegralTargetLinearForm_positiveRealPlace_conj ha (star F.omega) cert.anchor
  have hyReal : conj yValue = yValue := by
    simpa only [yValue, sigma] using
      main3IntegralTargetLinearForm_positiveRealPlace_conj ha F.omega y
  have hyBarReal : conj yBarValue = yBarValue := by
    simpa only [yBarValue, sigma] using
      main3IntegralTargetLinearForm_positiveRealPlace_conj ha (star F.omega) y
  have hellY : cert.ell y = c ^ 2 * (conj anchorValue * yValue).re := by
    have hfun := congrArg (fun f : (Fin 2 → ℤ) →+ ℝ ↦ f y) hell
    simpa only [main3AnchorHermitianRadialAddHom_apply,
      sigma, anchorValue, yValue] using hfun
  have hellAnchor : cert.ell cert.anchor = c ^ 2 * ‖anchorValue‖ ^ 2 := by
    calc
      cert.ell cert.anchor =
          main3AnchorHermitianRadialAddHom (c ^ 2)
            (sigma F.omega) cert.anchor cert.anchor := by rw [hell]
      _ = c ^ 2 * ‖main3IntegralTargetLinearForm
          (sigma F.omega) cert.anchor‖ ^ 2 :=
        main3AnchorHermitianRadialAddHom_self (c ^ 2)
          (sigma F.omega) cert.anchor
      _ = c ^ 2 * ‖anchorValue‖ ^ 2 := by rfl
  have hanchorScaleSq :
      E ≤ 4 * (|c| * ‖anchorValue‖) ^ 2 := by
    calc
      E ≤ 4 * cert.ell cert.anchor := hrhoLower
      _ = 4 * (|c| * ‖anchorValue‖) ^ 2 := by
        rw [hellAnchor, ← sq_abs]
        ring
  have hsqrtSq : (Real.sqrt E) ^ 2 = E := Real.sq_sqrt hE.le
  have hanchorScale :
      Real.sqrt E ≤ 2 * (|c| * ‖anchorValue‖) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg E) (by positivity)).mp
    rw [hsqrtSq]
    nlinarith
  have hanchorHalf :
      Real.sqrt E / 2 ≤ |c| * ‖anchorValue‖ := by linarith
  have hpairAbs :
      |(conj anchorValue * yValue).re| =
        ‖anchorValue‖ * ‖yValue‖ :=
    abs_conj_mul_re_eq_norm_mul_of_fixed
      anchorValue yValue hanchorReal hyReal
  have hellAbs : |cert.ell y| =
      (|c| * ‖anchorValue‖) * (|c| * ‖yValue‖) := by
    rw [hellY, abs_mul, abs_of_nonneg (sq_nonneg c), hpairAbs, ← sq_abs]
    ring
  have hproduct :
      (|c| * ‖anchorValue‖) * (|c| * ‖yValue‖) ≤ E * mu := by
    rw [← hellAbs]
    exact hradial
  have hrootTimesFirst :
      Real.sqrt E / 2 * (|c| * ‖yValue‖) ≤ E * mu := by
    calc
      Real.sqrt E / 2 * (|c| * ‖yValue‖) ≤
          (|c| * ‖anchorValue‖) * (|c| * ‖yValue‖) := by
        gcongr
      _ ≤ E * mu := hproduct
  have hfirst : |c| * ‖yValue‖ ≤ 2 * Real.sqrt E * mu := by
    have hsqrtPos : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
    nlinarith
  have hanchorNormPos : 0 < ‖anchorValue‖ := by
    by_contra hnot
    have hzero : ‖anchorValue‖ = 0 := le_antisymm (le_of_not_gt hnot) (norm_nonneg _)
    simp only [hzero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero] at hellAnchor
    rw [hellAnchor] at hrhoLower
    nlinarith
  have htargetPos : 0 < targetNormalized := by linarith
  have hratioNorm := congrArg norm hanchorRatio
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (sq_pos_of_ne_zero hc) htargetPos)] at hratioNorm
  have hanchorNormNe : ‖anchorValue‖ ≠ 0 := ne_of_gt hanchorNormPos
  have hanchorBarMul :
      ‖anchorBarValue‖ = c ^ 2 * targetNormalized * ‖anchorValue‖ := by
    apply (div_eq_iff hanchorNormNe).mp
    simpa only [anchorBarValue, anchorValue, sigma,
      mul_comm, mul_left_comm, mul_assoc] using hratioNorm
  have hcrossEq :
      ‖anchorBarValue * yValue - yBarValue * anchorValue‖ =
        |(main3IntegralTargetWedge cert.anchor y : ℝ)| * Delta := by
    have hwedgeNorm :=
      norm_main3IntegralTargetLinearForm_wedge_eq F sigma cert.anchor y
    simpa only [anchorBarValue, anchorValue, yBarValue, yValue,
      sigma, Delta] using hwedgeNorm
  have hcross :
      ‖anchorBarValue * yValue - yBarValue * anchorValue‖ ≤
        E * mu / Mmesh := by
    rw [hcrossEq]
    calc
      |(main3IntegralTargetWedge cert.anchor y : ℝ)| * Delta ≤
          (K * mu / 2) * Delta :=
        mul_le_mul_of_nonneg_right hwedge hDelta.le
      _ = E * mu / Mmesh := by
        dsimp only [K]
        field_simp [hDelta.ne', hMmeshPos.ne']
  have hEmu : 0 ≤ E * mu := mul_nonneg hE.le hmu
  have hcrossCoarse : E * mu / Mmesh ≤ E * mu := by
    apply (div_le_iff₀ hMmeshPos).2
    calc
      E * mu ≤ (E * mu) * 1 := by simp
      _ ≤ (E * mu) * Mmesh := by
        exact mul_le_mul_of_nonneg_left (by linarith) hEmu
  have hcrossScaled : E * mu / Mmesh ≤
      2 * (|c| * ‖anchorValue‖) * Real.sqrt E * mu := by
    calc
      E * mu / Mmesh ≤ E * mu := hcrossCoarse
      _ = Real.sqrt E * (Real.sqrt E * mu) := by
        conv_lhs => rw [← hsqrtSq]
        ring
      _ ≤ (2 * (|c| * ‖anchorValue‖)) *
          (Real.sqrt E * mu) := by
        exact mul_le_mul_of_nonneg_right hanchorScale
          (mul_nonneg (Real.sqrt_nonneg E) hmu)
      _ = 2 * (|c| * ‖anchorValue‖) * Real.sqrt E * mu := by ring
  have hbarProduct : ‖anchorBarValue‖ * ‖yValue‖ ≤
      4 * (|c| * ‖anchorValue‖) * Real.sqrt E * mu := by
    calc
      ‖anchorBarValue‖ * ‖yValue‖ =
          targetNormalized * (|c| * ‖anchorValue‖) *
            (|c| * ‖yValue‖) := by
        rw [hanchorBarMul, ← sq_abs]
        field_simp [abs_ne_zero.mpr hc]
      _ ≤ 2 * (|c| * ‖anchorValue‖) *
          (2 * Real.sqrt E * mu) := by
        gcongr
      _ = 4 * (|c| * ‖anchorValue‖) * Real.sqrt E * mu := by ring
  have hyBarAnchor : ‖yBarValue * anchorValue‖ ≤
      ‖anchorBarValue * yValue‖ +
        ‖anchorBarValue * yValue - yBarValue * anchorValue‖ := by
    calc
      ‖yBarValue * anchorValue‖ =
          ‖anchorBarValue * yValue -
            (anchorBarValue * yValue - yBarValue * anchorValue)‖ := by ring_nf
      _ ≤ ‖anchorBarValue * yValue‖ +
          ‖anchorBarValue * yValue - yBarValue * anchorValue‖ :=
        norm_sub_le _ _
  have hyBarAnchorBound : ‖yBarValue * anchorValue‖ ≤
      6 * (|c| * ‖anchorValue‖) * Real.sqrt E * mu := by
    calc
      ‖yBarValue * anchorValue‖ ≤
          ‖anchorBarValue * yValue‖ +
            ‖anchorBarValue * yValue - yBarValue * anchorValue‖ :=
        hyBarAnchor
      _ ≤ ‖anchorBarValue‖ * ‖yValue‖ + E * mu / Mmesh := by
        rw [norm_mul]
        gcongr
      _ ≤ 4 * (|c| * ‖anchorValue‖) * Real.sqrt E * mu +
          2 * (|c| * ‖anchorValue‖) * Real.sqrt E * mu := by
        gcongr
      _ = 6 * (|c| * ‖anchorValue‖) * Real.sqrt E * mu := by ring
  have hanchorScalePos : 0 < |c| * ‖anchorValue‖ :=
    mul_pos (abs_pos.mpr hc) hanchorNormPos
  have hsecond : ‖yBarValue‖ / |c| ≤ 8 * Real.sqrt E * mu := by
    have hmul : (|c| * ‖anchorValue‖) * (‖yBarValue‖ / |c|) ≤
        (|c| * ‖anchorValue‖) * (8 * Real.sqrt E * mu) := by
      calc
        (|c| * ‖anchorValue‖) * (‖yBarValue‖ / |c|) =
            ‖yBarValue * anchorValue‖ := by
          rw [norm_mul]
          field_simp [abs_ne_zero.mpr hc]
        _ ≤ 6 * (|c| * ‖anchorValue‖) * Real.sqrt E * mu :=
          hyBarAnchorBound
        _ ≤ (|c| * ‖anchorValue‖) *
            (8 * Real.sqrt E * mu) := by
          have hnonneg : 0 ≤
              (|c| * ‖anchorValue‖) * Real.sqrt E * mu := by positivity
          calc
            6 * (|c| * ‖anchorValue‖) * Real.sqrt E * mu =
                6 * ((|c| * ‖anchorValue‖) * Real.sqrt E * mu) := by ring
            _ ≤ 8 * ((|c| * ‖anchorValue‖) * Real.sqrt E * mu) :=
              mul_le_mul_of_nonneg_right (by norm_num) hnonneg
            _ = (|c| * ‖anchorValue‖) *
                (8 * Real.sqrt E * mu) := by ring
    exact le_of_mul_le_mul_left hmul hanchorScalePos
  have hfirstCoarse : |c| * ‖yValue‖ ≤ 8 * Real.sqrt E * mu := by
    have hnonneg : 0 ≤ Real.sqrt E * mu := by positivity
    calc
      |c| * ‖yValue‖ ≤ 2 * Real.sqrt E * mu := hfirst
      _ = 2 * (Real.sqrt E * mu) := by ring
      _ ≤ 8 * (Real.sqrt E * mu) :=
        mul_le_mul_of_nonneg_right (by norm_num) hnonneg
      _ = 8 * Real.sqrt E * mu := by ring
  have hdirect : main3RealScaledTwoPlaceTargetSupNorm c (sigma F.omega)
      (sigma (star F.omega)) y ≤ 8 * Real.sqrt E * mu := by
    unfold main3RealScaledTwoPlaceTargetSupNorm
    simpa only [yValue, yBarValue] using max_le hfirstCoarse hsecond
  refine ⟨hdirect, ?_⟩
  intro S hS hband
  have hSmu : S * mu ≤ 1 := (le_div_iff₀ hmuPos).mp hband
  have hmuInvS : mu ≤ 1 / S := by
    apply (le_div_iff₀ hS).2
    calc
      mu * S = S * mu := mul_comm _ _
      _ ≤ 1 := hSmu
  calc
    main3RealScaledTwoPlaceTargetSupNorm c (sigma F.omega)
        (sigma (star F.omega)) y ≤ 8 * Real.sqrt E * mu := hdirect
    _ ≤ 8 * Real.sqrt E * (1 / S) := by
      exact mul_le_mul_of_nonneg_left hmuInvS (by positivity)
    _ = 8 * Real.sqrt E / S := by ring

/-- The literal Main3 real-cell completion witnesses satisfy the generic
two-place estimate.  Only `cert.anchor_mem` is converted back to a coordinate
point; no such conversion is made for the product-basis first column. -/
theorem main3LargeAnalyticFixedKeyRealCell_completion_shortestVector_bound
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : RealSquareMapCellPairIndex)
    (ha : shiftedSquareA h v < 0) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let a := shiftedSquareA h v
    let F := shiftedSquareFixedExplicitIntegralBasisData
      a (main3LargeAnalytic_shift_squarefree hi)
    let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
    let c := main3LargeAnalyticRealCellSignedCentre theta Y h v cell
    let Tset := main3LargeAnalyticFixedKeyCellTargetVectorImage
      htheta hY hi key (Sum.inl cell)
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    let Delta := Real.sqrt
      |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)|
    let Mmesh := (main3UnbalancedM theta Y : ℝ)
    let K := (2 * E / Mmesh) / Delta
    let T₀ := main3LargeAnalyticFixedKeyTargetCoordinateRadius a Y key
    ∀ (cert : PrimitiveWedgeReducedTargetCoverCertificate
        Tset (2 * E) K 8),
      cert.ell = main3AnchorHermitianRadialAddHom
          (c ^ 2) (sigma F.omega) cert.anchor →
      E ≤ 4 * cert.ell cert.anchor →
      ∀ (G H : SL(2, ℤ)),
        PrimitiveWedgeReducedTargetCoverCompletionEntryBoundSpec
            Tset cert.ell cert.anchor (2 * E) K 8 T₀ G H →
        let rho := cert.ell cert.anchor
        let U := K / 2
        let V := 1 + (8 : ℝ) / 2
        let M₀ := 2 * rho * V / (2 * E)
        let beta := cert.ell (fun i ↦ G i 1)
        let z := -K * beta / (2 * E)
        let mu := firstSlopeSupNorm U V M₀ z
        let y := primitiveWedgeReducedTargetCoverShortestVector G H
        main3RealScaledTwoPlaceTargetSupNorm c
            (sigma F.omega) (sigma (star F.omega)) y ≤
              8 * Real.sqrt E * mu ∧
          ∀ S : ℝ, 0 < S → S ≤ 1 / mu →
            main3RealScaledTwoPlaceTargetSupNorm c
                (sigma F.omega) (sigma (star F.omega)) y ≤
              8 * Real.sqrt E / S := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let a := shiftedSquareA h v
  let F := shiftedSquareFixedExplicitIntegralBasisData
    a (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
  let c := main3LargeAnalyticRealCellSignedCentre theta Y h v cell
  let Tset := main3LargeAnalyticFixedKeyCellTargetVectorImage
    htheta hY hi key (Sum.inl cell)
  let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let Delta := Real.sqrt
    |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)|
  let Mmesh := (main3UnbalancedM theta Y : ℝ)
  let K := (2 * E / Mmesh) / Delta
  let T₀ := main3LargeAnalyticFixedKeyTargetCoordinateRadius a Y key
  intro cert hell hrhoLower G H hcompletion
  have hspec : PrimitiveWedgeReducedTargetCoverSpec
      Tset cert.ell cert.anchor (2 * E) K 8 G H := hcompletion.2.1
  obtain ⟨anchorPoint, hanchorPoint, hanchorEq⟩ :=
    (mem_main3LargeAnalyticFixedKeyCellTargetVectorImage_iff
      htheta hY hi key (Sum.inl cell) cert.anchor).mp cert.anchor_mem
  let targetNormalized :=
    main3LargeAnalyticRealCellNormalizedTarget hi ha cell anchorPoint
  have htargetBounds :=
    main3LargeAnalytic_realCellCoordinatePointImage_normalizedTarget_bounds
      htheta hY hi key cell ha hanchorPoint
  have htargetLower : (1 / 2 : ℝ) ≤ targetNormalized := by
    simpa only [targetNormalized] using htargetBounds.1
  have htargetUpper : targetNormalized ≤ 2 := by
    simpa only [targetNormalized] using htargetBounds.2
  have hgeometry :=
    main3LargeAnalytic_realCellCoordinatePointImage_normalized_geometry
      htheta hY hi key cell ha hanchorPoint
  dsimp only at hgeometry
  have hc : c ≠ 0 := by simpa only [c] using hgeometry.1
  have hanchorRatio :
      main3IntegralTargetLinearForm (sigma (star F.omega)) cert.anchor /
          main3IntegralTargetLinearForm (sigma F.omega) cert.anchor =
        ((c ^ 2 * targetNormalized : ℝ) : ℂ) := by
    have htargetEq := hgeometry.2.2.2.2.2
    rw [← hanchorEq]
    simpa only [targetNormalized, main3EmbeddingTargetRatio,
      main3LargeAnalyticRealCellTargetRatio, main3IntegralTargetLinearForm,
      shiftedSquareCoordinatePointTargetVector, Matrix.cons_val_zero,
      Matrix.cons_val_one, a, F, sigma, c] using htargetEq
  have hE : 0 < E := by
    dsimp only [E]
    exact main3LargeAnalyticFixedKeyTargetScaleUpper_pos_of_mem
      htheta hY hi key (Sum.inl cell) cert.anchor_mem
  have hMmesh : 6 ≤ Mmesh := by
    dsimp only [Mmesh]
    exact_mod_cast six_le_main3UnbalancedM htheta hY
  have hbound := real_shortest_original_vector_scaledTwoPlace_norm_bounds
    F ha hE hMmesh hc htargetLower htargetUpper cert hell hrhoLower
      hanchorRatio hspec
  simpa only [a, F, sigma, c, Tset, E, Delta, Mmesh, K, T₀,
    targetNormalized] using hbound

/-- A nonempty real fixed cell supplies one certificate and one pair `G,H`
which simultaneously satisfy the existing completion-entry cover and the
two-real-place short-vector bound. -/
theorem exists_main3LargeAnalyticFixedKeyRealCellTargetCompletionShortestVectorBound
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
    let a := shiftedSquareA h v
    let F := shiftedSquareFixedExplicitIntegralBasisData
      a (main3LargeAnalytic_shift_squarefree hi)
    let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
    let c := main3LargeAnalyticRealCellSignedCentre theta Y h v cell
    let Tset := main3LargeAnalyticFixedKeyCellTargetVectorImage
      htheta hY hi key (Sum.inl cell)
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    let Delta := Real.sqrt
      |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)|
    let Mmesh := (main3UnbalancedM theta Y : ℝ)
    let K := (2 * E / Mmesh) / Delta
    let T₀ := main3LargeAnalyticFixedKeyTargetCoordinateRadius a Y key
    ∃ cert : PrimitiveWedgeReducedTargetCoverCertificate Tset (2 * E) K 8,
      cert.ell = main3AnchorHermitianRadialAddHom
          (c ^ 2) (sigma F.omega) cert.anchor ∧
      E ≤ 4 * cert.ell cert.anchor ∧
      cert.ell cert.anchor ≤ 2 * E ∧
      ∃ G H : SL(2, ℤ),
        PrimitiveWedgeReducedTargetCoverCompletionEntryBoundSpec
            Tset cert.ell cert.anchor (2 * E) K 8 T₀ G H ∧
        Main3LargeAnalyticRealCoverShortestVectorBoundSpec
          F ha c E K cert G H := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let a := shiftedSquareA h v
  let F := shiftedSquareFixedExplicitIntegralBasisData
    a (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
  let c := main3LargeAnalyticRealCellSignedCentre theta Y h v cell
  let Tset := main3LargeAnalyticFixedKeyCellTargetVectorImage
    htheta hY hi key (Sum.inl cell)
  let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let Delta := Real.sqrt
    |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)|
  let Mmesh := (main3UnbalancedM theta Y : ℝ)
  let K := (2 * E / Mmesh) / Delta
  let T₀ := main3LargeAnalyticFixedKeyTargetCoordinateRadius a Y key
  obtain ⟨cert, hell, hrhoLower, hrhoUpper, _hcalibration,
      G, H, hcompletion⟩ :=
    exists_main3LargeAnalyticFixedKeyRealCellTargetCompletionEntryBoundCover
      htheta hY hi key cell ha hnonempty
  have hbound :=
    main3LargeAnalyticFixedKeyRealCell_completion_shortestVector_bound
      htheta hY hi key cell ha cert hell hrhoLower G H hcompletion
  refine ⟨cert, ?_, ?_, ?_, G, H, ?_, ?_⟩
  · simpa only [a, F, sigma, c] using hell
  · simpa only [E] using hrhoLower
  · simpa only [E] using hrhoUpper
  · simpa only [Tset, E, K, T₀, a] using hcompletion
  · unfold Main3LargeAnalyticRealCoverShortestVectorBoundSpec
    simpa only [a, F, sigma, c, Tset, E, Delta, Mmesh, K, T₀] using hbound


end

end PellPaper
