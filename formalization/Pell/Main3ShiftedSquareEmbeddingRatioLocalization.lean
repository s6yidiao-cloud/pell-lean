import Pell.Main3LargeAnalyticScaledCoordinatePackage
import Pell.ShiftedSquareEmbeddingRatio
import Pell.Main3ShiftedSquareZetaLocalRatioError
import Pell.ShiftedSquareEmbeddingScaleBounds
import Mathlib.Tactic

/-!
# Localized embedding ratios for the main3 shifted-square route

This pointwise adapter combines the exact invariant square-map identity, the
explicit `zeta` error, and the polynomial embedding-scale bounds.  For every
complex embedding it places both source and target ratios in one explicit
annulus and controls the target ratio around the square of the source ratio.

The first quantitative theorem is denominator-free in the source and target
coordinates.  No logarithm, finite chart cover, determinant, or counting
claim is made here.
-/

namespace PellPaper

noncomputable section

local instance main3ShiftedSquareEmbeddingRatioLocalization_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- The source ratio `rho_alpha = alpha / bar(alpha)` after a chosen complex
embedding. -/
def shiftedSquareSourceEmbeddingRatio
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) : ℂ :=
  sigma (shiftedSquareIntegralBasisElement P.basis P.x :
      rationalQuadraticAlgebra (-a)) /
    sigma (star (shiftedSquareIntegralBasisElement P.basis P.x :
      rationalQuadraticAlgebra (-a)))

/-- The target ratio `rho_gamma = bar(gamma) / gamma` after a chosen complex
embedding. -/
def shiftedSquareTargetEmbeddingRatio
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) : ℂ :=
  sigma (star (shiftedSquareIntegralBasisElement P.basis P.y :
      rationalQuadraticAlgebra (-a))) /
    sigma (shiftedSquareIntegralBasisElement P.basis P.y :
      rationalQuadraticAlgebra (-a))

/-- Mapping the exact field identity gives the literal complex-embedding
invariant with the manuscript's orientation. -/
theorem shiftedSquare_embeddingRatio_complexIdentity
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    (shiftedSquareSourceEmbeddingRatio P sigma)⁻¹ ^ 2 *
        shiftedSquareTargetEmbeddingRatio P sigma =
      sigma (star (shiftedSquareZeta a d n)) /
        sigma (shiftedSquareZeta a d n) := by
  have h := congrArg sigma (shiftedSquare_embeddingRatio_identity P)
  simpa only [shiftedSquareSourceEmbeddingRatio,
    shiftedSquareTargetEmbeddingRatio, map_mul, map_pow, map_inv₀, map_div₀]
    using h

/-- Denominator-free localization of the invariant square map.  The source
and target cubic monomials differ by relative size at most
`8 * sqrt |a| / n`, with the division cleared from the statement. -/
theorem shiftedSquare_embeddingRatio_denominatorFreeError
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : a ≠ 0)
    (hn : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ))
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    (n : ℝ) *
        ‖sigma (star (shiftedSquareIntegralBasisElement P.basis P.x :
              rationalQuadraticAlgebra (-a))) ^ 2 *
            sigma (star (shiftedSquareIntegralBasisElement P.basis P.y :
              rationalQuadraticAlgebra (-a))) -
          sigma (shiftedSquareIntegralBasisElement P.basis P.x :
              rationalQuadraticAlgebra (-a)) ^ 2 *
            sigma (shiftedSquareIntegralBasisElement P.basis P.y :
              rationalQuadraticAlgebra (-a))‖ ≤
      8 * Real.sqrt |(a : ℝ)| *
        ‖sigma (shiftedSquareIntegralBasisElement P.basis P.x :
              rationalQuadraticAlgebra (-a)) ^ 2 *
            sigma (shiftedSquareIntegralBasisElement P.basis P.y :
              rationalQuadraticAlgebra (-a))‖ := by
  let alpha : rationalQuadraticAlgebra (-a) :=
    shiftedSquareIntegralBasisElement P.basis P.x
  let gamma : rationalQuadraticAlgebra (-a) :=
    shiftedSquareIntegralBasisElement P.basis P.y
  let zeta : rationalQuadraticAlgebra (-a) := shiftedSquareZeta a d n
  let A : ℂ := sigma (star alpha) ^ 2 * sigma (star gamma)
  let B : ℂ := sigma alpha ^ 2 * sigma gamma
  let Z : ℂ := sigma zeta
  let Zbar : ℂ := sigma (star zeta)
  have hcross : A * Z = B * Zbar := by
    have h := congrArg sigma (shiftedSquare_embeddingRatio_crossIdentity P)
    simpa only [A, B, Z, Zbar, alpha, gamma, zeta, map_mul, map_pow] using h
  have hdeviation : (A - B) * Z = -(B * (Z - Zbar)) := by
    calc
      (A - B) * Z = A * Z - B * Z := by ring
      _ = B * Zbar - B * Z := by rw [hcross]
      _ = -(B * (Z - Zbar)) := by ring
  have hsqrtPos : 0 < Real.sqrt |(a : ℝ)| := by
    apply Real.sqrt_pos.2
    exact abs_pos.mpr (by exact_mod_cast ha)
  have hnPos : (0 : ℝ) < n := by nlinarith
  have hZlower : (n : ℝ) / 4 ≤ ‖Z‖ := by
    simpa only [Z, zeta, NumberField.InfinitePlace.apply] using
      (shiftedSquareZeta_infinitePlace_bounds a d n hn
        (NumberField.InfinitePlace.mk sigma)).1
  have hZpos : 0 < ‖Z‖ :=
    (div_pos hnPos (by norm_num)).trans_le hZlower
  have hrelative :
      (n : ℝ) * ‖Z - Zbar‖ ≤
        8 * Real.sqrt |(a : ℝ)| * ‖Z‖ := by
    simpa only [Z, Zbar, zeta] using
      shiftedSquareZeta_embedding_relativeError_mul_le a d n hn sigma
  have hnorm : ‖A - B‖ * ‖Z‖ = ‖B‖ * ‖Z - Zbar‖ := by
    calc
      ‖A - B‖ * ‖Z‖ = ‖(A - B) * Z‖ := by rw [norm_mul]
      _ = ‖-(B * (Z - Zbar))‖ := congrArg norm hdeviation
      _ = ‖B‖ * ‖Z - Zbar‖ := by rw [norm_neg, norm_mul]
  change (n : ℝ) * ‖A - B‖ ≤
    8 * Real.sqrt |(a : ℝ)| * ‖B‖
  refine le_of_mul_le_mul_right ?_ hZpos
  calc
    ((n : ℝ) * ‖A - B‖) * ‖Z‖ =
        (n : ℝ) * (‖A - B‖ * ‖Z‖) := by ring
    _ = (n : ℝ) * (‖B‖ * ‖Z - Zbar‖) := by rw [hnorm]
    _ = ‖B‖ * ((n : ℝ) * ‖Z - Zbar‖) := by ring
    _ ≤ ‖B‖ * (8 * Real.sqrt |(a : ℝ)| * ‖Z‖) :=
      mul_le_mul_of_nonneg_left hrelative (norm_nonneg B)
    _ = (8 * Real.sqrt |(a : ℝ)| * ‖B‖) * ‖Z‖ := by ring

/-- The exact invariant and the `zeta` estimate give the normalized quotient
error used before any choice of a finite chart. -/
theorem shiftedSquare_embeddingRatio_quotientError
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (hn : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ))
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    ‖(shiftedSquareSourceEmbeddingRatio P sigma)⁻¹ ^ 2 *
          shiftedSquareTargetEmbeddingRatio P sigma - 1‖ ≤
      (8 * Real.sqrt |(a : ℝ)|) / (n : ℝ) := by
  rw [shiftedSquare_embeddingRatio_complexIdentity P sigma]
  exact shiftedSquareZeta_embedding_star_div_sub_one_norm_le a d n hn sigma

private theorem norm_div_bounds_of_common_scale
    {x y : ℂ} {s F : ℝ}
    (hs : 0 < s) (hF : 0 < F)
    (hxLower : s / F ≤ ‖x‖) (hxUpper : ‖x‖ ≤ F * s)
    (hyLower : s / F ≤ ‖y‖) (hyUpper : ‖y‖ ≤ F * s) :
    1 / F ^ 2 ≤ ‖x / y‖ ∧ ‖x / y‖ ≤ F ^ 2 := by
  have hyPos : 0 < ‖y‖ := (div_pos hs hF).trans_le hyLower
  rw [norm_div]
  constructor
  · apply (le_div_iff₀ hyPos).2
    calc
      (1 / F ^ 2) * ‖y‖ ≤ (1 / F ^ 2) * (F * s) :=
        mul_le_mul_of_nonneg_left hyUpper (by positivity)
      _ = s / F := by field_simp
      _ ≤ ‖x‖ := hxLower
  · apply (div_le_iff₀ hyPos).2
    calc
      ‖x‖ ≤ F * s := hxUpper
      _ = F ^ 2 * (s / F) := by field_simp
      _ ≤ F ^ 2 * ‖y‖ :=
        mul_le_mul_of_nonneg_left hyLower (sq_nonneg F)

/-- The scale bounds at an embedding and at its composition with quadratic
conjugation place both invariant ratios in the explicit common annulus
`F⁻² ≤ ‖rho‖ ≤ F²`, where `F = 512 * |a|`. -/
theorem shiftedSquare_embeddingRatio_normBounds
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : a ≠ 0) (hd : 0 < d) (hw : 0 < w)
    (hn : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ))
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    let F := shiftedSquareEmbeddingScaleLoss a
    (1 / F ^ 2 ≤ ‖shiftedSquareSourceEmbeddingRatio P sigma‖ ∧
        ‖shiftedSquareSourceEmbeddingRatio P sigma‖ ≤ F ^ 2) ∧
      (1 / F ^ 2 ≤ ‖shiftedSquareTargetEmbeddingRatio P sigma‖ ∧
        ‖shiftedSquareTargetEmbeddingRatio P sigma‖ ≤ F ^ 2) := by
  let F := shiftedSquareEmbeddingScaleLoss a
  let sourceScale := Real.sqrt (shiftedSquareEAlpha P)
  let targetScale := Real.sqrt (shiftedSquareEGamma P)
  let sigmaStar : rationalQuadraticAlgebra (-a) →+* ℂ :=
    sigma.comp (starRingEnd (rationalQuadraticAlgebra (-a)))
  have hF : 0 < F := by
    dsimp only [F, shiftedSquareEmbeddingScaleLoss]
    exact mul_pos (by norm_num) (abs_pos.mpr (by exact_mod_cast ha))
  have hd₀ : (0 : ℝ) < shiftedSquareD₀ d := by
    exact_mod_cast shiftedSquareD₀_pos hd
  have hC : (0 : ℝ) < P.minkowski.C₀ := by
    exact_mod_cast P.minkowski.C₀_pos
  have hr : (0 : ℝ) < P.r := by exact_mod_cast P.r_pos
  have hell : (0 : ℝ) < P.ell := by exact_mod_cast P.ell_pos
  have hwReal : (0 : ℝ) < w := by exact_mod_cast hw
  have hSourceScale : 0 < sourceScale := by
    apply Real.sqrt_pos.2
    dsimp only [sourceScale, shiftedSquareEAlpha]
    simp only [Nat.cast_mul]
    positivity
  have hTargetScale : 0 < targetScale := by
    apply Real.sqrt_pos.2
    dsimp only [targetScale, shiftedSquareEGamma]
    simp only [Nat.cast_mul, Nat.cast_pow]
    positivity
  have hSource :=
    shiftedSquare_sourceEmbedding_scaleBounds ha hd P
      (NumberField.InfinitePlace.mk sigma)
  have hSourceStar :=
    shiftedSquare_sourceEmbedding_scaleBounds ha hd P
      (NumberField.InfinitePlace.mk sigmaStar)
  have hTarget :=
    shiftedSquare_targetEmbedding_scaleBounds ha hd hn P
      (NumberField.InfinitePlace.mk sigma)
  have hTargetStar :=
    shiftedSquare_targetEmbedding_scaleBounds ha hd hn P
      (NumberField.InfinitePlace.mk sigmaStar)
  have hSource' :
      sourceScale / F ≤
          ‖sigma (shiftedSquareIntegralBasisElement P.basis P.x :
            rationalQuadraticAlgebra (-a))‖ ∧
        ‖sigma (shiftedSquareIntegralBasisElement P.basis P.x :
            rationalQuadraticAlgebra (-a))‖ ≤ F * sourceScale := by
    simpa only [sourceScale, F, NumberField.InfinitePlace.apply] using hSource
  have hSourceStar' :
      sourceScale / F ≤
          ‖sigma (star (shiftedSquareIntegralBasisElement P.basis P.x :
            rationalQuadraticAlgebra (-a)))‖ ∧
        ‖sigma (star (shiftedSquareIntegralBasisElement P.basis P.x :
            rationalQuadraticAlgebra (-a)))‖ ≤ F * sourceScale := by
    simpa only [sourceScale, F, sigmaStar, NumberField.InfinitePlace.apply,
      RingHom.coe_comp, Function.comp_apply, starRingEnd_apply] using hSourceStar
  have hTarget' :
      targetScale / F ≤
          ‖sigma (shiftedSquareIntegralBasisElement P.basis P.y :
            rationalQuadraticAlgebra (-a))‖ ∧
        ‖sigma (shiftedSquareIntegralBasisElement P.basis P.y :
            rationalQuadraticAlgebra (-a))‖ ≤ F * targetScale := by
    simpa only [targetScale, F, NumberField.InfinitePlace.apply] using hTarget
  have hTargetStar' :
      targetScale / F ≤
          ‖sigma (star (shiftedSquareIntegralBasisElement P.basis P.y :
            rationalQuadraticAlgebra (-a)))‖ ∧
        ‖sigma (star (shiftedSquareIntegralBasisElement P.basis P.y :
            rationalQuadraticAlgebra (-a)))‖ ≤ F * targetScale := by
    simpa only [targetScale, F, sigmaStar, NumberField.InfinitePlace.apply,
      RingHom.coe_comp, Function.comp_apply, starRingEnd_apply] using hTargetStar
  have hSourceRatio := norm_div_bounds_of_common_scale
    hSourceScale hF hSource'.1 hSource'.2 hSourceStar'.1 hSourceStar'.2
  have hTargetRatio := norm_div_bounds_of_common_scale
    hTargetScale hF hTargetStar'.1 hTargetStar'.2 hTarget'.1 hTarget'.2
  simpa only [shiftedSquareSourceEmbeddingRatio,
    shiftedSquareTargetEmbeddingRatio, F] using ⟨hSourceRatio, hTargetRatio⟩

/-- After undoing the invariant `rho_alpha⁻²`, the target ratio lies close to
the square of the source ratio.  The final bound uses the annulus radius and
is ready for a subsequent finite-cell construction. -/
theorem shiftedSquare_embeddingRatio_targetChartError
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : a ≠ 0) (hd : 0 < d) (hw : 0 < w)
    (hn : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ))
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    ‖shiftedSquareTargetEmbeddingRatio P sigma -
        shiftedSquareSourceEmbeddingRatio P sigma ^ 2‖ ≤
      ((8 * Real.sqrt |(a : ℝ)|) / (n : ℝ)) *
        shiftedSquareEmbeddingScaleLoss a ^ 4 := by
  let sourceRatio := shiftedSquareSourceEmbeddingRatio P sigma
  let targetRatio := shiftedSquareTargetEmbeddingRatio P sigma
  let F := shiftedSquareEmbeddingScaleLoss a
  have hsqrtPos : 0 < Real.sqrt |(a : ℝ)| := by
    apply Real.sqrt_pos.2
    exact abs_pos.mpr (by exact_mod_cast ha)
  have hnPos : (0 : ℝ) < n := by nlinarith
  have hnorms := shiftedSquare_embeddingRatio_normBounds ha hd hw hn P sigma
  have hsourceUpper : ‖sourceRatio‖ ≤ F ^ 2 := by
    simpa only [sourceRatio, F] using hnorms.1.2
  have hsourceNormPos : 0 < ‖sourceRatio‖ := by
    have hlower : 1 / F ^ 2 ≤ ‖sourceRatio‖ := by
      simpa only [sourceRatio, F] using hnorms.1.1
    have hF : 0 < F := by
      dsimp only [F, shiftedSquareEmbeddingScaleLoss]
      exact mul_pos (by norm_num) (abs_pos.mpr (by exact_mod_cast ha))
    exact (div_pos zero_lt_one (sq_pos_of_pos hF)).trans_le hlower
  have hsourceNe : sourceRatio ≠ 0 := norm_pos_iff.mp hsourceNormPos
  have hquotient := shiftedSquare_embeddingRatio_quotientError hn P sigma
  have hrewrite :
      targetRatio - sourceRatio ^ 2 =
        sourceRatio ^ 2 * (sourceRatio⁻¹ ^ 2 * targetRatio - 1) := by
    field_simp [hsourceNe]
  have hrelative :
      ‖targetRatio - sourceRatio ^ 2‖ ≤
        ‖sourceRatio‖ ^ 2 *
          ((8 * Real.sqrt |(a : ℝ)|) / (n : ℝ)) := by
    rw [hrewrite, norm_mul, norm_pow]
    apply mul_le_mul_of_nonneg_left
    · simpa only [sourceRatio, targetRatio] using hquotient
    · positivity
  have hsourceSq : ‖sourceRatio‖ ^ 2 ≤ F ^ 4 := by
    nlinarith [norm_nonneg sourceRatio, sq_nonneg F]
  have hcoefficient :
      0 ≤ (8 * Real.sqrt |(a : ℝ)|) / (n : ℝ) := by positivity
  calc
    ‖shiftedSquareTargetEmbeddingRatio P sigma -
          shiftedSquareSourceEmbeddingRatio P sigma ^ 2‖ =
        ‖targetRatio - sourceRatio ^ 2‖ := by rfl
    _ ≤ ‖sourceRatio‖ ^ 2 *
          ((8 * Real.sqrt |(a : ℝ)|) / (n : ℝ)) := hrelative
    _ = ((8 * Real.sqrt |(a : ℝ)|) / (n : ℝ)) *
          ‖sourceRatio‖ ^ 2 := by ring
    _ ≤ ((8 * Real.sqrt |(a : ℝ)|) / (n : ℝ)) * F ^ 4 :=
      mul_le_mul_of_nonneg_left hsourceSq hcoefficient
    _ = ((8 * Real.sqrt |(a : ℝ)|) / (n : ℝ)) *
          shiftedSquareEmbeddingScaleLoss a ^ 4 := by rfl

/-- Complete pointwise localization data for one package and one complex
embedding. -/
structure ShiftedSquareEmbeddingRatioLocalizationCertificate
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) : Prop where
  source_ratio_ne_zero : shiftedSquareSourceEmbeddingRatio P sigma ≠ 0
  target_ratio_ne_zero : shiftedSquareTargetEmbeddingRatio P sigma ≠ 0
  source_ratio_norm_bounds :
    1 / shiftedSquareEmbeddingScaleLoss a ^ 2 ≤
        ‖shiftedSquareSourceEmbeddingRatio P sigma‖ ∧
      ‖shiftedSquareSourceEmbeddingRatio P sigma‖ ≤
        shiftedSquareEmbeddingScaleLoss a ^ 2
  target_ratio_norm_bounds :
    1 / shiftedSquareEmbeddingScaleLoss a ^ 2 ≤
        ‖shiftedSquareTargetEmbeddingRatio P sigma‖ ∧
      ‖shiftedSquareTargetEmbeddingRatio P sigma‖ ≤
        shiftedSquareEmbeddingScaleLoss a ^ 2
  invariant_identity :
    (shiftedSquareSourceEmbeddingRatio P sigma)⁻¹ ^ 2 *
        shiftedSquareTargetEmbeddingRatio P sigma =
      sigma (star (shiftedSquareZeta a d n)) /
        sigma (shiftedSquareZeta a d n)
  denominator_free_error :
    (n : ℝ) *
        ‖sigma (star (shiftedSquareIntegralBasisElement P.basis P.x :
              rationalQuadraticAlgebra (-a))) ^ 2 *
            sigma (star (shiftedSquareIntegralBasisElement P.basis P.y :
              rationalQuadraticAlgebra (-a))) -
          sigma (shiftedSquareIntegralBasisElement P.basis P.x :
              rationalQuadraticAlgebra (-a)) ^ 2 *
            sigma (shiftedSquareIntegralBasisElement P.basis P.y :
              rationalQuadraticAlgebra (-a))‖ ≤
      8 * Real.sqrt |(a : ℝ)| *
        ‖sigma (shiftedSquareIntegralBasisElement P.basis P.x :
              rationalQuadraticAlgebra (-a)) ^ 2 *
            sigma (shiftedSquareIntegralBasisElement P.basis P.y :
              rationalQuadraticAlgebra (-a))‖
  quotient_error :
    ‖(shiftedSquareSourceEmbeddingRatio P sigma)⁻¹ ^ 2 *
          shiftedSquareTargetEmbeddingRatio P sigma - 1‖ ≤
      (8 * Real.sqrt |(a : ℝ)|) / (n : ℝ)
  target_chart_error :
    ‖shiftedSquareTargetEmbeddingRatio P sigma -
        shiftedSquareSourceEmbeddingRatio P sigma ^ 2‖ ≤
      ((8 * Real.sqrt |(a : ℝ)|) / (n : ℝ)) *
        shiftedSquareEmbeddingScaleLoss a ^ 4

/-- Assemble the localization certificate from the canonical exact ratio,
`zeta` error, and scale bounds. -/
theorem shiftedSquare_embeddingRatio_localizationCertificate
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : a ≠ 0) (hd : 0 < d) (hw : 0 < w)
    (hn : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ))
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    ShiftedSquareEmbeddingRatioLocalizationCertificate heq P sigma := by
  have hnorms := shiftedSquare_embeddingRatio_normBounds ha hd hw hn P sigma
  have hF : 0 < shiftedSquareEmbeddingScaleLoss a := by
    dsimp only [shiftedSquareEmbeddingScaleLoss]
    exact mul_pos (by norm_num) (abs_pos.mpr (by exact_mod_cast ha))
  have hsourceNormPos : 0 < ‖shiftedSquareSourceEmbeddingRatio P sigma‖ :=
    (div_pos zero_lt_one (sq_pos_of_pos hF)).trans_le hnorms.1.1
  have htargetNormPos : 0 < ‖shiftedSquareTargetEmbeddingRatio P sigma‖ :=
    (div_pos zero_lt_one (sq_pos_of_pos hF)).trans_le hnorms.2.1
  exact {
    source_ratio_ne_zero := norm_pos_iff.mp hsourceNormPos
    target_ratio_ne_zero := norm_pos_iff.mp htargetNormPos
    source_ratio_norm_bounds := hnorms.1
    target_ratio_norm_bounds := hnorms.2
    invariant_identity := shiftedSquare_embeddingRatio_complexIdentity P sigma
    denominator_free_error :=
      shiftedSquare_embeddingRatio_denominatorFreeError ha hn P sigma
    quotient_error := shiftedSquare_embeddingRatio_quotientError hn P sigma
    target_chart_error :=
      shiftedSquare_embeddingRatio_targetChartError ha hd hw hn P sigma }

/-- Every actual point of the corrected mixed-parameter large-analytic route
has one scaled coordinate package and, for every complex embedding, the
localization certificate attached to that exact same package. -/
theorem exists_main3LargeAnalytic_embeddingRatioLocalization
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N d w n : ℕ}
    (htheta : 3 ≤ theta) (hY : 8 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (hp : (d, w, n) ∈
      squarefreeShiftedSquareBlock (shiftedSquareA h v) D Y N) :
    let heq := main3LargeAnalytic_squarefreeBlock_equation hp
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    ∃ P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq,
      Main3LargeAnalyticScaledCoordinateCertificate
          (D := D) (Y := Y) (N := N) heq P ∧
        ∀ sigma : rationalQuadraticAlgebra (-(shiftedSquareA h v)) →+* ℂ,
          ShiftedSquareEmbeddingRatioLocalizationCertificate heq P sigma := by
  let heq := main3LargeAnalytic_squarefreeBlock_equation hp
  let fieldFact : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  change ∃ P : @ShiftedSquareSimultaneousNormalizedCoordinatePackage
      (shiftedSquareA h v) d w n fieldFact heq,
    @Main3LargeAnalyticScaledCoordinateCertificate
        (shiftedSquareA h v) D Y N d w n fieldFact heq P ∧
      ∀ sigma : rationalQuadraticAlgebra (-(shiftedSquareA h v)) →+* ℂ,
        @ShiftedSquareEmbeddingRatioLocalizationCertificate
          (shiftedSquareA h v) d w n fieldFact heq P sigma
  have hscaledExists :=
    exists_main3LargeAnalytic_scaledCoordinatePackage htheta hY hi hp
  change ∃ P : @ShiftedSquareSimultaneousNormalizedCoordinatePackage
      (shiftedSquareA h v) d w n fieldFact heq,
    @Main3LargeAnalyticScaledCoordinateCertificate
      (shiftedSquareA h v) D Y N d w n fieldFact heq P at hscaledExists
  obtain ⟨P, hscaled⟩ := hscaledExists
  refine ⟨P, hscaled, fun sigma => ?_⟩
  exact @shiftedSquare_embeddingRatio_localizationCertificate
    (shiftedSquareA h v) d w n fieldFact heq hscaled.shift_ne_zero
      hscaled.base.source_pos hscaled.base.target_pos
      hscaled.base.shift_dominance P sigma

end

end PellPaper
