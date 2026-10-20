import Pell.QuadraticOrderPellRealEmbedding
import Pell.Main3ShiftedSquareEmbeddingRatioLocalization
import Mathlib.Tactic

/-!
# Explicit archimedean place geometry for shifted-square ratios

This isolated candidate constructs the two concrete embeddings of
`rationalQuadraticAlgebra (-a)` selected by the sign of `a`.  If `a < 0`,
the positive real embedding is composed with `ℝ → ℂ`; all of its values, and
hence the two normalized embedding ratios, are real.  If `0 < a`, the
distinguished root is sent to `I * sqrt a`; this embedding intertwines the
quadratic involution with complex conjugation, so both normalized ratios have
norm one.

The ratio statements retain the literal nonzero denominator facts.  No
finite chart, cell count, logarithm, determinant, or asymptotic estimate is
asserted here.
-/

namespace PellPaper

noncomputable section

/-! ## The real branch -/

/-- For `a < 0`, the positive real embedding of the real quadratic algebra
`ℚ(sqrt(-a))`, followed by the standard inclusion `ℝ → ℂ`. -/
noncomputable def shiftedSquarePositiveRealPlaceEmbedding
    (a : ℤ) (ha : a < 0) :
    rationalQuadraticAlgebra (-a) →+* ℂ :=
  (algebraMap ℝ ℂ).comp
    (rationalQuadraticAlgebraRealEmbedding (-a) (by omega)).toRingHom

/-- The real-place embedding is literally the complexification of the
project's chosen positive real embedding. -/
@[simp]
theorem shiftedSquarePositiveRealPlaceEmbedding_apply
    (a : ℤ) (ha : a < 0)
    (z : rationalQuadraticAlgebra (-a)) :
    shiftedSquarePositiveRealPlaceEmbedding a ha z =
      (rationalQuadraticAlgebraRealEmbedding (-a) (by omega) z : ℂ) :=
  rfl

/-- The distinguished quadratic generator goes to the positive square root
at the selected real place. -/
@[simp]
theorem shiftedSquarePositiveRealPlaceEmbedding_omega
    (a : ℤ) (ha : a < 0) :
    shiftedSquarePositiveRealPlaceEmbedding a ha
        QuadraticAlgebra.omega =
      (Real.sqrt ((-a : ℤ) : ℝ) : ℂ) := by
  change ((rationalQuadraticAlgebraRealEmbedding (-a) (by omega)
    QuadraticAlgebra.omega : ℝ) : ℂ) = _
  rw [rationalQuadraticAlgebraRealEmbedding_omega]

/-- Complex conjugation fixes every value of the selected real embedding.
Notice that this does not claim that quadratic conjugation fixes the source
element: it only records that this particular place is real-valued. -/
@[simp]
theorem shiftedSquarePositiveRealPlaceEmbedding_conj
    (a : ℤ) (ha : a < 0)
    (z : rationalQuadraticAlgebra (-a)) :
    star (shiftedSquarePositiveRealPlaceEmbedding a ha z) =
      shiftedSquarePositiveRealPlaceEmbedding a ha z := by
  rw [shiftedSquarePositiveRealPlaceEmbedding_apply]
  simp

/-- Quadratic conjugation sends the distinguished generator to the negative
root under the selected positive real place. -/
@[simp]
theorem shiftedSquarePositiveRealPlaceEmbedding_star_omega
    (a : ℤ) (ha : a < 0) :
    shiftedSquarePositiveRealPlaceEmbedding a ha
        (star (QuadraticAlgebra.omega :
          rationalQuadraticAlgebra (-a))) =
      -(Real.sqrt ((-a : ℤ) : ℝ) : ℂ) := by
  have homega : star (QuadraticAlgebra.omega :
      rationalQuadraticAlgebra (-a)) = -QuadraticAlgebra.omega := by
    apply QuadraticAlgebra.ext <;> norm_num
  rw [homega, map_neg, shiftedSquarePositiveRealPlaceEmbedding_omega]

/-! ## The imaginary branch -/

/-- For `0 < a`, the explicit complex algebra homomorphism from
`ℚ(sqrt(-a))` which sends the distinguished root to `I * sqrt a`. -/
noncomputable def shiftedSquareImaginaryPlaceAlgHom
    (a : ℤ) (ha : 0 < a) :
    rationalQuadraticAlgebra (-a) →ₐ[ℚ] ℂ :=
  QuadraticAlgebra.lift
    ⟨Complex.I * (Real.sqrt (a : ℝ) : ℂ), by
      rw [zero_smul, add_zero]
      simp only [Algebra.smul_def, mul_one]
      have hs : Real.sqrt (a : ℝ) * Real.sqrt (a : ℝ) = (a : ℝ) :=
        Real.mul_self_sqrt (by exact_mod_cast (le_of_lt ha))
      apply Complex.ext
      · simp [hs]
      · simp⟩

/-- The ring embedding underlying the explicit imaginary-place algebra
homomorphism.  This is the form consumed by `NumberField.InfinitePlace` and
the shifted-square ratio API. -/
noncomputable def shiftedSquareImaginaryPlaceEmbedding
    (a : ℤ) (ha : 0 < a) :
    rationalQuadraticAlgebra (-a) →+* ℂ :=
  (shiftedSquareImaginaryPlaceAlgHom a ha).toRingHom

/-- The distinguished generator has the requested positive-imaginary image.
-/
@[simp]
theorem shiftedSquareImaginaryPlaceEmbedding_omega
    (a : ℤ) (ha : 0 < a) :
    shiftedSquareImaginaryPlaceEmbedding a ha
        QuadraticAlgebra.omega =
      Complex.I * (Real.sqrt (a : ℝ) : ℂ) := by
  change (0 : ℚ) • (1 : ℂ) + (1 : ℚ) •
      (Complex.I * (Real.sqrt (a : ℝ) : ℂ)) = _
  simp

/-- At the explicit imaginary place, quadratic conjugation is exactly
complex conjugation. -/
theorem shiftedSquareImaginaryPlaceEmbedding_star
    (a : ℤ) (ha : 0 < a)
    (z : rationalQuadraticAlgebra (-a)) :
    shiftedSquareImaginaryPlaceEmbedding a ha (star z) =
      star (shiftedSquareImaginaryPlaceEmbedding a ha z) := by
  rcases z with ⟨x, y⟩
  change ((x + 0 * y : ℚ) • (1 : ℂ) + (-y : ℚ) •
      (Complex.I * (Real.sqrt (a : ℝ) : ℂ))) =
    star ((x : ℚ) • (1 : ℂ) + (y : ℚ) •
      (Complex.I * (Real.sqrt (a : ℝ) : ℂ)))
  apply Complex.ext <;> simp

/-- The star-compatibility theorem specializes on the distinguished root to
the negative imaginary root. -/
@[simp]
theorem shiftedSquareImaginaryPlaceEmbedding_star_omega
    (a : ℤ) (ha : 0 < a) :
    shiftedSquareImaginaryPlaceEmbedding a ha
        (star (QuadraticAlgebra.omega :
          rationalQuadraticAlgebra (-a))) =
      -(Complex.I * (Real.sqrt (a : ℝ) : ℂ)) := by
  rw [shiftedSquareImaginaryPlaceEmbedding_star,
    shiftedSquareImaginaryPlaceEmbedding_omega]
  simp

/-! ## Denominators and ratio geometry -/

local instance shiftedSquareExplicitPlaceGeometry_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- Under the project's no-rational-root hypothesis, the selected real-place
homomorphism is an actual embedding. -/
theorem shiftedSquarePositiveRealPlaceEmbedding_injective
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : a < 0) :
    Function.Injective (shiftedSquarePositiveRealPlaceEmbedding a ha) :=
  (shiftedSquarePositiveRealPlaceEmbedding a ha).injective

/-- Under the project's no-rational-root hypothesis, the selected
imaginary-place homomorphism is an actual embedding. -/
theorem shiftedSquareImaginaryPlaceEmbedding_injective
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : 0 < a) :
    Function.Injective (shiftedSquareImaginaryPlaceEmbedding a ha) :=
  (shiftedSquareImaginaryPlaceEmbedding a ha).injective

/-- The primitive source element in a simultaneous normalized package is
nonzero. -/
theorem shiftedSquare_sourcePrimitiveElement_ne_zero
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    (shiftedSquareIntegralBasisElement P.basis P.x :
      rationalQuadraticAlgebra (-a)) ≠ 0 := by
  intro hzero
  have hxzero : shiftedSquareIntegralBasisElement P.basis P.x = 0 := by
    apply Subtype.ext
    exact hzero
  apply P.minkowski.mu_ne_zero
  rw [P.mu_coordinates, hxzero, smul_zero]

/-- The primitive target element in a simultaneous normalized package is
nonzero. -/
theorem shiftedSquare_targetPrimitiveElement_ne_zero
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    (shiftedSquareIntegralBasisElement P.basis P.y :
      rationalQuadraticAlgebra (-a)) ≠ 0 := by
  intro hzero
  have hyzero : shiftedSquareIntegralBasisElement P.basis P.y = 0 := by
    apply Subtype.ext
    exact hzero
  apply P.nu_ne_zero
  rw [P.nu_coordinates, hyzero, smul_zero]

/-- The literal denominator of the source ratio is nonzero at every complex
embedding. -/
theorem shiftedSquare_sourceEmbeddingRatio_denominator_ne_zero
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    sigma (star (shiftedSquareIntegralBasisElement P.basis P.x :
      rationalQuadraticAlgebra (-a))) ≠ 0 := by
  intro hzero
  have hpre : star (shiftedSquareIntegralBasisElement P.basis P.x :
      rationalQuadraticAlgebra (-a)) = 0 := by
    apply sigma.injective
    simpa using hzero
  exact (star_ne_zero.mpr (shiftedSquare_sourcePrimitiveElement_ne_zero P))
    hpre

/-- The literal denominator of the target ratio is nonzero at every complex
embedding. -/
theorem shiftedSquare_targetEmbeddingRatio_denominator_ne_zero
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    sigma (shiftedSquareIntegralBasisElement P.basis P.y :
      rationalQuadraticAlgebra (-a)) ≠ 0 := by
  intro hzero
  apply shiftedSquare_targetPrimitiveElement_ne_zero P
  apply sigma.injective
  simpa using hzero

/-- The source ratio at the selected real place is a nonzero real number.
This is the non-axis fact needed before choosing its sign and dyadic range. -/
theorem shiftedSquare_positiveRealPlace_sourceRatio_re_ne_zero
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : a < 0)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    (shiftedSquareSourceEmbeddingRatio P
      (shiftedSquarePositiveRealPlaceEmbedding a ha)).re ≠ 0 := by
  let alpha : rationalQuadraticAlgebra (-a) :=
    shiftedSquareIntegralBasisElement P.basis P.x
  let tau := rationalQuadraticAlgebraRealEmbedding (-a) (by omega)
  have halpha : alpha ≠ 0 := by
    simpa only [alpha] using shiftedSquare_sourcePrimitiveElement_ne_zero P
  have hnum : tau alpha ≠ 0 := by
    intro hzero
    apply halpha
    apply tau.injective
    simpa using hzero
  have hden : tau (star alpha) ≠ 0 := by
    intro hzero
    apply star_ne_zero.mpr halpha
    apply tau.injective
    simpa using hzero
  simpa only [shiftedSquareSourceEmbeddingRatio,
    shiftedSquarePositiveRealPlaceEmbedding_apply,
    ← Complex.ofReal_div, Complex.ofReal_re, alpha, tau] using
      div_ne_zero hnum hden

/-- The target ratio at the selected real place is strictly positive.  The
sign comes from the positive signed norm
`w * (C₀ / ell)^2` of the primitive target element, not merely from the fact
that the ratio is real. -/
theorem shiftedSquare_positiveRealPlace_targetRatio_re_pos
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : a < 0)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    0 < (shiftedSquareTargetEmbeddingRatio P
      (shiftedSquarePositiveRealPlaceEmbedding a ha)).re := by
  let gammaInt := shiftedSquareIntegralBasisElement P.basis P.y
  let gamma : rationalQuadraticAlgebra (-a) := gammaInt
  let M : ℕ := w * (P.minkowski.C₀ / P.ell) ^ 2
  let tau := rationalQuadraticAlgebraRealEmbedding (-a) (by omega)
  have hgamma : gamma ≠ 0 := by
    simpa only [gamma, gammaInt] using
      shiftedSquare_targetPrimitiveElement_ne_zero P
  have hgammaInt : gammaInt ≠ 0 := by
    intro hzero
    apply hgamma
    simp [gamma, hzero]
  have hnormZ : Algebra.norm ℤ gammaInt = (M : ℤ) := by
    calc
      Algebra.norm ℤ gammaInt =
          shiftedSquareIntegralBasisNormEval P.basis P.y :=
        (shiftedSquareIntegralBasisNormEval_eq_algebraNorm
          P.basis P.y).symm
      _ = shiftedSquareExplicitNormFormEval P.t P.c P.y :=
        shiftedSquareIntegralBasisNormEval_eq_explicit P.basis P.omega
          P.t P.c P.basis_zero P.basis_one P.omega_sq P.y
      _ = (M : ℤ) := by
        simpa only [M] using P.normalized_target_norm
  have hMne : M ≠ 0 := by
    intro hzero
    have hnormNe : Algebra.norm ℤ gammaInt ≠ 0 :=
      Algebra.norm_ne_zero_iff.mpr hgammaInt
    apply hnormNe
    rw [hnormZ, hzero]
    norm_num
  have hMpos : 0 < M := Nat.pos_of_ne_zero hMne
  have hnormCast :
      ((Algebra.norm ℤ gammaInt : ℤ) : ℚ) =
        Algebra.norm ℚ gamma := by
    rw [← Algebra.intNorm_eq_norm ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)))]
    exact Algebra.algebraMap_intNorm
      (A := ℤ) (K := ℚ) (L := rationalQuadraticAlgebra (-a))
      (B := NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)))
      gammaInt
  have hnormQ : Algebra.norm ℚ gamma = (M : ℚ) := by
    rw [← hnormCast, hnormZ]
    norm_num
  have hquadraticNorm : QuadraticAlgebra.norm gamma = (M : ℚ) := by
    calc
      QuadraticAlgebra.norm gamma = Algebra.norm ℚ gamma := by
        symm
        calc
          Algebra.norm ℚ gamma =
              gamma.re * gamma.re - ((-a : ℤ) : ℚ) *
                gamma.im * gamma.im :=
            rationalQuadraticAlgebra_norm_apply (-a) gamma
          _ = QuadraticAlgebra.norm gamma := by
            rw [QuadraticAlgebra.norm_def]
            norm_num
      _ = (M : ℚ) := hnormQ
  have hproduct : tau gamma * tau (star gamma) = (M : ℝ) := by
    calc
      tau gamma * tau (star gamma) = tau (gamma * star gamma) := by
        rw [map_mul]
      _ = tau (algebraMap ℚ (rationalQuadraticAlgebra (-a))
          (QuadraticAlgebra.norm gamma)) := by
        exact congrArg tau
          (QuadraticAlgebra.algebraMap_norm_eq_mul_star gamma).symm
      _ = ((QuadraticAlgebra.norm gamma : ℚ) : ℝ) := by simp
      _ = (M : ℝ) := by rw [hquadraticNorm]; norm_num
  have hgammaReal : tau gamma ≠ 0 := by
    intro hzero
    apply hgamma
    apply tau.injective
    simpa using hzero
  have hratioPos : 0 < tau (star gamma) / tau gamma := by
    have hsq : 0 < tau gamma ^ 2 := sq_pos_of_ne_zero hgammaReal
    have hrearrange :
        tau (star gamma) / tau gamma =
          (tau gamma * tau (star gamma)) / tau gamma ^ 2 := by
      field_simp [hgammaReal]
    rw [hrearrange, hproduct]
    exact div_pos (by exact_mod_cast hMpos) hsq
  simpa only [shiftedSquareTargetEmbeddingRatio,
    shiftedSquarePositiveRealPlaceEmbedding_apply,
    ← Complex.ofReal_div, Complex.ofReal_re, gamma, gammaInt, tau] using
      hratioPos

/-- Exact real-place geometry of the two normalized ratios, including their
actual denominator witnesses. -/
structure ShiftedSquareRealPlaceRatioGeometry
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a)
    (ha : a < 0)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) : Prop where
  source_denominator_ne_zero :
    shiftedSquarePositiveRealPlaceEmbedding a ha
      (star (shiftedSquareIntegralBasisElement P.basis P.x :
        rationalQuadraticAlgebra (-a))) ≠ 0
  target_denominator_ne_zero :
    shiftedSquarePositiveRealPlaceEmbedding a ha
      (shiftedSquareIntegralBasisElement P.basis P.y :
        rationalQuadraticAlgebra (-a)) ≠ 0
  source_ratio_im_eq_zero :
    (shiftedSquareSourceEmbeddingRatio P
      (shiftedSquarePositiveRealPlaceEmbedding a ha)).im = 0
  target_ratio_im_eq_zero :
    (shiftedSquareTargetEmbeddingRatio P
      (shiftedSquarePositiveRealPlaceEmbedding a ha)).im = 0
  source_ratio_re_ne_zero :
    (shiftedSquareSourceEmbeddingRatio P
      (shiftedSquarePositiveRealPlaceEmbedding a ha)).re ≠ 0
  target_ratio_re_pos :
    0 < (shiftedSquareTargetEmbeddingRatio P
      (shiftedSquarePositiveRealPlaceEmbedding a ha)).re

/-- At the selected positive real place, both normalized embedding ratios are
real and both displayed denominators are nonzero. -/
theorem shiftedSquare_positiveRealPlace_ratioGeometry
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : a < 0)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    ShiftedSquareRealPlaceRatioGeometry heq ha P := by
  refine {
    source_denominator_ne_zero :=
      shiftedSquare_sourceEmbeddingRatio_denominator_ne_zero P _
    target_denominator_ne_zero :=
      shiftedSquare_targetEmbeddingRatio_denominator_ne_zero P _
    source_ratio_im_eq_zero := ?_
    target_ratio_im_eq_zero := ?_
    source_ratio_re_ne_zero :=
      shiftedSquare_positiveRealPlace_sourceRatio_re_ne_zero ha P
    target_ratio_re_pos :=
      shiftedSquare_positiveRealPlace_targetRatio_re_pos ha P }
  · simp only [shiftedSquareSourceEmbeddingRatio,
      shiftedSquarePositiveRealPlaceEmbedding_apply,
      ← Complex.ofReal_div, Complex.ofReal_im]
  · simp only [shiftedSquareTargetEmbeddingRatio,
      shiftedSquarePositiveRealPlaceEmbedding_apply,
      ← Complex.ofReal_div, Complex.ofReal_im]

/-- Exact imaginary-place geometry of the two normalized ratios, including
their actual denominator witnesses. -/
structure ShiftedSquareImaginaryPlaceRatioGeometry
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a)
    (ha : 0 < a)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) : Prop where
  source_denominator_ne_zero :
    shiftedSquareImaginaryPlaceEmbedding a ha
      (star (shiftedSquareIntegralBasisElement P.basis P.x :
        rationalQuadraticAlgebra (-a))) ≠ 0
  target_denominator_ne_zero :
    shiftedSquareImaginaryPlaceEmbedding a ha
      (shiftedSquareIntegralBasisElement P.basis P.y :
        rationalQuadraticAlgebra (-a)) ≠ 0
  source_ratio_norm_eq_one :
    ‖shiftedSquareSourceEmbeddingRatio P
      (shiftedSquareImaginaryPlaceEmbedding a ha)‖ = 1
  target_ratio_norm_eq_one :
    ‖shiftedSquareTargetEmbeddingRatio P
      (shiftedSquareImaginaryPlaceEmbedding a ha)‖ = 1

/-- At the explicit imaginary place, star compatibility makes both normalized
embedding ratios lie on the unit circle, and both displayed denominators are
nonzero. -/
theorem shiftedSquare_imaginaryPlace_ratioGeometry
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : 0 < a)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    ShiftedSquareImaginaryPlaceRatioGeometry heq ha P := by
  have hsourceDen :=
    shiftedSquare_sourceEmbeddingRatio_denominator_ne_zero P
      (shiftedSquareImaginaryPlaceEmbedding a ha)
  have htargetDen :=
    shiftedSquare_targetEmbeddingRatio_denominator_ne_zero P
      (shiftedSquareImaginaryPlaceEmbedding a ha)
  refine {
    source_denominator_ne_zero := hsourceDen
    target_denominator_ne_zero := htargetDen
    source_ratio_norm_eq_one := ?_
    target_ratio_norm_eq_one := ?_ }
  · rw [shiftedSquareSourceEmbeddingRatio, norm_div,
      shiftedSquareImaginaryPlaceEmbedding_star, norm_star]
    have hsourceNum : shiftedSquareImaginaryPlaceEmbedding a ha
        (shiftedSquareIntegralBasisElement P.basis P.x :
          rationalQuadraticAlgebra (-a)) ≠ 0 := by
      intro hzero
      apply shiftedSquare_sourcePrimitiveElement_ne_zero P
      apply (shiftedSquareImaginaryPlaceEmbedding a ha).injective
      simpa using hzero
    exact div_self (norm_ne_zero_iff.mpr hsourceNum)
  · rw [shiftedSquareTargetEmbeddingRatio, norm_div,
      shiftedSquareImaginaryPlaceEmbedding_star, norm_star]
    exact div_self (norm_ne_zero_iff.mpr htargetDen)

end

end PellPaper
