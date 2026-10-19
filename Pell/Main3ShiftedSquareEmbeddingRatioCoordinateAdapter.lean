import Pell.Main3EmbeddingBasisRatioFactorization
import Pell.Main3LargeAnalyticCellCoordinatePointImage
import Pell.Main3ShiftedSquareCoordinateContainer
import Pell.ShiftedSquareExplicitPlaceGeometry
import Pell.ComplexUnitCircleSquareMapCellPairCover
import Mathlib.Tactic

/-!
# Fixed-basis coordinate points and shifted-square embedding ratios

The determinant route evaluates integral homogeneous coordinate points in a
fixed basis, while the shifted-square localization route defines its ratios
directly from the corresponding field elements.  This module proves that the
two descriptions are literally identical.

The basis images are chosen in the column-change convention

`omega = sigma(B.omega)` and `omegaBar = sigma(star B.omega)`.

For the no-reversal point `((x0,x1),(y0,y1))`, this makes the source ratio
`alpha/starAlpha` and the target ratio `starGamma/gamma`, exactly as in the
reflected bidegree-`(1,B)` evaluation matrix.  No determinant estimate or
point count is asserted.
-/

namespace PellPaper

noncomputable section

/-- The literal determinant-engine point attached to one normalized package,
factored through its public complete coordinate code. -/
def main3ShiftedSquarePackagePoint
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    GeneralBidegreeFormPoint :=
  shiftedSquareCoordinateCodePoint (shiftedSquareCoordinateCodeOfPackage P)

/-- The package point has the literal no-reversal coordinate order used by
the general bidegree determinant engine. -/
theorem main3ShiftedSquarePackagePoint_eq
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    main3ShiftedSquarePackagePoint P =
      ((P.x 0, P.x 1), (P.y 0, P.y 1)) := by
  rfl

/-- Image of the fixed integral-basis generator at a chosen complex
embedding. -/
def main3ShiftedSquareEmbeddingOmega
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) : ℂ :=
  sigma (B.omega : rationalQuadraticAlgebra (-a))

/-- Image of the quadratic conjugate of the fixed basis generator. -/
def main3ShiftedSquareEmbeddingOmegaBar
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) : ℂ :=
  sigma (star (B.omega : rationalQuadraticAlgebra (-a)))

/-- These two basis images are definitionally the parameters of the
canonical fixed-basis column-change matrix. -/
theorem main3ShiftedSquareEmbeddingBasisColumnChangeMatrix_eq
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (degree : ℕ) (B : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    main3ShiftedSquareEmbeddingBasisColumnChangeMatrix degree B sigma =
      main3EmbeddingBasisColumnChangeMatrix degree
        (main3ShiftedSquareEmbeddingOmega B sigma)
        (main3ShiftedSquareEmbeddingOmegaBar B sigma) := by
  rfl

/-- Mapping a primitive integral-basis element evaluates its displayed
coordinates at `sigma(P.omega)`. -/
theorem shiftedSquare_embedding_integralBasisElement_eq_coordinateLinear
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (u : Fin 2 → ℤ) :
    sigma (shiftedSquareIntegralBasisElement P.basis u :
        rationalQuadraticAlgebra (-a)) =
      (u 0 : ℂ) +
        sigma (P.omega : rationalQuadraticAlgebra (-a)) * (u 1 : ℂ) := by
  have hfield :
      (shiftedSquareIntegralBasisElement P.basis u :
          rationalQuadraticAlgebra (-a)) =
        (u 0 : rationalQuadraticAlgebra (-a)) +
          (u 1 : rationalQuadraticAlgebra (-a)) * P.omega := by
    exact congrArg Subtype.val
      (shiftedSquareIntegralBasisElement_eq_explicit
        P.basis P.omega P.basis_zero P.basis_one u)
  rw [hfield]
  simp only [map_add, map_mul, map_intCast]
  ring

/-- Mapping the conjugate primitive element evaluates the same coordinates
at `sigma(star P.omega)`. -/
theorem shiftedSquare_embedding_star_integralBasisElement_eq_coordinateLinear
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (u : Fin 2 → ℤ) :
    sigma (star (shiftedSquareIntegralBasisElement P.basis u :
        rationalQuadraticAlgebra (-a))) =
      (u 0 : ℂ) +
        sigma (star (P.omega : rationalQuadraticAlgebra (-a))) *
          (u 1 : ℂ) := by
  have hfield :
      (shiftedSquareIntegralBasisElement P.basis u :
          rationalQuadraticAlgebra (-a)) =
        (u 0 : rationalQuadraticAlgebra (-a)) +
          (u 1 : rationalQuadraticAlgebra (-a)) * P.omega := by
    exact congrArg Subtype.val
      (shiftedSquareIntegralBasisElement_eq_explicit
        P.basis P.omega P.basis_zero P.basis_one u)
  rw [hfield]
  simp only [star_add, star_mul, star_intCast, map_add, map_mul, map_intCast]

/-- The displayed source numerator of the package point is the embedded
primitive source element. -/
theorem main3ShiftedSquarePackagePoint_sourceNumerator_eq
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ShiftedSquareFixedExplicitIntegralBasisData a)
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (homega : P.omega = B.omega)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    ((main3ShiftedSquarePackagePoint P).1.1 : ℂ) +
        main3ShiftedSquareEmbeddingOmega B sigma *
          ((main3ShiftedSquarePackagePoint P).1.2 : ℂ) =
      sigma (shiftedSquareIntegralBasisElement P.basis P.x :
        rationalQuadraticAlgebra (-a)) := by
  change (P.x 0 : ℂ) +
      sigma (B.omega : rationalQuadraticAlgebra (-a)) * (P.x 1 : ℂ) = _
  rw [← homega]
  exact (shiftedSquare_embedding_integralBasisElement_eq_coordinateLinear
    P sigma P.x).symm

/-- The displayed source denominator is the embedded conjugate primitive
source element. -/
theorem main3ShiftedSquarePackagePoint_sourceDenominator_eq
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ShiftedSquareFixedExplicitIntegralBasisData a)
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (homega : P.omega = B.omega)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    ((main3ShiftedSquarePackagePoint P).1.1 : ℂ) +
        main3ShiftedSquareEmbeddingOmegaBar B sigma *
          ((main3ShiftedSquarePackagePoint P).1.2 : ℂ) =
      sigma (star (shiftedSquareIntegralBasisElement P.basis P.x :
        rationalQuadraticAlgebra (-a))) := by
  change (P.x 0 : ℂ) +
      sigma (star (B.omega : rationalQuadraticAlgebra (-a))) *
        (P.x 1 : ℂ) = _
  rw [← homega]
  exact
    (shiftedSquare_embedding_star_integralBasisElement_eq_coordinateLinear
      P sigma P.x).symm

/-- The displayed target numerator is the embedded conjugate primitive
target element. -/
theorem main3ShiftedSquarePackagePoint_targetNumerator_eq
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ShiftedSquareFixedExplicitIntegralBasisData a)
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (homega : P.omega = B.omega)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    ((main3ShiftedSquarePackagePoint P).2.1 : ℂ) +
        main3ShiftedSquareEmbeddingOmegaBar B sigma *
          ((main3ShiftedSquarePackagePoint P).2.2 : ℂ) =
      sigma (star (shiftedSquareIntegralBasisElement P.basis P.y :
        rationalQuadraticAlgebra (-a))) := by
  change (P.y 0 : ℂ) +
      sigma (star (B.omega : rationalQuadraticAlgebra (-a))) *
        (P.y 1 : ℂ) = _
  rw [← homega]
  exact
    (shiftedSquare_embedding_star_integralBasisElement_eq_coordinateLinear
      P sigma P.y).symm

/-- The displayed target denominator is the embedded primitive target
element. -/
theorem main3ShiftedSquarePackagePoint_targetDenominator_eq
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ShiftedSquareFixedExplicitIntegralBasisData a)
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (homega : P.omega = B.omega)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    ((main3ShiftedSquarePackagePoint P).2.1 : ℂ) +
        main3ShiftedSquareEmbeddingOmega B sigma *
          ((main3ShiftedSquarePackagePoint P).2.2 : ℂ) =
      sigma (shiftedSquareIntegralBasisElement P.basis P.y :
        rationalQuadraticAlgebra (-a)) := by
  change (P.y 0 : ℂ) +
      sigma (B.omega : rationalQuadraticAlgebra (-a)) * (P.y 1 : ℂ) = _
  rw [← homega]
  exact (shiftedSquare_embedding_integralBasisElement_eq_coordinateLinear
    P sigma P.y).symm

/-- Exact source-ratio adapter in the reflected embedding-basis orientation
`alpha/starAlpha`. -/
theorem main3ShiftedSquarePackagePoint_sourceRatio_eq
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ShiftedSquareFixedExplicitIntegralBasisData a)
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (homega : P.omega = B.omega)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    main3EmbeddingSourceRatio
        (main3ShiftedSquareEmbeddingOmega B sigma)
        (main3ShiftedSquareEmbeddingOmegaBar B sigma)
        (main3ShiftedSquarePackagePoint P) =
      shiftedSquareSourceEmbeddingRatio P sigma := by
  rw [main3EmbeddingSourceRatio, shiftedSquareSourceEmbeddingRatio,
    main3ShiftedSquarePackagePoint_sourceNumerator_eq B P homega sigma,
    main3ShiftedSquarePackagePoint_sourceDenominator_eq B P homega sigma]

/-- Exact target-ratio adapter in the manuscript orientation
`starGamma/gamma`. -/
theorem main3ShiftedSquarePackagePoint_targetRatio_eq
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ShiftedSquareFixedExplicitIntegralBasisData a)
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (homega : P.omega = B.omega)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    main3EmbeddingTargetRatio
        (main3ShiftedSquareEmbeddingOmega B sigma)
        (main3ShiftedSquareEmbeddingOmegaBar B sigma)
        (main3ShiftedSquarePackagePoint P) =
      shiftedSquareTargetEmbeddingRatio P sigma := by
  rw [main3EmbeddingTargetRatio, shiftedSquareTargetEmbeddingRatio,
    main3ShiftedSquarePackagePoint_targetNumerator_eq B P homega sigma,
    main3ShiftedSquarePackagePoint_targetDenominator_eq B P homega sigma]

/-- Both displayed denominators required by the radial/ratio factorization
are nonzero for the package point at every complex embedding. -/
theorem main3ShiftedSquarePackagePoint_denominators_ne_zero
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ShiftedSquareFixedExplicitIntegralBasisData a)
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (homega : P.omega = B.omega)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    (((main3ShiftedSquarePackagePoint P).1.1 : ℂ) +
        main3ShiftedSquareEmbeddingOmegaBar B sigma *
          ((main3ShiftedSquarePackagePoint P).1.2 : ℂ) ≠ 0) ∧
      (((main3ShiftedSquarePackagePoint P).2.1 : ℂ) +
        main3ShiftedSquareEmbeddingOmega B sigma *
          ((main3ShiftedSquarePackagePoint P).2.2 : ℂ) ≠ 0) := by
  constructor
  · rw [main3ShiftedSquarePackagePoint_sourceDenominator_eq B P homega sigma]
    exact shiftedSquare_sourceEmbeddingRatio_denominator_ne_zero P sigma
  · rw [main3ShiftedSquarePackagePoint_targetDenominator_eq B P homega sigma]
    exact shiftedSquare_targetEmbeddingRatio_denominator_ne_zero P sigma

/-- The complete pair of determinant-engine ratios is exactly the pair used
by shifted-square localization. -/
theorem main3ShiftedSquarePackagePoint_ratioPair_eq
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ShiftedSquareFixedExplicitIntegralBasisData a)
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (homega : P.omega = B.omega)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    (main3EmbeddingSourceRatio
          (main3ShiftedSquareEmbeddingOmega B sigma)
          (main3ShiftedSquareEmbeddingOmegaBar B sigma)
          (main3ShiftedSquarePackagePoint P),
        main3EmbeddingTargetRatio
          (main3ShiftedSquareEmbeddingOmega B sigma)
          (main3ShiftedSquareEmbeddingOmegaBar B sigma)
          (main3ShiftedSquarePackagePoint P)) =
      (shiftedSquareSourceEmbeddingRatio P sigma,
        shiftedSquareTargetEmbeddingRatio P sigma) := by
  rw [main3ShiftedSquarePackagePoint_sourceRatio_eq B P homega sigma,
    main3ShiftedSquarePackagePoint_targetRatio_eq B P homega sigma]

/-- Membership in every accepted complex square-map cell transports exactly
across the ratio adapter. -/
theorem main3ShiftedSquarePackagePoint_cellPair_iff
    {a : ℤ} {d w n M : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ShiftedSquareFixedExplicitIntegralBasisData a)
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (homega : P.omega = B.omega)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (i : ComplexUnitCircleSlopeCellIndex) :
    InComplexUnitCircleSquareMapCellPair M i
        (main3EmbeddingSourceRatio
            (main3ShiftedSquareEmbeddingOmega B sigma)
            (main3ShiftedSquareEmbeddingOmegaBar B sigma)
            (main3ShiftedSquarePackagePoint P),
          main3EmbeddingTargetRatio
            (main3ShiftedSquareEmbeddingOmega B sigma)
            (main3ShiftedSquareEmbeddingOmegaBar B sigma)
            (main3ShiftedSquarePackagePoint P)) ↔
      InComplexUnitCircleSquareMapCellPair M i
        (shiftedSquareSourceEmbeddingRatio P sigma,
          shiftedSquareTargetEmbeddingRatio P sigma) := by
  rw [main3ShiftedSquarePackagePoint_ratioPair_eq B P homega sigma]

/-- At the explicit imaginary place, the two determinant-engine ratios of
the fixed-basis package point lie on the unit circle. -/
theorem main3ShiftedSquarePackagePoint_imaginaryRatio_norms_eq_one
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ShiftedSquareFixedExplicitIntegralBasisData a)
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (homega : P.omega = B.omega)
    (ha : 0 < a) :
    let sigma := shiftedSquareImaginaryPlaceEmbedding a ha
    (‖main3EmbeddingSourceRatio
          (main3ShiftedSquareEmbeddingOmega B sigma)
          (main3ShiftedSquareEmbeddingOmegaBar B sigma)
          (main3ShiftedSquarePackagePoint P)‖ = 1) ∧
      (‖main3EmbeddingTargetRatio
          (main3ShiftedSquareEmbeddingOmega B sigma)
          (main3ShiftedSquareEmbeddingOmegaBar B sigma)
          (main3ShiftedSquarePackagePoint P)‖ = 1) := by
  dsimp only
  rw [main3ShiftedSquarePackagePoint_sourceRatio_eq B P homega,
    main3ShiftedSquarePackagePoint_targetRatio_eq B P homega]
  exact ⟨(shiftedSquare_imaginaryPlace_ratioGeometry ha P).source_ratio_norm_eq_one,
    (shiftedSquare_imaginaryPlace_ratioGeometry ha P).target_ratio_norm_eq_one⟩

/-- The actual encoded fixed-basis solution uses the same ratio pair as its
same-witness normalized package. -/
theorem Main3LargeAnalyticFixedBasisEncodingCertificate.main3EmbeddingRatio_pair_eq
    {a : ℤ} {D Y N d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {B : ShiftedSquareFixedExplicitIntegralBasisData a}
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (C : Main3LargeAnalyticFixedBasisEncodingCertificate
      (D := D) (Y := Y) (N := N) B heq)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    (main3EmbeddingSourceRatio
          (main3ShiftedSquareEmbeddingOmega B sigma)
          (main3ShiftedSquareEmbeddingOmegaBar B sigma)
          (shiftedSquareCoordinateCodePoint C.encoded.code),
        main3EmbeddingTargetRatio
          (main3ShiftedSquareEmbeddingOmega B sigma)
          (main3ShiftedSquareEmbeddingOmegaBar B sigma)
          (shiftedSquareCoordinateCodePoint C.encoded.code)) =
      (shiftedSquareSourceEmbeddingRatio C.P sigma,
        shiftedSquareTargetEmbeddingRatio C.P sigma) := by
  have hcode : C.encoded.code = shiftedSquareCoordinateCodeOfPackage C.P := by
    simpa only [shiftedSquareCoordinateCodeOfPackage] using C.encoded_code_eq
  rw [hcode]
  exact main3ShiftedSquarePackagePoint_ratioPair_eq
    B C.P C.omega_eq sigma

/-- The two literal denominators for an actual encoded point are nonzero,
ready to discharge the hypotheses of the reflected radial/ratio
factorization. -/
theorem Main3LargeAnalyticFixedBasisEncodingCertificate.main3EmbeddingRatio_denominators_ne_zero
    {a : ℤ} {D Y N d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {B : ShiftedSquareFixedExplicitIntegralBasisData a}
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (C : Main3LargeAnalyticFixedBasisEncodingCertificate
      (D := D) (Y := Y) (N := N) B heq)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    (((shiftedSquareCoordinateCodePoint C.encoded.code).1.1 : ℂ) +
        main3ShiftedSquareEmbeddingOmegaBar B sigma *
          ((shiftedSquareCoordinateCodePoint C.encoded.code).1.2 : ℂ) ≠ 0) ∧
      (((shiftedSquareCoordinateCodePoint C.encoded.code).2.1 : ℂ) +
        main3ShiftedSquareEmbeddingOmega B sigma *
          ((shiftedSquareCoordinateCodePoint C.encoded.code).2.2 : ℂ) ≠ 0) := by
  have hcode : C.encoded.code = shiftedSquareCoordinateCodeOfPackage C.P := by
    simpa only [shiftedSquareCoordinateCodeOfPackage] using C.encoded_code_eq
  rw [hcode]
  exact main3ShiftedSquarePackagePoint_denominators_ne_zero
    B C.P C.omega_eq sigma

/-- Accepted complex square-map cell membership for an actual encoded point
is exactly the localization membership of its same package. -/
theorem Main3LargeAnalyticFixedBasisEncodingCertificate.main3EmbeddingRatio_cellPair_iff
    {a : ℤ} {D Y N d w n M : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {B : ShiftedSquareFixedExplicitIntegralBasisData a}
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (C : Main3LargeAnalyticFixedBasisEncodingCertificate
      (D := D) (Y := Y) (N := N) B heq)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (i : ComplexUnitCircleSlopeCellIndex) :
    InComplexUnitCircleSquareMapCellPair M i
        (main3EmbeddingSourceRatio
            (main3ShiftedSquareEmbeddingOmega B sigma)
            (main3ShiftedSquareEmbeddingOmegaBar B sigma)
            (shiftedSquareCoordinateCodePoint C.encoded.code),
          main3EmbeddingTargetRatio
            (main3ShiftedSquareEmbeddingOmega B sigma)
            (main3ShiftedSquareEmbeddingOmegaBar B sigma)
            (shiftedSquareCoordinateCodePoint C.encoded.code)) ↔
      InComplexUnitCircleSquareMapCellPair M i
        (shiftedSquareSourceEmbeddingRatio C.P sigma,
          shiftedSquareTargetEmbeddingRatio C.P sigma) := by
  rw [C.main3EmbeddingRatio_pair_eq sigma]

/-- The literal homogeneous point used by the fixed-block cell image has
the shifted-square ratio pair of the very certificate selected to construct
its coordinate code.  Thus no second choice of a normalized witness enters
when localization is passed to the determinant point family. -/
theorem main3LargeAnalytic_blockCellCoordinatePoint_embeddingRatio_pair_eq
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (p : Main3LargeAnalyticSquarefreeBlockPoint h v D Y N)
    (sigma : rationalQuadraticAlgebra (-(shiftedSquareA h v)) →+* ℂ) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let B := shiftedSquareFixedExplicitIntegralBasisData
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
    let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
      htheta (show 8 ≤ Y by omega) hi p
    (main3EmbeddingSourceRatio
          (main3ShiftedSquareEmbeddingOmega B sigma)
          (main3ShiftedSquareEmbeddingOmegaBar B sigma)
          (main3LargeAnalytic_blockCellCoordinatePoint htheta hY hi p),
        main3EmbeddingTargetRatio
          (main3ShiftedSquareEmbeddingOmega B sigma)
          (main3ShiftedSquareEmbeddingOmegaBar B sigma)
          (main3LargeAnalytic_blockCellCoordinatePoint htheta hY hi p)) =
      (shiftedSquareSourceEmbeddingRatio C.P sigma,
        shiftedSquareTargetEmbeddingRatio C.P sigma) := by
  exact
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
        (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    by
      let hY8 : 8 ≤ Y := by omega
      let B := shiftedSquareFixedExplicitIntegralBasisData
        (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
      let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
        htheta hY8 hi p
      simpa only [main3LargeAnalytic_blockCellCoordinatePoint,
          main3LargeAnalytic_blockCoordinateCode]
        using C.main3EmbeddingRatio_pair_eq sigma

end

end PellPaper
