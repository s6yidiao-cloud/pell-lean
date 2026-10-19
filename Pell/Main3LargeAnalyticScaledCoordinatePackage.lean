import Pell.Main3LargeAnalyticCoordinatePackage
import Pell.ShiftedSquareEmbeddingScaleBounds

/-!
# Polynomially scaled coordinate packages on large-analytic main3 blocks

This isolated adapter extends the canonical per-point large-analytic
coordinate certificate with the coefficient-height and polynomial embedding
scale consequences needed by the determinant route.  The extension retains
the exact same coordinate package `P`: in particular its basis, primitive
coordinates, contents, Minkowski element, `C₀`, and target element are not
rechosen.

Only pointwise algebraic consequences are recorded.  There is no ratio
estimate, dyadic subpartition, or counting claim in this module.
-/

namespace PellPaper

noncomputable section

local instance main3LargeAnalyticScaledCoordinatePackage_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- The scale and coefficient consequences attached to an existing
large-analytic coordinate certificate.  Every field refers to the same
literal package `P` occurring in `base`. -/
structure Main3LargeAnalyticScaledCoordinateCertificate
    {a : ℤ} {D Y N d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) : Prop where
  base : Main3LargeAnalyticCoordinateCertificate (D := D) (Y := Y) (N := N)
    heq P
  shift_ne_zero : a ≠ 0
  surface_coefficient_height :
    shiftedSquareSurfaceCoefficientHeight P.c ≤ 8 * a.natAbs + 4
  all_surface_coefficients :
    ∀ i : Fin 3, ∀ j : Fin 2,
      |shiftedSquareSurfaceCoefficients P.t P.c i j| ≤
        ((8 * a.natAbs + 4 : ℕ) : ℤ)
  C₀_le_thirtytwo_mul_sqrt_abs :
    (P.minkowski.C₀ : ℝ) ≤ 32 * Real.sqrt |(a : ℝ)|
  EAlpha_ge_source_floor :
    (shiftedSquareD₀ d : ℝ) / (2 * (P.minkowski.C₀ : ℝ)) ≤
      shiftedSquareEAlpha P
  EGamma_ge_target_floor :
    (w : ℝ) ≤ shiftedSquareEGamma P
  source_embedding_scale_bounds :
    ∀ place : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a)),
      Real.sqrt (shiftedSquareEAlpha P) / shiftedSquareEmbeddingScaleLoss a ≤
          place (shiftedSquareIntegralBasisElement P.basis P.x) ∧
        place (shiftedSquareIntegralBasisElement P.basis P.x) ≤
          shiftedSquareEmbeddingScaleLoss a * Real.sqrt (shiftedSquareEAlpha P)
  target_embedding_scale_bounds :
    ∀ place : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a)),
      Real.sqrt (shiftedSquareEGamma P) / shiftedSquareEmbeddingScaleLoss a ≤
          place (shiftedSquareIntegralBasisElement P.basis P.y) ∧
        place (shiftedSquareIntegralBasisElement P.basis P.y) ≤
          shiftedSquareEmbeddingScaleLoss a * Real.sqrt (shiftedSquareEGamma P)

/-- Every actual point in a large-analytic main3 squarefree block admits the
same simultaneous normalized package as the canonical base theorem, now
equipped with coefficient bounds, the `C₀` bound, norm-scale floors, and all
four polynomial embedding-scale inequalities.  The field certificate is
derived from the active index and remains local to the dependent result. -/
theorem exists_main3LargeAnalytic_scaledCoordinatePackage
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
        (D := D) (Y := Y) (N := N) heq P := by
  let heq := main3LargeAnalytic_squarefreeBlock_equation hp
  let fieldFact : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  change ∃ P : @ShiftedSquareSimultaneousNormalizedCoordinatePackage
      (shiftedSquareA h v) d w n fieldFact heq,
    @Main3LargeAnalyticScaledCoordinateCertificate
      (shiftedSquareA h v) D Y N d w n fieldFact heq P
  have hbaseExists :=
    exists_main3LargeAnalytic_simultaneousNormalizedCoordinatePackage
      htheta hY hi hp
  change ∃ P : @ShiftedSquareSimultaneousNormalizedCoordinatePackage
      (shiftedSquareA h v) d w n fieldFact heq,
    @Main3LargeAnalyticCoordinateCertificate
      (shiftedSquareA h v) D Y N d w n fieldFact heq P at hbaseExists
  obtain ⟨P, hbase⟩ := hbaseExists
  have hiActive :=
    (mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi).1
  obtain ⟨hiBroad, hcell⟩ :=
    mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiActive
  have hshift :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_shift_package
      hiBroad hcell
  have ha : shiftedSquareA h v ≠ 0 := hshift.2.2.1
  refine ⟨P, {
    base := hbase
    shift_ne_zero := ha
    surface_coefficient_height :=
      @ShiftedSquareSimultaneousNormalizedCoordinatePackage.surfaceCoefficientHeight_le
        (shiftedSquareA h v) d w n fieldFact heq P
    all_surface_coefficients := fun i j =>
      @ShiftedSquareSimultaneousNormalizedCoordinatePackage.surfaceCoefficient_abs_le
        (shiftedSquareA h v) d w n fieldFact heq P i j
    C₀_le_thirtytwo_mul_sqrt_abs := P.minkowski.C₀_le_thirtytwo_mul_sqrt_abs
    EAlpha_ge_source_floor :=
      @shiftedSquareEAlpha_ge_sourceFloor
        (shiftedSquareA h v) d w n fieldFact heq P
    EGamma_ge_target_floor :=
      @shiftedSquareEGamma_ge_targetFloor
        (shiftedSquareA h v) d w n fieldFact heq P
    source_embedding_scale_bounds := fun place =>
      @shiftedSquare_sourceEmbedding_scaleBounds
        (shiftedSquareA h v) d w n fieldFact heq ha hbase.source_pos P place
    target_embedding_scale_bounds := fun place =>
      @shiftedSquare_targetEmbedding_scaleBounds
        (shiftedSquareA h v) d w n fieldFact heq ha hbase.source_pos
          hbase.shift_dominance P place }⟩

end

end PellPaper
