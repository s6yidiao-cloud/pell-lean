import Pell.ShiftedSquareExplicitPlaceGeometry
import Pell.ComplexUnitCircleSquareMapCellPairCover

/-!
# Imaginary-place shifted-square packages enter the finite square-map cells

This adapter specializes the unit-circle square-map cover to the explicit
imaginary embedding of the shifted-square quadratic algebra.  Star becomes
complex conjugation at this place, so the source and target ratios have norm
one; the localization certificate and the cross-multiplied mesh inequality
then select one literal complex source/target cell pair.

No determinant or arithmetic point-count estimate occurs here.
-/

namespace PellPaper

noncomputable section

local instance shiftedSquareImaginaryPlaceCellPairAdapter_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- At the explicit positive-imaginary place, a simultaneous normalized
package lies in one of the literal `8 M + 4` complex square-map cell pairs. -/
theorem exists_shiftedSquare_imaginaryPlace_complexUnitCircleSquareMapCellPair
    {a : ℤ} {d w n M : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : 0 < a) (hd : 0 < d) (hw : 0 < w)
    (hn : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ))
    (hM : 0 < M)
    (hmesh : 8 * (M : ℝ) * Real.sqrt |(a : ℝ)| ≤ (n : ℝ))
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    let sigma := shiftedSquareImaginaryPlaceEmbedding a ha
    ∃ i ∈ complexUnitCircleSlopeCellIndices M,
      InComplexUnitCircleSquareMapCellPair M i
        (shiftedSquareSourceEmbeddingRatio P sigma,
          shiftedSquareTargetEmbeddingRatio P sigma) := by
  let sigma := shiftedSquareImaginaryPlaceEmbedding a ha
  have hloc := shiftedSquare_embeddingRatio_localizationCertificate
    (ne_of_gt ha) hd hw hn P sigma
  have hgeo := shiftedSquare_imaginaryPlace_ratioGeometry ha P
  have hsqrtPos : 0 < Real.sqrt |(a : ℝ)| := by
    exact Real.sqrt_pos.2 (abs_pos.mpr (by exact_mod_cast (ne_of_gt ha)))
  have hnReal : (0 : ℝ) < n := by nlinarith
  have hnNat : 0 < n := by exact_mod_cast hnReal
  simpa only [sigma] using
    exists_mem_complexUnitCircleSquareMapCellPair_of_shiftedSquare_scale
      hM hnNat P sigma hloc hgeo.source_ratio_norm_eq_one
        hgeo.target_ratio_norm_eq_one hmesh

end

end PellPaper
