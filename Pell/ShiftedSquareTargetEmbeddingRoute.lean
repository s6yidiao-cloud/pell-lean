import Pell.ShiftedSquareTargetEmbeddingBounds
import Pell.ShiftedSquareZetaEmbeddingBounds

/-!
# Unconditional target embedding box on the large shifted-square range

This route adapter composes the reviewed zeta comparison with the reviewed
factorization transfer.  Its only extra hypothesis is the manuscript's
large-range condition `2 * sqrt |a| ≤ n`.
-/

namespace PellPaper

noncomputable section

/-- At every infinite place, the primitive target element lies in the exact
two-sided box obtained from the simultaneous source element whenever the
shifted-square numerator dominates the field parameter. -/
theorem shiftedSquare_targetEmbedding_twoSided
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (hd : 0 < d)
    (hn : 2 * Real.sqrt |a| ≤ (n : ℝ))
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a))) :
    ((P.minkowski.C₀ : ℝ) ^ 2 * ((n : ℝ) / 4)) /
          ((8 * Real.sqrt
            ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|)) ^ 2 * P.ell) ≤
        v (shiftedSquareIntegralBasisElement P.basis P.y) ∧
      v (shiftedSquareIntegralBasisElement P.basis P.y) ≤
        ((P.minkowski.C₀ : ℝ) ^ 2 * (2 * (n : ℝ))) /
          (((((shiftedSquareD₀ d * P.minkowski.C₀ : ℕ) : ℝ) /
              (8 * Real.sqrt
                ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|))) ^ 2) * P.ell) :=
  shiftedSquare_targetEmbedding_twoSided_of_zeta_bounds hd P v
    (shiftedSquareZeta_infinitePlace_bounds a d n hn v)

end

end PellPaper
