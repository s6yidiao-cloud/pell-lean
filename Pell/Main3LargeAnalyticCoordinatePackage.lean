import Pell.Main3LargeAnalyticShiftDominance
import Pell.ShiftedSquareContentScaleBounds
import Pell.ShiftedSquareQuadraticEmbeddingLower
import Pell.ShiftedSquareSimultaneousRouteAdapter
import Pell.ShiftedSquareTargetEmbeddingRoute
import Mathlib.Tactic

/-!
# Coordinate packages for points in large-analytic main3 blocks

This isolated route adapter starts from an actual point of an active
large-analytic squarefree shifted-square block.  Active-cell nonemptiness
supplies the squarefree admissible shift, block membership supplies the
positive squarefree target and exact shifted-square equation, and the
large-analytic cutoff supplies numerator dominance.  These are precisely the
hypotheses of the simultaneous normalized-coordinate construction.

The capstone theorem installs the rational-root certificate derived from the
active cell inside its result type.  Thus no field `Fact` is assumed by its
caller.  The returned package is accompanied by the literal dyadic ranges,
the exact source and target embedding boxes, the two scalar lower-scale
bounds, and the fixed-coordinate fibre bound.  No point-count or analytic
estimate is introduced here.
-/

namespace PellPaper

noncomputable section

local instance main3LargeAnalyticCoordinatePackage_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- The exact equation carried by membership in a squarefree shifted-square
block.  Naming this proof keeps the dependent coordinate-package type stable
at the main3 route boundary. -/
theorem main3LargeAnalytic_squarefreeBlock_equation
    {h : ℤ} {v D Y N d w n : ℕ}
    (hp : (d, w, n) ∈
      squarefreeShiftedSquareBlock (shiftedSquareA h v) D Y N) :
    (d : ℤ) ^ 2 * (w : ℤ) =
      (n : ℤ) ^ 2 + shiftedSquareA h v := by
  obtain ⟨_hd, _hw, _hn, _hDd, _hdD, _hYw, _hwY, _hNn, _hnN,
      heq, _hsf⟩ := mem_squarefreeShiftedSquareBlock.mp hp
  exact heq

/-- The active-cell shift package rules out rational roots in the quadratic
algebra attached to every large-analytic index. -/
theorem main3LargeAnalytic_shift_noRationalRoot
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    rationalQuadraticAlgebraNoRationalRoot (-(shiftedSquareA h v)) := by
  have hiLarge :=
    mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi
  have hiActive :=
    mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiLarge.1
  have hshift :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_shift_package
      hiActive.1 hiActive.2
  exact shiftedSquare_radicand_noRationalRoot hshift.2.1 hshift.2.2.2

/-- Route-facing consequences attached to one simultaneous normalized
coordinate package.  The parameter `heq` is the literal equation extracted
from the block point, so every displayed conclusion concerns the same
original `(d,w,n)` and the same nested Minkowski witness. -/
structure Main3LargeAnalyticCoordinateCertificate
    {a : ℤ} {D Y N d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) : Prop where
  source_pos : 0 < d
  target_pos : 0 < w
  numerator_pos : 0 < n
  source_dyadic : D ≤ d ∧ d < 2 * D
  target_dyadic : Y ≤ w ∧ w < 2 * Y
  numerator_dyadic : N ≤ n ∧ n < 2 * N
  target_squarefree : Squarefree w
  shift_dominance : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ)
  source_embedding_box :
    ∀ place : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a)),
      (((shiftedSquareD₀ d * P.minkowski.C₀ : ℕ) : ℝ) /
          (8 * Real.sqrt
            ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|))) / P.r ≤
          place (shiftedSquareIntegralBasisElement P.basis P.x) ∧
        place (shiftedSquareIntegralBasisElement P.basis P.x) <
          (8 * Real.sqrt
            ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|)) / P.r
  target_embedding_box :
    ∀ place : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a)),
      ((P.minkowski.C₀ : ℝ) ^ 2 * ((n : ℝ) / 4)) /
            ((8 * Real.sqrt
              ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|)) ^ 2 * P.ell) ≤
          place (shiftedSquareIntegralBasisElement P.basis P.y) ∧
        place (shiftedSquareIntegralBasisElement P.basis P.y) ≤
          ((P.minkowski.C₀ : ℝ) ^ 2 * (2 * (n : ℝ))) /
            (((((shiftedSquareD₀ d * P.minkowski.C₀ : ℕ) : ℝ) /
                (8 * Real.sqrt
                  ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|))) ^ 2) *
              P.ell)
  source_norm_scale_lower :
    (shiftedSquareD₀ d : ℝ) / (2 * (P.minkowski.C₀ : ℝ)) ≤
      ((shiftedSquareD₀ d * P.minkowski.C₀ : ℕ) : ℝ) /
        (P.r : ℝ) ^ 2
  target_norm_scale_lower :
    (w : ℝ) ≤
      ((w * P.minkowski.C₀ ^ 2 : ℕ) : ℝ) / (P.ell : ℝ) ^ 2
  fixed_fibre_card_le_one :
    ∀ S : Finset (ShiftedSquareFixedCoordinateSolution a P.basis P.t P.c
      P.minkowski.C₀ P.r P.ell P.x P.y), S.card ≤ 1

/-- Every point of a large-analytic main3 squarefree block admits a
simultaneous normalized coordinate package, with no caller-supplied field
certificate.  All data and estimates in the certificate refer to the same
package `P` and hence to its single nested Minkowski element. -/
theorem exists_main3LargeAnalytic_simultaneousNormalizedCoordinatePackage
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
      Main3LargeAnalyticCoordinateCertificate (D := D) (Y := Y) (N := N)
        heq P := by
  let heq := main3LargeAnalytic_squarefreeBlock_equation hp
  let fieldFact : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  change ∃ P : @ShiftedSquareSimultaneousNormalizedCoordinatePackage
      (shiftedSquareA h v) d w n fieldFact heq,
    @Main3LargeAnalyticCoordinateCertificate
      (shiftedSquareA h v) D Y N d w n fieldFact heq P
  have hiLarge :=
    mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi
  have hiActive :=
    mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiLarge.1
  have hshift :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_shift_package
      hiActive.1 hiActive.2
  obtain ⟨hd, hwpos, hnpos, hDd, hdD, hYw, hwY, hNn, hnN,
      _heq, hw⟩ := mem_squarefreeShiftedSquareBlock.mp hp
  have hwone : 1 < w := by omega
  obtain ⟨P⟩ :=
    @exists_shiftedSquareSimultaneousNormalizedCoordinatePackage
      (shiftedSquareA h v) d w n fieldFact hshift.2.1 hd hw hwone heq
  have hdominance :=
    mem_main3LargeAnalytic_squarefreeBlock_shift_dominates
      htheta hY hi hp
  refine ⟨P, {
    source_pos := hd
    target_pos := hwpos
    numerator_pos := hnpos
    source_dyadic := ⟨hDd, hdD⟩
    target_dyadic := ⟨hYw, hwY⟩
    numerator_dyadic := ⟨hNn, hnN⟩
    target_squarefree := hw
    shift_dominance := hdominance
    source_embedding_box := fun place =>
      @shiftedSquare_sourceEmbedding_twoSided
        (shiftedSquareA h v) d w n fieldFact heq hd P place
    target_embedding_box := fun place =>
      @shiftedSquare_targetEmbedding_twoSided
        (shiftedSquareA h v) d w n fieldFact heq hd hdominance P place
    source_norm_scale_lower :=
      @shiftedSquare_sourceNormScale_lower
        (shiftedSquareA h v) d w n fieldFact heq P
    target_norm_scale_lower :=
      @shiftedSquare_targetNormScale_lower
        (shiftedSquareA h v) d w n fieldFact heq P
    fixed_fibre_card_le_one := fun S =>
      @ShiftedSquareSimultaneousNormalizedCoordinatePackage.fixedFiber_card_le_one
        (shiftedSquareA h v) d w n fieldFact heq P S }⟩

end

end PellPaper
