import Pell.DyadicLocalRatioCellAuxiliaryForm
import Pell.DyadicTargetImageGeometry
import Pell.GeneralBidegreeOneSpecialization

/-!
# Two-layer auxiliary forms on literal source-target cells

The general-bidegree determinant endpoint on an explicit local source-ratio
cell specializes at source degree one to the two-layer form used by the
residual full-cell count.  Since a literal source-target tuple cell is a
filter of that local cell, the same form vanishes on every tuple in the
source-target cell with no coefficient-height loss.

All determinant, clearing-cost, mesh, and continuous-surplus hypotheses
remain explicit.  This file performs only the exact specialization and
restriction needed by the downstream full-cell count.
-/

namespace PellPaper

noncomputable section

/-- The exact Hadamard coefficient height delivered by the dyadic
source-degree-one endpoint is nonnegative, including the rank-zero case.
This is the sign side condition required when the height is passed to the
downstream residual full-cell theorem. -/
theorem dyadicSourceTargetCell_twoLayerAuxiliaryHeight_nonneg
    (B r : ℕ) (i : ℕ × ℕ × ℕ × ℕ) :
    0 ≤
      (√(r : ℝ) *
        (((dyadicSourceCoordinateBound i : ℤ) ^ 1 *
          (dyadicTargetCoordinateBound i : ℤ) ^ B : ℤ) : ℝ)) ^ r := by
  positivity

/-- A bounded general bidegree-`(1,B)` auxiliary form on a local source-ratio
cell is literally a bounded two-layer form on each of its source-target
subcells.  The target-ceiling filter only restricts the vanishing family;
the coefficient vector and its exact Hadamard height are unchanged. -/
theorem exists_nonzero_real_bounded_integral_twoLayerForm_on_dyadicSourceTargetTupleCell_of_generalBidegreeOne
    (B : ℕ) {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    (M j : ℕ)
    (haux : ∃ r : ℕ, r < (1 + 1) * (B + 1) ∧
      ∃ c : generalBidegreeFormIndex 1 B → ℤ, c ≠ 0 ∧
        (∀ p ∈ dyadicFactorTuplePointCell
            (dyadicFactorBoxLocalRatioCell theta Y i M j),
          generalBidegreeFormEval 1 B c p = 0) ∧
          ∀ ab, (|c ab| : ℝ) ≤
            (√(r : ℝ) *
              (((dyadicSourceCoordinateBound i : ℤ) ^ 1 *
                (dyadicTargetCoordinateBound i : ℤ) ^ B : ℤ) : ℝ)) ^ r) :
    ∃ r : ℕ, r < 2 * (B + 1) ∧
      ∃ f : twoLayerFormIndex B → ℤ, f ≠ 0 ∧
        (∀ k : ℤ, ∀ q ∈ dyadicSourceTargetTupleCell theta Y i M j k,
            twoLayerFormEval B f
              (((q.1 : ℤ), (q.2.1 : ℤ)),
                ((q.2.2.2 : ℤ), (q.2.2.1 : ℤ))) = 0) ∧
          ∀ ab, (|f ab| : ℝ) ≤
            (√(r : ℝ) *
              (((dyadicSourceCoordinateBound i : ℤ) ^ 1 *
                (dyadicTargetCoordinateBound i : ℤ) ^ B : ℤ) : ℝ)) ^ r := by
  rcases haux with ⟨r, hr, c, hc, hvanish, hheight⟩
  refine ⟨r, ?_, c, hc, ?_, hheight⟩
  · simpa using hr
  · intro k q hq
    have hlocal : q ∈ dyadicFactorBoxLocalRatioCell theta Y i M j :=
      (Finset.mem_filter.mp hq).1
    have hp :
        (((q.1 : ℤ), (q.2.1 : ℤ)),
            ((q.2.2.2 : ℤ), (q.2.2.1 : ℤ))) ∈
          dyadicFactorTuplePointCell
            (dyadicFactorBoxLocalRatioCell theta Y i M j) := by
      exact Finset.mem_map.mpr ⟨q, hlocal, rfl⟩
    simpa only [generalBidegreeFormEval_one_eq_twoLayerFormEval] using
      hvanish _ hp

/-- **Literal source-target-cell two-layer auxiliary form.**  Under the
existing polynomial-mesh determinant budgets, a positive integral local
mesh parameter gives one nonzero integral two-layer form on every literal
source-target tuple cell.  The output retains the exact separate-coordinate
Hadamard height from the general-bidegree endpoint.

This is directly consumable by
`eventually_exists_bounded_twoLayer_common_factor_with_full_dyadic_count`:
take its form degree to be `B` and its real coefficient bound to be the
displayed height.  No determinant budget or full-cell sieve budget is proved
here. -/
theorem exists_nonzero_real_bounded_integral_twoLayerForm_of_dyadicSourceTargetTupleCell_uniformDyadicComparableCostPolynomialMeshRate
    (B : ℕ) {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    {M j : ℕ} (hM : 0 < M)
    (xScale sigma m xDet L baseCost slack alphaDE alphaUV gainCoeff
      quadCoeff meshCoeff : ℝ)
    (htargetScale : xScale ≤ ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 *
      ((2 ^ i.2.2.2 : ℕ) : ℝ))
    (hxScale : 1536 ≤ xScale) (hsigma : 0 < sigma)
    (hlocalThreshold : Real.exp (Real.log (1536 : ℝ) / sigma) ≤ xScale)
    (hsourceDecay : m * L ≤ Real.log (M : ℝ))
    (hxDetL : xDet * L = (1 - sigma) * Real.log xScale)
    (hB : 0 < B) (hm : 0 < m) (hmxDet : m ≤ xDet)
    (hshear : xDet * ((1 : ℝ) / (B : ℝ)) ≤ 2 * m)
    (hL : L = Real.log (Y : ℝ)) (hY : 1 < (Y : ℝ))
    (hgain : 0 < gainCoeff) (hquad : 0 ≤ quadCoeff) (hslack : 0 < slack)
    (hcomparisonThreshold :
      Real.exp (shearedComparableCoordinateLogLoss 1 B 2 24 / slack) ≤
        (Y : ℝ))
    (hbaseCost :
      ((2 * ((2 ^ i.1 : ℕ) : ℝ)) *
        (2 * ((2 ^ i.2.1 : ℕ) : ℝ))) ^
          (1 * ((1 + 1) * (B + 1)) / 2) *
        ((2 * ((2 ^ i.2.2.1 : ℕ) : ℝ)) *
          (2 * ((2 ^ i.2.2.2 : ℕ) : ℝ))) ^
            (B * ((1 + 1) * (B + 1)) / 2) ≤ Real.exp baseCost)
    (hbudget : baseCost + slack * L +
      Real.log (Nat.factorial (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) +
        shearedActualRankTaylorTail 1 B *
          (Fintype.card (generalBidegreeGrid 1 B) : ℝ) ≤
      sourceNormalizedLeadingCost B ((1 : ℝ) / (B : ℝ))
          alphaDE alphaUV L +
        quadCoeff * (B : ℝ) ^ 2 * L)
    (hdominates : quadCoeff * (B : ℝ) ^ 2 ≤
      (gainCoeff / 2) * (B : ℝ) ^ 3)
    (hpolynomialMeshCorrection :
      sourceNormalizedFloorPolynomialMeshCorrection 1 B m xDet L ≤
        meshCoeff * (B : ℝ) ^ 3 * L)
    (hcontinuousSurplus : gainCoeff + meshCoeff ≤
      shearedSurplus m xDet alphaDE alphaUV ((1 : ℝ) / (B : ℝ))) :
    ∃ r : ℕ, r < 2 * (B + 1) ∧
      ∃ f : twoLayerFormIndex B → ℤ, f ≠ 0 ∧
        (∀ k : ℤ, ∀ q ∈ dyadicSourceTargetTupleCell theta Y i M j k,
            twoLayerFormEval B f
              (((q.1 : ℤ), (q.2.1 : ℤ)),
                ((q.2.2.2 : ℤ), (q.2.2.1 : ℤ))) = 0) ∧
          ∀ ab, (|f ab| : ℝ) ≤
            (√(r : ℝ) *
              (((dyadicSourceCoordinateBound i : ℤ) ^ 1 *
                (dyadicTargetCoordinateBound i : ℤ) ^ B : ℤ) : ℝ)) ^ r := by
  apply
    exists_nonzero_real_bounded_integral_twoLayerForm_on_dyadicSourceTargetTupleCell_of_generalBidegreeOne
      B M j
  exact
    exists_nonzero_real_bounded_integral_generalBidegreeForm_of_dyadicFactorBoxLocalRatioCell_uniformDyadicComparableCostPolynomialMeshRate
      1 B hM xScale sigma m xDet L baseCost slack alphaDE alphaUV gainCoeff
        quadCoeff meshCoeff htargetScale hxScale hsigma hlocalThreshold
          hsourceDecay hxDetL hB hm hmxDet (by simpa using hshear) hL hY
            hgain hquad hslack hcomparisonThreshold hbaseCost
              (by simpa using hbudget) hdominates
              hpolynomialMeshCorrection (by simpa using hcontinuousSurplus)

end

end PellPaper
