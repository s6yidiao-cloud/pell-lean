import Pell.DyadicBalancedActualCellAggregation
import Pell.DyadicTwoLayerFanTupleCell
import Pell.DyadicBalancedParameterComposition
import Pell.DyadicResidualFullCellBudget

/-!
# Exact-fan determinant-to-aggregation composition

This module feeds the literal exact-fan auxiliary form on every source-target
tuple cell into the existing sparse/thin/full aggregation theorem.  The
rank-sensitive Hadamard height is enlarged to the already named uniform
full-column height, after which one uniform residual-sieve threshold serves
all cells and all returned factor degrees.

Only the exact fan rate and the residual-sieve threshold remain numerical
premises; no generic rectangular mesh budget is retained.
-/

namespace PellPaper

open Filter

noncomputable section

/-- **Exact-fan determinant-to-balanced-box aggregation.**  The exact
two-layer fan rate supplies every local auxiliary form; one uniform
residual-sieve budget then yields the canonical thin/full box bound. -/
theorem eventually_dyadicFactorBoxCell_card_le_thinFull_of_twoLayerFan_and_uniformBudget
    (hWeil : OneVariableQuadraticWeilDegreeBound) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (B fanK H0 : ℕ) (theta Q : ℝ) (Y : ℕ)
        (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ)
        (xScale sigma m xDet L baseCost : ℝ),
        0 < M → 2 ≤ Y → 2 ≤ Q →
        (M : ℝ) ≤
          ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) →
        ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
          (Y : ℝ) ^ (2 * Q) →
        xScale ≤ ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 *
          ((2 ^ i.2.2.2 : ℕ) : ℝ) →
        1536 ≤ xScale → 0 < sigma →
        Real.exp (Real.log (1536 : ℝ) / sigma) ≤ xScale →
        m * L ≤ Real.log (M : ℝ) →
        xDet * L = (1 - sigma) * Real.log xScale →
        0 < m * L →
        1 ≤ fanK → fanK ≤ B →
        (2 * (fanK : ℝ) - 1) * (m * L) ≤ xDet * L →
        xDet * L ≤ (2 * (fanK : ℝ) + 1) * (m * L) →
        ((2 * ((2 ^ i.1 : ℕ) : ℝ)) *
          (2 * ((2 ^ i.2.1 : ℕ) : ℝ))) ^
            (1 * ((1 + 1) * (B + 1)) / 2) *
          ((2 * ((2 ^ i.2.2.1 : ℕ) : ℝ)) *
            (2 * ((2 ^ i.2.2.2 : ℕ) : ℝ))) ^
              (B * ((1 + 1) * (B + 1)) / 2) ≤ Real.exp baseCost →
        (baseCost + shearedComparableCoordinateLogLoss 1 B 2 24) +
            Real.log (Nat.factorial
              (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) +
          twoLayerFanTaylorTail B *
            (Fintype.card (generalBidegreeGrid 1 B) : ℝ) <
          twoLayerWeight B fanK (m * L) (xDet * L) →
        fullCellResidualSieveUniformBudgetThreshold i M B
            (dyadicSourceTargetCellResidualHeight B i) ≤ (N : ℝ) →
        let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
        let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
        ((dyadicFactorBoxCell theta Y i).card : ℝ) ≤
          1348 * (M : ℝ) *
              ((H0 : ℝ) + 96 * Q * (B : ℝ) + 16) +
            8 * fullCellOddDegreeSieveAggregateEnvelope
              N (2 * B + 1) U V (M : ℝ) := by
  filter_upwards
    [eventually_dyadicFactorBoxCell_card_le_thinFull_of_cellwiseAuxiliary
      hWeil] with N haggregate
  intro B fanK H0 theta Q Y i M xScale sigma m xDet L baseCost
    hM hY hQ hMscale hxQ htargetScale hxScale hsigma hlocalThreshold
    hsourceDecay hxDetL hellM hfanKpos hfanKB hfanLower hfanUpper
    hbaseCost hrate hthreshold
  dsimp only
  apply haggregate B H0 theta Q Y i M hM hY hQ hMscale hxQ
  intro p _hp _hoccupancy
  obtain ⟨r, hr, f, hf0, hvanish, hheight⟩ :=
    exists_nonzero_real_bounded_integral_twoLayerForm_of_dyadicSourceTargetTupleCell_twoLayerFanRate
      (theta := theta) (Y := Y) (boxIndex := i) (M := M)
      (sourceIndex := p.1) (targetIndex := p.2)
      B fanK hM xScale sigma m xDet L baseCost
      htargetScale hxScale hsigma hlocalThreshold hsourceDecay hxDetL
      hellM hfanKpos hfanKB hfanLower hfanUpper hbaseCost hrate
  refine ⟨f, dyadicSourceTargetCellAuxiliaryUniformHeight B i,
    hf0, ?_, ?_, ?_, ?_⟩
  · exact dyadicSourceTargetCellAuxiliaryUniformHeight_nonneg B i
  · intro ab
    exact (hheight ab).trans
      (dyadicSourceTargetCellAuxiliaryHeight_le_uniform B r i hr)
  · intro q hq
    simpa [dyadicFactorTupleToGeneralBidegreeFormPoint] using hvanish q hq
  · intro _hfull
    apply fullCellResidualSieveBudgets_of_uniformBudgetThreshold_le
    exact hthreshold

end

end PellPaper
