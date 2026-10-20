import Pell.DyadicComparableCostAdapter
import Pell.DyadicTargetScaleLogSlack
import Pell.SourceNormalizedLeadingCostRate

/-!
# A literal dyadic comparable-cost determinant endpoint

For a single actual dyadic factor box, the source-centre and endpoint-scale
comparisons have fixed constants `2` and `24`. This module composes that
geometric transport with the named logarithmic loss and the source-normalized
leading-cost cancellation. It removes abstract clearing-cost and strict-rate
premises from the dyadic target-scale minor endpoint.

The symmetric dyadic base-cost estimate, leading-cost residual budget, and
finite-mesh cubic surplus remain explicit source-specific quantitative inputs.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- **Uniform-box comparable-cost determinant endpoint.** Actual factor
tuples in one dyadic box supply the cleared-minor cost with literal `c = 2`,
`k = 24` logarithmic loss. A common source leading cost, explicit quadratic
residual budget, and finite-mesh cubic surplus then supply the strict rate. -/
theorem standardSelectedIntegralMinor_det_eq_zero_of_uniformDyadicComparableCostRate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ℕ) (eRows : ι ≃ generalBidegreeGrid A B)
    (r : generalBidegreeFormIndex A B ≃ ι)
    (hr : r = (generalBidegreeGridPointEquiv A B).trans eRows.symm)
    {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    (d e u v : ι → ℕ)
    (s0 M xScale sigma m xDet L baseCost slack rho alphaDE alphaUV gainCoeff
      quadCoeff : ℝ)
    (hcond : ∀ row, DyadicFactorCondition theta Y
      (d row) (e row) (u row) (v row))
    (hbox : ∀ row, (d row, e row, u row, v row) ∈ dyadicBox i)
    (hs0 : 0 < s0) (hM : 1 ≤ M)
    (hlower : ∀ row, s0 ≤ (d row : ℝ) / (e row : ℝ))
    (hupper : ∀ row, (d row : ℝ) / (e row : ℝ) ≤ s0 * (1 + 1 / M))
    (htargetScale : xScale ≤ ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 *
      ((2 ^ i.2.2.2 : ℕ) : ℝ))
    (hxScale : 1536 ≤ xScale) (hsigma : 0 < sigma)
    (hlocalThreshold : Real.exp (Real.log (1536 : ℝ) / sigma) ≤ xScale)
    (hsourceDecay : m * L ≤ Real.log M)
    (hxDetL : xDet * L = (1 - sigma) * Real.log xScale)
    (hB : 0 < B) (hm : 0 < m) (hmxDet : m ≤ xDet)
    (hshear : xDet * ((A : ℝ) / (B : ℝ)) ≤ 2 * m)
    (hL : L = Real.log (Y : ℝ)) (hY : 1 < (Y : ℝ))
    (hgain : 0 < gainCoeff) (hquad : 0 ≤ quadCoeff) (hslack : 0 < slack)
    (hcomparisonThreshold :
      Real.exp (shearedComparableCoordinateLogLoss A B 2 24 / slack) ≤ (Y : ℝ))
    (hbaseCost :
      ((2 * ((2 ^ i.1 : ℕ) : ℝ)) *
        (2 * ((2 ^ i.2.1 : ℕ) : ℝ))) ^
          (A * ((A + 1) * (B + 1)) / 2) *
        ((2 * ((2 ^ i.2.2.1 : ℕ) : ℝ)) *
          (2 * ((2 ^ i.2.2.2 : ℕ) : ℝ))) ^
            (B * ((A + 1) * (B + 1)) / 2) ≤ Real.exp baseCost)
    (hbudget : baseCost + slack * L +
      Real.log (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) +
        shearedActualRankTaylorTail A B *
          (Fintype.card (generalBidegreeGrid A B) : ℝ) ≤
      sourceNormalizedLeadingCost B rho alphaDE alphaUV L +
        quadCoeff * (B : ℝ) ^ 2 * L)
    (hdominates : quadCoeff * (B : ℝ) ^ 2 ≤
      (gainCoeff / 2) * (B : ℝ) ^ 3)
    (hsurplus : sourceNormalizedLeadingCost B rho alphaDE alphaUV L +
      gainCoeff * (B : ℝ) ^ 3 * L ≤
      sourceNormalizedFloorCubicGain A B m xDet L) :
    ((generalBidegreeFormEvaluationMatrix A B
      (dyadicFactorTupleFamilyPoints d e u v)).submatrix r id).det = 0 := by
  have hcost :
      |(∏ j : generalBidegreeFormIndex A B,
          ((dyadicFactorTupleFamilyPoints d e u v (r j)).1.2 : ℝ) ^ A *
            ((dyadicFactorTupleFamilyPoints d e u v (r j)).2.2 : ℝ) ^ B) *
          s0 ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2)| ≤
        Real.exp (baseCost + shearedComparableCoordinateLogLoss A B 2 24) :=
    dyadicFactorTupleFamilyPoints_hcost_logLoss_of_dyadicComparableBounds
      A B d e u v r hcond hbox hM hlower hupper hbaseCost
  have hrate :
      (baseCost + shearedComparableCoordinateLogLoss A B 2 24) +
          Real.log (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) +
        shearedActualRankTaylorTail A B *
          (Fintype.card (generalBidegreeGrid A B) : ℝ) <
        sourceNormalizedFloorCubicGain A B m xDet L := by
    exact sourceNormalizedFloor_strictRate_of_comparableCoordinateLoss
      A B m xDet L baseCost 2 24 slack
        (sourceNormalizedLeadingCost B rho alphaDE alphaUV L)
        gainCoeff quadCoeff (Y : ℝ)
        hB hL hY hgain hquad hslack hcomparisonThreshold hbudget
        hdominates hsurplus
  have hLpos : 0 < L := by
    rw [hL]
    exact Real.log_pos hY
  exact standardSelectedIntegralMinor_det_eq_zero_of_dyadicTargetScaleLogSlack
    A B eRows r hr (fun _ => i) d e u v s0 M xScale sigma m xDet L
      hcond hbox hs0 hM hlower hupper (fun _ => htargetScale) hxScale hsigma
      hlocalThreshold hsourceDecay hxDetL hB hm hmxDet hLpos hshear
      (baseCost + shearedComparableCoordinateLogLoss A B 2 24) hcost hrate

end

end PellPaper
