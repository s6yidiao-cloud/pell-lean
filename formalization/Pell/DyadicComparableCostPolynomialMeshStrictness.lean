import Pell.DyadicComparableCostStrictness
import Pell.SourceNormalizedFloorCubicSurplusBridge

/-!
# Uniform dyadic comparable-cost strictness with a polynomial mesh budget

This is the uniform-box comparable-cost determinant endpoint with its
abstract finite-mesh surplus premise replaced by the continuous sheared
surplus and the explicit polynomial source-mesh correction.  The actual
source leading-cost budget, local-coordinate input, and determinant-side
shape conditions remain hypotheses.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- **Uniform dyadic comparable-cost endpoint with a polynomial mesh
budget.** The source leading cost is evaluated at the actual bidegree ratio
`A / B`.  A coefficient bound for the displayed polynomial mesh correction
and a continuous sheared-surplus gap replace the abstract floor-cubic
`hsurplus` premise of
`standardSelectedIntegralMinor_det_eq_zero_of_uniformDyadicComparableCostRate`.
No estimate for that correction coefficient or for the cleared base cost is
derived here. -/
theorem standardSelectedIntegralMinor_det_eq_zero_of_uniformDyadicComparableCostPolynomialMeshRate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ℕ) (eRows : ι ≃ generalBidegreeGrid A B)
    (r : generalBidegreeFormIndex A B ≃ ι)
    (hr : r = (generalBidegreeGridPointEquiv A B).trans eRows.symm)
    {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    (d e u v : ι → ℕ)
    (s0 M xScale sigma m xDet L baseCost slack alphaDE alphaUV gainCoeff
      quadCoeff meshCoeff : ℝ)
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
      sourceNormalizedLeadingCost B ((A : ℝ) / (B : ℝ)) alphaDE alphaUV L +
        quadCoeff * (B : ℝ) ^ 2 * L)
    (hdominates : quadCoeff * (B : ℝ) ^ 2 ≤
      (gainCoeff / 2) * (B : ℝ) ^ 3)
    (hpolynomialMeshCorrection :
      sourceNormalizedFloorPolynomialMeshCorrection A B m xDet L ≤
        meshCoeff * (B : ℝ) ^ 3 * L)
    (hcontinuousSurplus : gainCoeff + meshCoeff ≤
      shearedSurplus m xDet alphaDE alphaUV ((A : ℝ) / (B : ℝ))) :
    ((generalBidegreeFormEvaluationMatrix A B
      (dyadicFactorTupleFamilyPoints d e u v)).submatrix r id).det = 0 := by
  have hLpos : 0 < L := by
    rw [hL]
    exact Real.log_pos hY
  have hfloorSurplus :
      sourceNormalizedLeadingCost B ((A : ℝ) / (B : ℝ)) alphaDE alphaUV L +
        gainCoeff * (B : ℝ) ^ 3 * L ≤
      sourceNormalizedFloorCubicGain A B m xDet L :=
    sourceNormalizedLeadingCost_add_cubicGain_le_floorCubicGain_of_polynomialMeshCorrection_coeff_bound
      A B m xDet L alphaDE alphaUV gainCoeff meshCoeff
        hB hm hmxDet hLpos hpolynomialMeshCorrection hcontinuousSurplus
  exact standardSelectedIntegralMinor_det_eq_zero_of_uniformDyadicComparableCostRate
    A B eRows r hr d e u v
      s0 M xScale sigma m xDet L baseCost slack
        ((A : ℝ) / (B : ℝ)) alphaDE alphaUV gainCoeff quadCoeff
      hcond hbox hs0 hM hlower hupper htargetScale hxScale hsigma hlocalThreshold
      hsourceDecay hxDetL hB hm hmxDet hshear hL hY hgain hquad hslack
      hcomparisonThreshold hbaseCost hbudget hdominates hfloorSurplus

end

end PellPaper
