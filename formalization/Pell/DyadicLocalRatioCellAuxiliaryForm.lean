import Pell.DyadicComparableCostPolynomialMeshActualSubcell
import Pell.DyadicLocalRatioCover

/-!
# Auxiliary forms on explicit local-ratio cells

This is the direct composition of the literal `2M` source-ratio cover with
the actual finite-subcell interpolation endpoint.  It removes the former
whole-box common-window input by taking the localization parameter to be a
positive natural number.  The global determinant and budget hypotheses are
still deliberately explicit.
-/

namespace PellPaper

noncomputable section

/-- **Literal auxiliary form on one explicit local source-ratio cell.**
For a positive integral localization parameter, the cell itself supplies the
required common source window.  This theorem does not establish any of the
remaining determinant, clearing-cost, mesh, or curve-count hypotheses. -/
theorem exists_nonzero_real_bounded_integral_generalBidegreeForm_of_dyadicFactorBoxLocalRatioCell_uniformDyadicComparableCostPolynomialMeshRate
    (A B : ℕ) {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    {M k : ℕ} (hM : 0 < M)
    (xScale sigma m xDet L baseCost slack alphaDE alphaUV gainCoeff
      quadCoeff meshCoeff : ℝ)
    (htargetScale : xScale ≤ ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 *
      ((2 ^ i.2.2.2 : ℕ) : ℝ))
    (hxScale : 1536 ≤ xScale) (hsigma : 0 < sigma)
    (hlocalThreshold : Real.exp (Real.log (1536 : ℝ) / sigma) ≤ xScale)
    (hsourceDecay : m * L ≤ Real.log (M : ℝ))
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
    ∃ r : ℕ, r < (A + 1) * (B + 1) ∧
      ∃ c : generalBidegreeFormIndex A B → ℤ, c ≠ 0 ∧
        (∀ p ∈ dyadicFactorTuplePointCell
            (dyadicFactorBoxLocalRatioCell theta Y i M k),
          generalBidegreeFormEval A B c p = 0) ∧
          ∀ j, (|c j| : ℝ) ≤
            (√(r : ℝ) *
              (((dyadicSourceCoordinateBound i : ℤ) ^ A *
                (dyadicTargetCoordinateBound i : ℤ) ^ B : ℤ) : ℝ)) ^ r := by
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hM)
  have hcenterpos : 0 < dyadicFactorBoxLocalRatioCenter i M k := by
    unfold dyadicFactorBoxLocalRatioCenter
    exact mul_pos (dyadicFactorBoxLocalRatioStart_pos i)
      (pow_pos (by
        unfold localRatioMeshStep
        positivity) _)
  refine
    exists_nonzero_real_bounded_integral_generalBidegreeForm_of_dyadicFactorTupleSubcell_uniformDyadicComparableCostPolynomialMeshRate
      A B (dyadicFactorBoxLocalRatioCell theta Y i M k)
      (dyadicFactorBoxLocalRatioCell_subset_dyadicFactorBoxCell theta Y i M k)
      (dyadicFactorBoxLocalRatioCenter i M k) (M : ℝ)
      xScale sigma m xDet L baseCost slack alphaDE alphaUV gainCoeff quadCoeff
        meshCoeff ?_ hcenterpos hMreal htargetScale
          hxScale hsigma hlocalThreshold hsourceDecay hxDetL hB hm hmxDet hshear
            hL hY hgain hquad hslack hcomparisonThreshold hbaseCost hbudget
              hdominates hpolynomialMeshCorrection hcontinuousSurplus
  intro q hq
  exact dyadicFactorBoxLocalRatioCell_commonWindow hq

/-- The homogeneous relation on an explicit local source-ratio cell returns
to the literal affine coordinates `(d/e,v/u)` with exactly the same height.
This is only relation transport, not a curve factorization or point count. -/
theorem exists_nonzero_real_bounded_integral_generalBidegreeFormAffine_of_vanishing_on_dyadicFactorBoxLocalRatioCell
    (A B : ℕ) {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ} (M k : ℕ)
    (haux : ∃ r : ℕ, r < (A + 1) * (B + 1) ∧
      ∃ c : generalBidegreeFormIndex A B → ℤ, c ≠ 0 ∧
        (∀ p ∈ dyadicFactorTuplePointCell
            (dyadicFactorBoxLocalRatioCell theta Y i M k),
          generalBidegreeFormEval A B c p = 0) ∧
          ∀ j, (|c j| : ℝ) ≤
            (√(r : ℝ) *
              (((dyadicSourceCoordinateBound i : ℤ) ^ A *
                (dyadicTargetCoordinateBound i : ℤ) ^ B : ℤ) : ℝ)) ^ r) :
    ∃ r : ℕ, r < (A + 1) * (B + 1) ∧
      ∃ c : generalBidegreeFormIndex A B → ℤ, c ≠ 0 ∧
        (∀ q ∈ dyadicFactorBoxLocalRatioCell theta Y i M k,
          generalBidegreeFormAffineEval A B c
            ((q.1 : ℚ) / (q.2.1 : ℚ))
            ((q.2.2.2 : ℚ) / (q.2.2.1 : ℚ)) = 0) ∧
          ∀ j, (|c j| : ℝ) ≤
            (√(r : ℝ) *
              (((dyadicSourceCoordinateBound i : ℤ) ^ A *
                (dyadicTargetCoordinateBound i : ℤ) ^ B : ℤ) : ℝ)) ^ r := by
  exact
    exists_nonzero_real_bounded_integral_generalBidegreeFormAffine_of_vanishing_on_dyadicFactorTuplePointSubcell
      A B (dyadicFactorBoxLocalRatioCell theta Y i M k)
      (dyadicFactorBoxLocalRatioCell_subset_dyadicFactorBoxCell theta Y i M k) haux

end

end PellPaper
