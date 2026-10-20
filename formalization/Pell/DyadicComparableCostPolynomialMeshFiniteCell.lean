import Pell.DyadicComparableCostPolynomialMeshStrictness
import Pell.ScaledGeneralBidegreeFiniteCell

/-!
# A finite-cell auxiliary form from the uniform dyadic polynomial-mesh rate

This file connects the uniform dyadic comparable-cost determinant endpoint to
the rectangular integral-kernel handoff.  A finite cell whose actual integral
points are represented by dyadic factor tuples has every full-column minor
zero under the uniform hypotheses; consequently one nonzero integral
general-bidegree form vanishes on the entire cell.

The theorem below neither counts the points of the cell nor supplies its
factor tuples, source budget, or polynomial mesh-correction budget.  Those
remain explicit inputs.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- **Finite uniform dyadic-cell auxiliary-form endpoint.**  Suppose each
point of `cell` is literally the integral homogeneous point associated to its
indexed dyadic factor tuple, and the tuple conditions are uniform on the
cell.  The polynomial-mesh comparable-cost rate then kills every full
general-bidegree evaluation minor, so the whole cell lies on one nonzero
integral standard form of bidegree `(A,B)`.

No cell cardinality, source budget, or mesh-correction coefficient bound is
created here: the displayed uniform hypotheses are precisely the data passed
to each grid-sized row selection. -/
theorem exists_nonzero_integral_generalBidegreeForm_of_finset_uniformDyadicComparableCostPolynomialMeshRate
    (A B : ℕ) (cell : Finset GeneralBidegreeFormPoint)
    {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    (d e u v : {p // p ∈ cell} → ℕ)
    (hpoints : ∀ row, dyadicFactorTupleFamilyPoints d e u v row = row.1)
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
    ∃ c : generalBidegreeFormIndex A B → ℤ, c ≠ 0 ∧
      ∀ p ∈ cell, generalBidegreeFormEval A B c p = 0 := by
  classical
  obtain ⟨c, hcne, hcvanish⟩ :=
    exists_nonzero_integral_generalBidegreeForm_of_forall_full_integralEvaluationMinors_eq_zero
      A B (fun row : {p // p ∈ cell} => row.1) (by
  intro r
  have hselectedPoints :
      dyadicFactorTupleFamilyPoints
          (fun row : generalBidegreeFormIndex A B => d (r row))
          (fun row : generalBidegreeFormIndex A B => e (r row))
          (fun row : generalBidegreeFormIndex A B => u (r row))
          (fun row : generalBidegreeFormIndex A B => v (r row)) =
        fun row : generalBidegreeFormIndex A B => (r row).1 := by
    funext row
    exact hpoints (r row)
  have hr : (Equiv.refl (generalBidegreeFormIndex A B)) =
      (generalBidegreeGridPointEquiv A B).trans
        (generalBidegreeGridPointEquiv A B).symm := by
    apply Equiv.ext
    intro row
    exact ((generalBidegreeGridPointEquiv A B).symm_apply_apply row).symm
  have hselected :
      ((generalBidegreeFormEvaluationMatrix A B
        (dyadicFactorTupleFamilyPoints
          (fun row : generalBidegreeFormIndex A B => d (r row))
          (fun row : generalBidegreeFormIndex A B => e (r row))
          (fun row : generalBidegreeFormIndex A B => u (r row))
          (fun row : generalBidegreeFormIndex A B => v (r row)))).submatrix
            (Equiv.refl _) id).det = 0 := by
    exact
      standardSelectedIntegralMinor_det_eq_zero_of_uniformDyadicComparableCostPolynomialMeshRate
        A B (generalBidegreeGridPointEquiv A B) (Equiv.refl _) hr
        (fun row : generalBidegreeFormIndex A B => d (r row))
        (fun row : generalBidegreeFormIndex A B => e (r row))
        (fun row : generalBidegreeFormIndex A B => u (r row))
        (fun row : generalBidegreeFormIndex A B => v (r row))
        s0 M xScale sigma m xDet L baseCost slack alphaDE alphaUV gainCoeff
          quadCoeff meshCoeff
        (fun row => hcond (r row))
        (fun row => hbox (r row))
        hs0 hM
        (fun row => hlower (r row))
        (fun row => hupper (r row))
        htargetScale hxScale hsigma hlocalThreshold hsourceDecay hxDetL
        hB hm hmxDet hshear hL hY hgain hquad hslack hcomparisonThreshold
        hbaseCost hbudget hdominates hpolynomialMeshCorrection hcontinuousSurplus
  rw [hselectedPoints] at hselected
  change (generalBidegreeFormEvaluationMatrix A B
    (fun row : generalBidegreeFormIndex A B => (r row).1)).det = 0 at hselected
  have hmatrix : generalBidegreeFormEvaluationMatrix A B
      (fun row : generalBidegreeFormIndex A B => (r row).1) =
      (generalBidegreeFormEvaluationMatrix A B
        (fun row : {p // p ∈ cell} => row.1)).submatrix r id := by
    ext row ab
    rfl
  rw [← hmatrix]
  exact hselected)
  refine ⟨c, hcne, ?_⟩
  intro p hp
  exact hcvanish ⟨p, hp⟩

end

end PellPaper
