import Pell.DyadicComparableCostPolynomialMeshFiniteCell
import Pell.GeneralBidegreeFullMinorHadamardHeight

/-!
# Explicit dyadic coordinate heights for the finite-cell polynomial-mesh relation

This file adds the literal Hadamard-height conclusion to the finite uniform
dyadic-cell auxiliary-form endpoint.  The source and target coordinate bounds
are the maximum of the two relevant doubled dyadic endpoints; no asymptotic
replacement by a power of `Y` is made.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The common nonnegative source-coordinate bound for a dyadic box. -/
def dyadicSourceCoordinateBound (i : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  2 * max (2 ^ i.1) (2 ^ i.2.1)

/-- The common nonnegative target-coordinate bound for a dyadic box. -/
def dyadicTargetCoordinateBound (i : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  2 * max (2 ^ i.2.2.1) (2 ^ i.2.2.2)

/-- Actual factor tuples in one dyadic box give literal separate bounds for
the homogeneous coordinates `((d,e),(v,u))`. -/
theorem dyadicFactorTupleFamilyPoints_coordinates_bounded_of_mem_dyadicBox
    {ι : Type*} (d e u v : ι → ℕ) {i : ℕ × ℕ × ℕ × ℕ}
    (hbox : ∀ row, (d row, e row, u row, v row) ∈ dyadicBox i) :
    ∀ row, generalBidegreeFormPointCoordinatesBounded
      (dyadicSourceCoordinateBound i) (dyadicTargetCoordinateBound i)
      (dyadicFactorTupleFamilyPoints d e u v row) := by
  intro row
  obtain ⟨hd, he, hu, hv⟩ := dyadicBox_coordinate_upper_bounds (hbox row)
  have hd' : d row ≤ dyadicSourceCoordinateBound i := by
    unfold dyadicSourceCoordinateBound
    calc
      d row ≤ 2 * 2 ^ i.1 := hd
      _ ≤ 2 * max (2 ^ i.1) (2 ^ i.2.1) :=
        Nat.mul_le_mul_left _ (Nat.le_max_left _ _)
  have he' : e row ≤ dyadicSourceCoordinateBound i := by
    unfold dyadicSourceCoordinateBound
    calc
      e row ≤ 2 * 2 ^ i.2.1 := he
      _ ≤ 2 * max (2 ^ i.1) (2 ^ i.2.1) :=
        Nat.mul_le_mul_left _ (Nat.le_max_right _ _)
  have hu' : u row ≤ dyadicTargetCoordinateBound i := by
    unfold dyadicTargetCoordinateBound
    calc
      u row ≤ 2 * 2 ^ i.2.2.1 := hu
      _ ≤ 2 * max (2 ^ i.2.2.1) (2 ^ i.2.2.2) :=
        Nat.mul_le_mul_left _ (Nat.le_max_left _ _)
  have hv' : v row ≤ dyadicTargetCoordinateBound i := by
    unfold dyadicTargetCoordinateBound
    calc
      v row ≤ 2 * 2 ^ i.2.2.2 := hv
      _ ≤ 2 * max (2 ^ i.2.2.1) (2 ^ i.2.2.2) :=
        Nat.mul_le_mul_left _ (Nat.le_max_right _ _)
  unfold generalBidegreeFormPointCoordinatesBounded
    dyadicFactorTupleFamilyPoints dyadicFactorTupleToGeneralBidegreeFormPoint
  norm_num
  exact ⟨by exact_mod_cast hd', by exact_mod_cast he',
    by exact_mod_cast hv', by exact_mod_cast hu'⟩

/-- **Finite uniform dyadic-cell relation with literal Hadamard height.**
The uniform polynomial-mesh comparable-cost hypotheses make every full
minor of the raw cell evaluation matrix vanish.  The dyadic box then supplies
the separate coordinate bounds
`2 max(D,E)` and `2 max(U,V)`, so the resulting nonzero integral form has
the displayed cofactor/Hadamard coefficient scale.

No asymptotic bound in `Y`, no factor-height bound, and no point-counting
conclusion is asserted. -/
theorem exists_nonzero_real_bounded_integral_generalBidegreeForm_of_finset_uniformDyadicComparableCostPolynomialMeshRate
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
    ∃ r : ℕ, r < (A + 1) * (B + 1) ∧
      ∃ c : generalBidegreeFormIndex A B → ℤ, c ≠ 0 ∧
        (∀ p ∈ cell, generalBidegreeFormEval A B c p = 0) ∧
          ∀ j, (|c j| : ℝ) ≤
            (√(r : ℝ) *
              (((dyadicSourceCoordinateBound i : ℤ) ^ A *
                (dyadicTargetCoordinateBound i : ℤ) ^ B : ℤ) : ℝ)) ^ r := by
  classical
  have hminor : ∀ s : generalBidegreeFormIndex A B ↪ {p // p ∈ cell},
      ((generalBidegreeFormEvaluationMatrix A B
        (fun row : {p // p ∈ cell} => row.1)).submatrix s id).det = 0 := by
    intro s
    have hselectedPoints :
        dyadicFactorTupleFamilyPoints
            (fun row : generalBidegreeFormIndex A B => d (s row))
            (fun row : generalBidegreeFormIndex A B => e (s row))
            (fun row : generalBidegreeFormIndex A B => u (s row))
            (fun row : generalBidegreeFormIndex A B => v (s row)) =
          fun row : generalBidegreeFormIndex A B => (s row).1 := by
      funext row
      exact hpoints (s row)
    have hidentityRows : (Equiv.refl (generalBidegreeFormIndex A B)) =
        (generalBidegreeGridPointEquiv A B).trans
          (generalBidegreeGridPointEquiv A B).symm := by
      apply Equiv.ext
      intro row
      exact ((generalBidegreeGridPointEquiv A B).symm_apply_apply row).symm
    have hselected :
        ((generalBidegreeFormEvaluationMatrix A B
          (dyadicFactorTupleFamilyPoints
            (fun row : generalBidegreeFormIndex A B => d (s row))
            (fun row : generalBidegreeFormIndex A B => e (s row))
            (fun row : generalBidegreeFormIndex A B => u (s row))
            (fun row : generalBidegreeFormIndex A B => v (s row)))).submatrix
              (Equiv.refl _) id).det = 0 := by
      exact
        standardSelectedIntegralMinor_det_eq_zero_of_uniformDyadicComparableCostPolynomialMeshRate
          A B (generalBidegreeGridPointEquiv A B) (Equiv.refl _) hidentityRows
          (fun row : generalBidegreeFormIndex A B => d (s row))
          (fun row : generalBidegreeFormIndex A B => e (s row))
          (fun row : generalBidegreeFormIndex A B => u (s row))
          (fun row : generalBidegreeFormIndex A B => v (s row))
          s0 M xScale sigma m xDet L baseCost slack alphaDE alphaUV gainCoeff
            quadCoeff meshCoeff
          (fun row => hcond (s row))
          (fun row => hbox (s row))
          hs0 hM
          (fun row => hlower (s row))
          (fun row => hupper (s row))
          htargetScale hxScale hsigma hlocalThreshold hsourceDecay hxDetL
          hB hm hmxDet hshear hL hY hgain hquad hslack hcomparisonThreshold
          hbaseCost hbudget hdominates hpolynomialMeshCorrection hcontinuousSurplus
    rw [hselectedPoints] at hselected
    change (generalBidegreeFormEvaluationMatrix A B
      (fun row : generalBidegreeFormIndex A B => (s row).1)).det = 0 at hselected
    have hmatrix : generalBidegreeFormEvaluationMatrix A B
        (fun row : generalBidegreeFormIndex A B => (s row).1) =
        (generalBidegreeFormEvaluationMatrix A B
          (fun row : {p // p ∈ cell} => row.1)).submatrix s id := by
      ext row ab
      rfl
    rw [← hmatrix]
    exact hselected
  have hS : (0 : ℤ) ≤ (dyadicSourceCoordinateBound i : ℤ) := by
    exact_mod_cast Nat.zero_le (dyadicSourceCoordinateBound i)
  have hT : (0 : ℤ) ≤ (dyadicTargetCoordinateBound i : ℤ) := by
    exact_mod_cast Nat.zero_le (dyadicTargetCoordinateBound i)
  have hcoordinates : ∀ row : {p // p ∈ cell},
      generalBidegreeFormPointCoordinatesBounded
        (dyadicSourceCoordinateBound i : ℤ)
        (dyadicTargetCoordinateBound i : ℤ) row.1 := by
    intro row
    rw [← hpoints row]
    exact dyadicFactorTupleFamilyPoints_coordinates_bounded_of_mem_dyadicBox
      d e u v hbox row
  obtain ⟨r, hr, c, hcne, hcvanish, hbound⟩ :=
    exists_nonzero_real_bounded_integral_generalBidegreeForm_of_forall_fullIntegralEvaluationMinors_eq_zero_hadamard_separateBounds
      (S := (dyadicSourceCoordinateBound i : ℤ))
      (T := (dyadicTargetCoordinateBound i : ℤ))
      A B (fun row : {p // p ∈ cell} => row.1) hminor hS hT hcoordinates
  refine ⟨r, hr, c, hcne, ?_, hbound⟩
  intro p hp
  exact hcvanish ⟨p, hp⟩

end

end PellPaper
