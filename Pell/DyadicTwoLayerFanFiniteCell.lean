import Pell.DyadicTwoLayerFanDeterminant
import Pell.DyadicComparableCostPolynomialMeshFiniteCellHeight

/-!
# A bounded auxiliary form from the exact dyadic two-layer fan rate

This module applies the exact-fan selected-minor endpoint to every full row
selection from a finite cell.  The existing integral-kernel and Hadamard
argument then gives one nonzero integral bidegree-`(1,B)` form vanishing on
the whole cell, with the literal separate dyadic coordinate height.

No point count, factorization, square-sieve estimate, or asymptotic
parameter choice is asserted here.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- **Finite-cell exact two-layer fan endpoint.**  If every point of a
finite cell is represented by an actual factor tuple in one localized
dyadic box and the exact fan rate holds, then one bounded nonzero integral
bidegree-`(1,B)` form vanishes on the entire cell. -/
theorem exists_nonzero_real_bounded_integral_generalBidegreeOneForm_of_finset_uniformDyadicTwoLayerFanRate
    (B k : ℕ) (cell : Finset GeneralBidegreeFormPoint)
    {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    (d e u v : {p // p ∈ cell} → ℕ)
    (hpoints : ∀ row, dyadicFactorTupleFamilyPoints d e u v row = row.1)
    (s0 M xScale sigma m xDet L baseCost : ℝ)
    (hcond : ∀ row, DyadicFactorCondition theta Y
      (d row) (e row) (u row) (v row))
    (hbox : ∀ row, (d row, e row, u row, v row) ∈ dyadicBox i)
    (hs0 : 0 < s0) (hM : 1 ≤ M)
    (hlower : ∀ row, s0 ≤ (d row : ℝ) / (e row : ℝ))
    (hupper : ∀ row,
      (d row : ℝ) / (e row : ℝ) ≤ s0 * (1 + 1 / M))
    (htargetScale : xScale ≤ ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 *
      ((2 ^ i.2.2.2 : ℕ) : ℝ))
    (hxScale : 1536 ≤ xScale) (hsigma : 0 < sigma)
    (hlocalThreshold :
      Real.exp (Real.log (1536 : ℝ) / sigma) ≤ xScale)
    (hsourceDecay : m * L ≤ Real.log M)
    (hxDetL : xDet * L = (1 - sigma) * Real.log xScale)
    (hellM : 0 < m * L)
    (hkpos : 1 ≤ k) (hkB : k ≤ B)
    (hfanLower : (2 * (k : ℝ) - 1) * (m * L) ≤ xDet * L)
    (hfanUpper : xDet * L ≤ (2 * (k : ℝ) + 1) * (m * L))
    (hbaseCost :
      ((2 * ((2 ^ i.1 : ℕ) : ℝ)) *
        (2 * ((2 ^ i.2.1 : ℕ) : ℝ))) ^
          (1 * ((1 + 1) * (B + 1)) / 2) *
        ((2 * ((2 ^ i.2.2.1 : ℕ) : ℝ)) *
          (2 * ((2 ^ i.2.2.2 : ℕ) : ℝ))) ^
            (B * ((1 + 1) * (B + 1)) / 2) ≤ Real.exp baseCost)
    (hrate :
      (baseCost + shearedComparableCoordinateLogLoss 1 B 2 24) +
          Real.log (Nat.factorial
            (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) +
        twoLayerFanTaylorTail B *
          (Fintype.card (generalBidegreeGrid 1 B) : ℝ) <
      twoLayerWeight B k (m * L) (xDet * L)) :
    ∃ r : ℕ, r < 2 * (B + 1) ∧
      ∃ c : generalBidegreeFormIndex 1 B → ℤ, c ≠ 0 ∧
        (∀ p ∈ cell, generalBidegreeFormEval 1 B c p = 0) ∧
          ∀ j, (|c j| : ℝ) ≤
            (√(r : ℝ) *
              (((dyadicSourceCoordinateBound i : ℤ) ^ 1 *
                (dyadicTargetCoordinateBound i : ℤ) ^ B : ℤ) : ℝ)) ^ r := by
  classical
  have hminor : ∀ s : generalBidegreeFormIndex 1 B ↪ {p // p ∈ cell},
      ((generalBidegreeFormEvaluationMatrix 1 B
        (fun row : {p // p ∈ cell} => row.1)).submatrix s id).det = 0 := by
    intro s
    have hselectedPoints :
        dyadicFactorTupleFamilyPoints
            (fun row : generalBidegreeFormIndex 1 B => d (s row))
            (fun row : generalBidegreeFormIndex 1 B => e (s row))
            (fun row : generalBidegreeFormIndex 1 B => u (s row))
            (fun row : generalBidegreeFormIndex 1 B => v (s row)) =
          fun row : generalBidegreeFormIndex 1 B => (s row).1 := by
      funext row
      exact hpoints (s row)
    have hidentityRows : (Equiv.refl (generalBidegreeFormIndex 1 B)) =
        (generalBidegreeGridPointEquiv 1 B).trans
          (generalBidegreeGridPointEquiv 1 B).symm := by
      apply Equiv.ext
      intro row
      exact ((generalBidegreeGridPointEquiv 1 B).symm_apply_apply row).symm
    have hselected :
        ((generalBidegreeFormEvaluationMatrix 1 B
          (dyadicFactorTupleFamilyPoints
            (fun row : generalBidegreeFormIndex 1 B => d (s row))
            (fun row : generalBidegreeFormIndex 1 B => e (s row))
            (fun row : generalBidegreeFormIndex 1 B => u (s row))
            (fun row : generalBidegreeFormIndex 1 B => v (s row)))).submatrix
              (Equiv.refl _) id).det = 0 := by
      exact
        standardSelectedIntegralMinor_det_eq_zero_of_uniformDyadicTwoLayerFanRate
          B k (generalBidegreeGridPointEquiv 1 B) (Equiv.refl _)
          hidentityRows
          (fun row : generalBidegreeFormIndex 1 B => d (s row))
          (fun row : generalBidegreeFormIndex 1 B => e (s row))
          (fun row : generalBidegreeFormIndex 1 B => u (s row))
          (fun row : generalBidegreeFormIndex 1 B => v (s row))
          s0 M xScale sigma m xDet L baseCost
          (fun row => hcond (s row))
          (fun row => hbox (s row))
          hs0 hM
          (fun row => hlower (s row))
          (fun row => hupper (s row))
          htargetScale hxScale hsigma hlocalThreshold hsourceDecay hxDetL
          hellM hkpos hkB hfanLower hfanUpper hbaseCost hrate
    rw [hselectedPoints] at hselected
    change (generalBidegreeFormEvaluationMatrix 1 B
      (fun row : generalBidegreeFormIndex 1 B => (s row).1)).det = 0 at hselected
    have hmatrix : generalBidegreeFormEvaluationMatrix 1 B
        (fun row : generalBidegreeFormIndex 1 B => (s row).1) =
        (generalBidegreeFormEvaluationMatrix 1 B
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
      1 B (fun row : {p // p ∈ cell} => row.1)
      hminor hS hT hcoordinates
  refine ⟨r, ?_, c, hcne, ?_, hbound⟩
  · simpa using hr
  · intro p hp
    exact hcvanish ⟨p, hp⟩

end

end PellPaper
